#!/usr/bin/env python3
"""Strict Lean axiom-log gate. Logs are evidence, not independent proof certificates.

The Lean invocation must itself succeed. This checker validates its output against
an optional trusted registry. It cannot establish the authenticity of a text log
or of a compiler-generated declaration from its name alone.

Usage: python3 scripts/check_axioms.py LOG [REGISTRY]
"""
from __future__ import annotations

from collections import Counter
import json
from pathlib import Path
import re
import sys
from typing import Any

ALLOWED_STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NATIVE_DECIDE_EXACT = {"Lean.ofReduceBool", "Lean.trustCompiler"}
FORBIDDEN_ALWAYS = {"sorryAx", "Lean.guardMsgsAx"}
VALID_BASES = {"standard", "standard+native_decide"}
MAX_INPUT_BYTES = 32 * 1024 * 1024
# Deliberately narrow: an unfamiliar toolchain format needs review, not a wildcard.
NATIVE_AUX = re.compile(r"(?P<owner>[^\s\[\],]+)\._native\.native_decide\.ax_[0-9]+(?:_[0-9]+)*\Z")
RECORD = re.compile(
    r"^'(?P<name>[^\r\n]+)' (?:depends on axioms: \[(?P<axioms>[^\[\]]*)\]"
    r"|(?P<free>does not depend on any axioms))[ \t]*$", re.MULTILINE
)


class AuditError(ValueError):
    """An input cannot safely be interpreted as a complete axiom audit."""


def is_native_decide(ax: str) -> bool:
    return ax in NATIVE_DECIDE_EXACT or NATIVE_AUX.fullmatch(ax) is not None


def _records(text: str) -> list[tuple[str, str | None]]:
    text = text.replace("\r\n", "\n")
    if "\x00" in text or "\x1b" in text:
        raise AuditError("control characters in audit output")
    if re.search(r"\berror:", text) or "unknown identifier" in text:
        raise AuditError("Lean reported an elaboration error")
    matches = list(RECORD.finditer(text))
    if not matches:
        raise AuditError("no complete #print axioms records")
    remainder = RECORD.sub("", text)
    # Do not silently discard a malformed record while accepting the other ones.
    if re.search(r"depends on axioms|does not depend on any axioms", remainder):
        raise AuditError("malformed or incomplete axiom record")
    rows: list[tuple[str, str | None]] = []
    for match in matches:
        name, atoms = match.group("name"), match.group("axioms")
        if not name or name != name.strip() or any(c.isspace() for c in name):
            raise AuditError("invalid declaration name")
        if atoms is not None and atoms.strip():
            tokens = [a.strip() for a in atoms.split(",")]
            if any(not a or any(c.isspace() for c in a) for a in tokens):
                raise AuditError(f"invalid axiom list for {name}")
            if len(tokens) != len(set(tokens)):
                raise AuditError(f"duplicate axiom in record for {name}")
        rows.append((name, atoms))
    duplicates = sorted(k for k, n in Counter(name for name, _ in rows).items() if n > 1)
    if duplicates:
        raise AuditError(f"duplicate declaration records: {duplicates}")
    return rows


def parse_audit_output(text: str) -> tuple[list[tuple[str, str]], list[str]]:
    """Compatible return shape; malformed and duplicate records now raise AuditError."""
    rows = _records(text)
    return ([(name, atoms) for name, atoms in rows if atoms is not None],
            [name for name, atoms in rows if atoms is None])


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise AuditError(f"duplicate JSON object key: {key}")
        result[key] = value
    return result


def read_text_bounded(path: Path) -> str:
    with path.open("rb") as stream:
        data = stream.read(MAX_INPUT_BYTES + 1)
    if len(data) > MAX_INPUT_BYTES:
        raise AuditError(f"input exceeds {MAX_INPUT_BYTES} bytes")
    return data.decode("utf-8")


def load_registry(path: Path) -> dict[str, Any]:
    raw = json.loads(read_text_bounded(path), object_pairs_hook=_unique_object)
    if not isinstance(raw, dict):
        raise AuditError("registry must be a JSON object")
    return raw


def validate_registry(registry: dict[str, Any]) -> tuple[set[str], set[str], dict[str, str] | None]:
    expected = registry.get("ledger_declarations")
    if (not isinstance(expected, list) or not expected or
            any(not isinstance(x, str) or not x or x != x.strip() for x in expected)):
        raise AuditError("registry needs a nonempty ledger_declarations list of names")
    if len(expected) != len(set(expected)):
        raise AuditError("registry contains duplicate ledger declarations")
    declarations = registry.get("declarations")
    if not isinstance(declarations, dict) or not set(expected).issubset(declarations):
        raise AuditError("declarations map must cover every ledger declaration")
    known = set(declarations)
    # Absence supports the existing legacy ECDLP registry; an explicitly present
    # map must be complete. An empty map must not silently disable per-row checks.
    bases = registry.get("axiom_base")
    if "axiom_base" in registry:
        if not isinstance(bases, dict) or set(bases) != set(expected):
            raise AuditError("axiom_base must cover exactly the audited declarations")
        if any(not isinstance(v, str) or v not in VALID_BASES for v in bases.values()):
            raise AuditError("unknown axiom_base value")
    return set(expected), known, bases


def audit(text: str, registry: dict[str, Any] | None = None) -> dict[str, Any]:
    rows = _records(text)
    known: set[str] = set()
    bases: dict[str, str] | None = None
    if registry is not None:
        expected, known, bases = validate_registry(registry)
        observed = {name for name, _ in rows}
        if observed != expected:
            raise AuditError(f"registry mismatch: missing={sorted(expected-observed)}, "
                             f"unexpected={sorted(observed-expected)}")
    compiler_users: list[str] = []
    violations: list[str] = []
    for name, atoms in rows:
        axioms = {a.strip() for a in (atoms or "").split(",") if a.strip()}
        compiler = False
        for ax in sorted(axioms):
            if ax in FORBIDDEN_ALWAYS:
                violations.append(f"{name}: forbidden axiom {ax}")
            elif ax in ALLOWED_STANDARD:
                continue
            elif ax in NATIVE_DECIDE_EXACT:
                compiler = True
            else:
                aux = NATIVE_AUX.fullmatch(ax)
                if aux is None:
                    violations.append(f"{name}: unrecognized axiom {ax}")
                else:
                    compiler = True
                    if aux.group("owner") not in known:
                        violations.append(f"{name}: native auxiliary owner is not in the registry")
        if compiler:
            compiler_users.append(name)
            if bases is not None and bases[name] != "standard+native_decide":
                violations.append(f"{name}: compiler trust exceeds declared standard base")
    if violations:
        raise AuditError("; ".join(violations))
    return {"audited_declarations": len(rows), "compiler_trusted": sorted(compiler_users),
            "exact_registry_match": registry is not None, "per_row_base_checked": bases is not None}


def main(argv: list[str]) -> int:
    if len(argv) not in {2, 3}:
        print("usage: check_axioms.py LOG [REGISTRY]", file=sys.stderr)
        return 2
    try:
        registry = load_registry(Path(argv[2])) if len(argv) == 3 else None
        report = audit(read_text_bounded(Path(argv[1])), registry)
    except (AuditError, OSError, UnicodeError, json.JSONDecodeError) as exc:
        print(f"AXIOM AUDIT FAILED: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(report, ensure_ascii=False, sort_keys=True))
    print("AXIOM AUDIT OK: observed dependencies fit the allowed base.")
    if registry is None:
        print("UNSCOPED LOG CHECK: completeness against a ledger was not established.")
    elif not report["per_row_base_checked"]:
        print("LEGACY REGISTRY: no per-row trust classification was supplied.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
