#!/usr/bin/env python3
"""Semantic-drift gate (CI).

After the 2026-07 semantic-correction pass, this gate fails the build if any specific
UNCONDITIONAL overclaim phrasing reappears in the docs / Lean docstrings / publication
surfaces. Each entry overstates what the Lean kernel actually proves:

- "full Shoup theorem" — we prove only the *fixed-transcript affine collision core*.
- "proved Θ(√n)" — we prove the √n *arithmetic relations*, not a running-time complexity.
- "GLV never / universal no-go" — we prove *this reduction* preserves the exponent, scoped.
- "Semaev prime-field no advantage" — no *known* method; the asymptotics are *open* (Petit).
- unconditional Frobenius-trace claims — `t = p+1−n` is the trace only *given* `#E = n`.

This is deliberately a small curated substring list (like `check_counts.py`), not an NLP
classifier. A line that must legitimately quote a banned phrase (this file, a negation, or a
historical/quoted review) can be exempted with an inline `drift-check: ignore` marker.

Usage:  python3 scripts/check_semantic_drift.py
"""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Files to scan: human-facing docs, Lean docstrings, publication + prompt surfaces.
SCAN: list[str] = [
    "README.md", "VERIFIED.md", "BARRIERS.md", "TRUST_REPORT.md", "ABSTRACT_SCOPE.md",
    "PUBLISHABLE_UNITS.md", "ROADMAP.md",
    "data/knowledge_graph.md", "COVERAGE.md",
]
SCAN_GLOBS: list[str] = ["Ecdlp/Proved/**/*.lean", "prompts/*.md", "notes/*.md"]

# Curated banned substrings (case-sensitive), each a phrasing removed in the correction pass.
FORBIDDEN: list[tuple[str, str]] = [
    ("not subexponential** and gives no", "Semaev prime-field: open, not a proven no-go"),
    ("pins the generic discrete-log complexity at", "Θ(√n) stated as a proved complexity theorem"),
    ("gives no *asymptotic* advantage against ECDLP", "GLV: universal no-go overclaim"),
    ("establishing the `Θ(√n)` generic", "Θ(√n) generic complexity overclaim"),
    ("Matching upper bounds closing Θ(√n)", "Θ(√n) 'closed' overclaim"),
    ("generic-group Θ(√n) combinatorial core", "Θ(√n) unit-title overclaim"),
    ("combinatorial core of the Shoup / Nechaev lower bound", "call it the fixed-transcript core"),
    ("**no** complex multiplication by `ℤ[ζ₃]` and **no** GLV", "c4≠0 excludes j=0 CM only"),
    ("— never a reduction", "GLV scoped no-go, not universal"),
]


def iter_files() -> list[Path]:
    files = [ROOT / s for s in SCAN]
    for g in SCAN_GLOBS:
        files.extend(sorted(ROOT.glob(g)))
    seen: set[Path] = set()
    out: list[Path] = []
    for f in files:
        if f.exists() and f not in seen:
            seen.add(f)
            out.append(f)
    return out


def main() -> int:
    failures: list[str] = []
    for path in iter_files():
        rel = path.relative_to(ROOT)
        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if "drift-check: ignore" in line:
                continue
            for bad, reason in FORBIDDEN:
                if bad in line:
                    failures.append(f"{rel}:{i}: banned overclaim '{bad}' ({reason})")

    if failures:
        print("SEMANTIC DRIFT FAILED — these unconditional overclaims must be re-hedged "
              "(see scripts/check_semantic_drift.py; exempt a legitimate quote with "
              "'drift-check: ignore'):")
        print("\n".join("  " + f for f in failures))
        return 1

    print(f"semantic-drift check OK: none of {len(FORBIDDEN)} banned overclaims present.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
