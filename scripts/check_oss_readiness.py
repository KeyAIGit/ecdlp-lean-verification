#!/usr/bin/env python3
"""Check a bounded, pending rights-review inventory; never grant a license.

Default exit 0 means notice metadata is internally consistent, NOT OSS clearance.
--require-release-ready intentionally fails while the owner decision is absent.
No network, model calls, signatures, file writes, or new experiments.
"""
from __future__ import annotations

import argparse
from datetime import date
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = "repo/OSS_READINESS.json"
BLOCKERS = {"RIGHTS-HOLDER", "LICENSE-DECISION", "CORPUS-RIGHTS", "ASSET-RIGHTS", "RELEASE-VERIFICATION"}
REQUIRED_SOURCE = {
    "Ecdlp/Proved/NormEDSIsElliptic.lean": "Apache-2.0",
    "archive/scratch/pr13155_eds.lean": "Apache-2.0",
    "fonts/Nunito-Variable.woff2": "OFL-1.1",
    "fonts/Baloo2-Variable.woff2": "OFL-1.1",
}
DOCUMENTS = ("LICENSING.md", "THIRD_PARTY_NOTICES.md", "CONTRIBUTING.md", "SECURITY.md")


def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def safe_file(root: Path, value: Any) -> Path:
    if not isinstance(value, str) or not value or value != value.strip():
        raise ValueError("path must be a nonempty normalized string")
    rel = PurePosixPath(value)
    if rel.is_absolute() or rel.as_posix() != value or ".." in rel.parts or "\\" in value or ":" in value:
        raise ValueError(f"unsafe repository path: {value!r}")
    path = root
    for part in rel.parts:
        path = path / part
        if path.is_symlink():
            raise ValueError(f"symlink is not a reviewed input: {value}")
    if not path.is_file():
        raise ValueError(f"missing reviewed file: {value}")
    return path


def require(value: bool, message: str) -> None:
    if not value:
        raise ValueError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def records(value: Any, label: str) -> list[dict[str, Any]]:
    require(isinstance(value, list) and bool(value), f"{label} must be a nonempty list")
    require(all(isinstance(row, dict) for row in value), f"{label} contains a non-object")
    return value


def inspect(root: Path) -> dict[str, Any]:
    raw = safe_file(root, MANIFEST).read_text(encoding="utf-8")
    m = json.loads(raw, object_pairs_hook=unique_object)
    require(isinstance(m, dict), "manifest must be an object")
    require(type(m.get("schema_version")) is int and m["schema_version"] == 1, "unsupported schema version")
    require(m.get("status") == "pending_rights_confirmation", "rights-state transition requires separate owner review and checker update")
    require(m.get("repository_license_granted") is False, "metadata cannot assert a repository-wide license grant")
    require("owner_approval" in m and m["owner_approval"] is None, "do not fabricate an owner approval")
    require(m.get("proposed_default_license") == "Apache-2.0", "proposed default changed without rights review")
    require(isinstance(m.get("scope"), str) and bool(m["scope"].strip()), "scope is required")
    date.fromisoformat(m.get("review_date", ""))
    require(bool(re.fullmatch(r"[0-9a-f]{40}", m.get("audited_source_commit", ""))), "invalid audited source commit")
    # An accidental root license would contradict the pending state. A later
    # genuine adoption must update the policy and evidence together, not a flag.
    for p in root.iterdir():
        require(not (p.is_file() and p.name.lower().split(".")[0] in {"license", "licence", "copying"}),
                "root license contradicts the pending review; complete adoption through review")
    for name in DOCUMENTS:
        safe_file(root, name)
    rows = records(m.get("blockers"), "blockers")
    ids = [row.get("id") for row in rows]
    require(all(isinstance(x, str) for x in ids), "invalid blocker ID")
    require(len(ids) == len(set(ids)) and set(ids) == BLOCKERS, "required unresolved blocker set was altered")
    require(all(isinstance(row.get("required"), str) and row["required"].strip() for row in rows), "blocker needs a resolution requirement")

    notices: dict[str, str] = {}
    for row in records(m.get("license_texts"), "license_texts"):
        path = safe_file(root, row.get("path"))
        name = row["path"]
        require(name not in notices, f"duplicate license text: {name}")
        require(digest(path) == row.get("sha256"), f"license-text digest mismatch: {name}")
        notices[name] = path.read_text(encoding="utf-8")

    seen: dict[str, str] = {}
    used_notices: set[str] = set()
    for row in records(m.get("third_party_files"), "third_party_files"):
        path = safe_file(root, row.get("path"))
        name, license_id = row["path"], row.get("license")
        require(name not in seen, f"duplicate third-party input: {name}")
        require(REQUIRED_SOURCE.get(name) == license_id, f"unreviewed file or license identity: {name}")
        require(digest(path) == row.get("source_sha256"), f"third-party source digest mismatch: {name}; review changes and attribution")
        notice_name = row.get("notice_path")
        require(isinstance(notice_name, str) and notice_name in notices, f"unregistered license text: {name}")
        notice = notices[notice_name]
        attribution = row.get("copyright")
        require(isinstance(attribution, str) and bool(attribution), f"missing attribution: {name}")
        require(isinstance(row.get("upstream"), str) and row["upstream"].startswith("https://"), f"missing upstream locator: {name}")
        require(isinstance(row.get("evidence"), str) and bool(row["evidence"].strip()), f"missing evidence limitation: {name}")
        if license_id == "Apache-2.0":
            require(attribution in path.read_text(encoding="utf-8"), f"source attribution missing: {name}")
            require("Apache License" in notice and "Version 2.0, January 2004" in notice and "END OF TERMS AND CONDITIONS" in notice,
                    f"incomplete Apache reference: {notice_name}")
        else:
            require(attribution in notice and "SIL OPEN FONT LICENSE Version 1.1" in notice and "OTHER DEALINGS IN THE FONT SOFTWARE." in notice,
                    f"incomplete OFL notice: {notice_name}")
            require(bool(re.fullmatch(r"[0-9a-f]{40}", row.get("upstream_notice_blob", ""))), f"invalid upstream notice blob: {name}")
        used_notices.add(notice_name)
        seen[name] = license_id
    require(seen == REQUIRED_SOURCE, "known third-party source set is incomplete")
    require(used_notices == set(notices), "orphaned/unmapped license text")

    # Deliberately narrow detection: new bundled fonts and attributed Lean files.
    # This is not copyright inference or an exhaustive third-party code scanner.
    for directory in ("Ecdlp", "ResearchOS", "archive"):
        for p in (root / directory).rglob("*.lean"):
            rel = p.relative_to(root).as_posix()
            safe_file(root, rel)
            if re.search(r"(?im)^\s*Copyright\b", p.read_text(encoding="utf-8")):
                require(rel in seen, f"unregistered attributed Lean file: {rel}")
    for p in (root / "fonts").rglob("*"):
        if p.suffix.lower() in {".woff", ".woff2", ".ttf", ".otf"}:
            rel = p.relative_to(root).as_posix()
            safe_file(root, rel)
            require(rel in seen, f"unregistered bundled font: {rel}")
    return {"metadata_consistent": True, "release_ready": False, "status": m["status"],
            "reviewed_third_party_files": len(seen), "unresolved_blockers": sorted(BLOCKERS)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root (also useful for fixtures)")
    parser.add_argument("--require-release-ready", action="store_true")
    args = parser.parse_args(argv)
    try:
        result = inspect(args.root.resolve())
    except (OSError, UnicodeError, ValueError, TypeError, KeyError) as exc:
        print(f"OSS NOTICE CHECK FAILED: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(result, sort_keys=True))
    if args.require_release_ready:
        print("RELEASE BLOCKED: rights-holder/license decision and other listed gates remain unresolved.", file=sys.stderr)
        return 1
    print("OSS NOTICE METADATA OK; legal clearance and repository-wide licensing remain PENDING.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
