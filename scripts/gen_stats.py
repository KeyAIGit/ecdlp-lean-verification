#!/usr/bin/env python3
"""Generate machine-readable stats for the verified ECDLP layer.

Single source of truth is the **ledger table itself** in ``VERIFIED.md``: the row
count is recounted mechanically from the main table (every ``| … | proved… |`` data
row above the "Coverage restatements" section), and the distinct-results figure is
``rows − alternate-form`` where the alternate-form figure is the curatorial number
stated in the canonical-count note (``(N rows are alternate-form``).

The canonical prose line (``**N ledger rows / ~M distinct kernel-verified
results**``) must MATCH the recount — this script (and ``scripts/check_counts.py``)
fails with the expected line if it drifts, so the prose can no longer silently lag
the table (which happened at 226→227, 235→227, and 239→228).

Writes two files (kept in the repo so they are fetchable via raw.githubusercontent):
  - ``data/stats.json``            — full stats object
  - ``badges/theorems.json``       — shields.io endpoint-badge format

Run locally (``python3 scripts/gen_stats.py``) or through the docs-sync workflow
(``.github/workflows/docs-sync.yml``). With ``--check`` it verifies the on-disk
files are in sync and exits non-zero if not (so the figures cannot silently
drift).

Raw URLs for a site to consume (main branch):
  https://raw.githubusercontent.com/KeyAIGit/-ecdlp-lean-verification/main/data/stats.json
  https://raw.githubusercontent.com/KeyAIGit/-ecdlp-lean-verification/main/badges/theorems.json
Live shields badge:
  https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/KeyAIGit/-ecdlp-lean-verification/main/badges/theorems.json
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
VERIFIED = ROOT / "VERIFIED.md"
STATS_JSON = ROOT / "data" / "stats.json"
BADGE_JSON = ROOT / "badges" / "theorems.json"

CANON_RE = re.compile(
    r"\*\*(\d+)\s+ledger rows\s*/\s*~(\d+)\s+distinct kernel-verified results\*\*"
)
ALT_RE = re.compile(r"\((\d+)\s+rows are alternate-form")
# Everything below this heading (coverage restatements, the attributed/ported table)
# is deliberately excluded from the headline figure.
HEADLINE_END = "### Coverage restatements"


def count_ledger_rows(text: str) -> tuple[int, int]:
    """Recount the main ledger table: rows whose status cell is `proved`/`proved¹`/`proved²`.

    Returns (total_rows, bare_proved_rows). Only the region above HEADLINE_END counts,
    so the tracked-separately sections cannot inflate the headline. A counted row must also
    cite a Lean declaration in backticks: every real ledger row names its theorem in
    backticks, so this rejects a stray prose/status table above the cutoff whose rows happen
    to end in a `proved…` cell (table-identity guard). `scripts/check_counts.py` mirrors this.
    """
    total = 0
    bare = 0
    for line in text.splitlines():
        if line.startswith(HEADLINE_END):
            break
        if not line.startswith("| "):
            continue
        if "`" not in line:
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) >= 2 and cells[-1].startswith("proved"):
            total += 1
            if cells[-1] == "proved":
                bare += 1
    return total, bare


def compute_stats() -> dict:
    text = VERIFIED.read_text(encoding="utf-8")

    ledger_rows, bare_proved = count_ledger_rows(text)
    if ledger_rows <= 0:
        raise SystemExit("gen_stats: no ledger rows found in VERIFIED.md main table")

    m_alt = ALT_RE.search(text)
    if not m_alt:
        raise SystemExit(
            "gen_stats: alternate-form figure not found in VERIFIED.md "
            "(expected '(N rows are alternate-form' in the canonical-count note)"
        )
    alt_form = int(m_alt.group(1))
    distinct = ledger_rows - alt_form

    m = CANON_RE.search(text)
    if not m:
        raise SystemExit(
            "gen_stats: canonical figure not found in VERIFIED.md "
            "(expected '**N ledger rows / ~M distinct kernel-verified results**')"
        )
    prose_rows, prose_distinct = int(m.group(1)), int(m.group(2))
    if (prose_rows, prose_distinct) != (ledger_rows, distinct):
        raise SystemExit(
            "gen_stats: VERIFIED.md canonical line is stale — the table recount gives "
            f"{ledger_rows} rows / ~{distinct} distinct (alternate-form {alt_form}), but the "
            f"prose says {prose_rows} / ~{prose_distinct}. Update the canonical line to:\n"
            f"  **{ledger_rows} ledger rows / ~{distinct} distinct kernel-verified results** "
            f"({alt_form} rows are alternate-form, …"
        )

    # Cross-checks derived from the tree (not authoritative, but surfaced).
    proved_dir = ROOT / "Ecdlp" / "Proved"
    proved_modules = len(list(proved_dir.rglob("*.lean"))) if proved_dir.is_dir() else 0

    return {
        "schemaVersion": 1,
        "project": "ecdlp-lean-verification",
        "curve": "secp256k1",
        "toolchain": "Lean 4 + Mathlib v4.31.0",
        "ledger_rows": ledger_rows,
        "distinct_results": distinct,
        "alt_form_rows": alt_form,
        "proved_modules": proved_modules,
        "proved_ledger_cells": bare_proved,
        "sorry_count": 0,
        "custom_axioms": 0,
        "invariant": "green build = every listed theorem fully proved (no sorry, no custom axioms)",
        "source_of_truth": "VERIFIED.md ledger table (rows recounted mechanically; "
                           "distinct = rows − curatorial alternate-form figure)",
    }


def badge(stats: dict) -> dict:
    return {
        "schemaVersion": 1,
        "label": "verified theorems",
        "message": f"{stats['distinct_results']} ({stats['ledger_rows']} rows)",
        "color": "brightgreen",
    }


def render() -> tuple[str, str]:
    stats = compute_stats()
    return (
        json.dumps(stats, indent=2, ensure_ascii=False) + "\n",
        json.dumps(badge(stats), indent=2, ensure_ascii=False) + "\n",
    )


def main(argv: list[str]) -> int:
    stats_text, badge_text = render()
    if "--check" in argv:
        ok = True
        for path, want in ((STATS_JSON, stats_text), (BADGE_JSON, badge_text)):
            have = path.read_text(encoding="utf-8") if path.exists() else None
            if have != want:
                print(f"gen_stats: {path.relative_to(ROOT)} is out of sync "
                      f"(run `python3 scripts/gen_stats.py`)")
                ok = False
        if ok:
            print("gen_stats: stats files in sync with VERIFIED.md")
            return 0
        return 1

    STATS_JSON.parent.mkdir(parents=True, exist_ok=True)
    BADGE_JSON.parent.mkdir(parents=True, exist_ok=True)
    STATS_JSON.write_text(stats_text, encoding="utf-8")
    BADGE_JSON.write_text(badge_text, encoding="utf-8")
    print(f"gen_stats: wrote {STATS_JSON.relative_to(ROOT)} and "
          f"{BADGE_JSON.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
