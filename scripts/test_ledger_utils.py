#!/usr/bin/env python3
"""Regression tests for VERIFIED.md grouped-reference parsing."""
from __future__ import annotations

import json
from pathlib import Path

from ledger_utils import ROW_RE, extract_files, parse_ledger, strip_md, strip_status

ROOT = Path(__file__).resolve().parent.parent
GROUPED_FILES = [
    "Ecdlp/Proved/ShamirSSS.lean",
    "Ecdlp/Proved/GlvTorsionAction.lean",
    "Ecdlp/Proved/ScalarGroupStructure.lean",
]
GENERATED = ["data/knowledge_graph.md", "data/result_registry.json"]


def test_braced_file_group() -> None:
    cell = "Ecdlp/Proved/{ShamirSSS,GlvTorsionAction,ScalarGroupStructure}.lean"
    assert extract_files(ROOT, cell) == GROUPED_FILES


def test_wildcard_row_keeps_file_scope() -> None:
    rows = parse_ledger(ROOT)
    matches = [row for row in rows if row["theorem_cell"] == "`Ecdlp.*`"]
    assert len(matches) == 1
    assert matches[0]["files"] == GROUPED_FILES


def test_strip_md_preserves_math_superscripts() -> None:
    """`¹`/`²` are *status-cell* footnote markers, never to be stripped from prose.

    Regression: `strip_md` used to drop them from every cell, which silently rewrote
    `S₄(x₁,x₂,x₃,β²x₄)` as `S₄(…,βx₄)` (a different, false identity), `16 = 4²` as
    `16 = 4`, and `E[n] ≅ (ℤ/n)²` as `E[n] ≅ (ℤ/n)` throughout the generated ledger
    artifacts. Only `strip_status` may remove them.
    """
    assert strip_md("**GLV**: `16 = 4²` and `E[n] ≅ (ℤ/n)²`.") == \
        "GLV: `16 = 4²` and `E[n] ≅ (ℤ/n)²`."
    assert strip_md("`S₄(x₁,x₂,x₃,β²x₄)`") == "S₄(x₁,x₂,x₃,β²x₄)"
    assert strip_md("β³ = 1") == "β³ = 1"
    # the footnote markers are still normalised away, but only for the status column
    assert strip_status("proved¹") == "proved"
    assert strip_status("**proved²**") == "proved"
    assert strip_status("proved") == "proved"


def test_ledger_cells_survive_verbatim_into_generated_artifacts() -> None:
    """End-to-end fidelity: a lossy cell transform must fail here, not ship silently.

    The docs-sync gate only checks that regeneration reproduces the committed files, so a
    generator that drops characters is a stable fixpoint and therefore invisible to it.
    This asserts the stronger property the fixpoint gate cannot see: every parsed claim and
    method string occurs verbatim in each generated artifact.
    """
    rows = parse_ledger(ROOT)
    assert len(rows) > 200, f"ledger looks truncated: only {len(rows)} rows parsed"
    for name in GENERATED:
        text = (ROOT / name).read_text(encoding="utf-8")
        for row in rows:
            for field in ("claim", "method"):
                value = row[field]
                if not value:
                    continue
                if value in text:
                    continue
                # JSON artifacts escape backslashes and quotes; compare the encoded form too
                if json.dumps(value, ensure_ascii=False)[1:-1] in text:
                    continue
                raise AssertionError(
                    f"{name}: {row['id']} {field} was altered on the way out of the "
                    f"ledger (a lossy transform in the cell pipeline): {value[:120]!r}"
                )


def test_row_regex_drops_only_the_excluded_secondary_table() -> None:
    """Rows are skipped only where VERIFIED.md documents an intentional exclusion.

    `ROW_RE` demands five non-empty cells, so a malformed or empty cell would delete a whole
    row from every generated artifact without any gate noticing. The only pipe-leading lines
    it may reject are the four-column "Ported / upstream-derived" table (header, separator and
    its two rows: `normEDS` and the verified-garbage certificate lemma), which VERIFIED.md
    excludes from the headline count on purpose.
    """
    lines = (ROOT / "VERIFIED.md").read_text(encoding="utf-8").splitlines()
    dropped = [ln for ln in lines if ln.lstrip().startswith("|") and not ROW_RE.match(ln)]
    assert len(dropped) == 4, (
        "unexpected number of unparsed table lines in VERIFIED.md "
        f"({len(dropped)}, expected the 4 lines of the excluded four-column table): {dropped}"
    )
    for marker in ("normEDS_isEllSequence", "noRoot_of_cert"):
        assert any(marker in ln for ln in dropped), (
            "the unparsed lines are no longer the excluded upstream-derived table; a real "
            f"ledger row may be getting dropped (missing {marker}): {dropped}"
        )


def main() -> int:
    tests = [
        test_braced_file_group,
        test_wildcard_row_keeps_file_scope,
        test_strip_md_preserves_math_superscripts,
        test_ledger_cells_survive_verbatim_into_generated_artifacts,
        test_row_regex_drops_only_the_excluded_secondary_table,
    ]
    for test in tests:
        test()
        print(f"ok  {test.__name__}")
    print(f"\nall {len(tests)} ledger-parser fixtures passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
