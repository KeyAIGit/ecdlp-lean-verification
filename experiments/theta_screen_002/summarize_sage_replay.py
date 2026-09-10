#!/usr/bin/env python3
"""Normalize and verify the bounded SageMath replay outputs."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path("experiments/theta_screen_002/sage_replay")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    original_path = ROOT / "verify_secp_result.json"
    independent_path = ROOT / "independent_verify_result.json"
    original = json.loads(original_path.read_text(encoding="utf-8"))
    independent = json.loads(independent_path.read_text(encoding="utf-8"))

    assert original["p"] == independent["p"]
    assert original["beta_hex"].lower() == independent["beta_hex"].lower()
    assert original["extension_polynomial"] == independent["extension_polynomial"]
    assert all(
        all(value for key, value in row.items() if key != "x")
        for row in original["samples"]
    )
    assert all(
        all(value for key, value in row.items() if key != "x")
        for row in independent["samples"]
    )

    case_paths = sorted((ROOT / "cases").glob("*.json"))
    if len(case_paths) != 12:
        raise AssertionError(f"expected 12 bounded cases, found {len(case_paths)}")

    rows = []
    for path in case_paths:
        payload = json.loads(path.read_text(encoding="utf-8"))
        config = payload["configuration"]
        solve = payload["solve"]
        rows.append(
            {
                "file": path.name,
                "sha256": sha256(path),
                "h": config["h"],
                "factor_base_x_size": config["factor_base_x_size"],
                "system": config["system"],
                "order": config["order"],
                "layout": config["variable_layout"],
                "variables": payload["ring_variables"],
                "input_equations": payload["input"]["equations"],
                "input_terms": payload["input"]["input_terms"],
                "input_max_total_degree": payload["input"]["input_max_total_degree"],
                "status": solve["status"],
                "seconds": solve.get("seconds", solve.get("seconds_before_interrupt")),
                "basis_polynomials": solve.get("basis_polynomials"),
                "basis_terms": solve.get("basis_terms"),
                "basis_max_total_degree": solve.get("basis_max_total_degree"),
                "peak_rss_mib": solve["peak_rss_mib"],
            }
        )

    completed = sum(row["status"] == "ok" for row in rows)
    timed_out = sum(row["status"] == "timeout" for row in rows)
    other = len(rows) - completed - timed_out

    summary = {
        "schema_version": "1.0",
        "scope": "bounded independent SageMath replay; no ECDLP target",
        "structural_replay": {
            "original_sha256": sha256(original_path),
            "independent_sha256": sha256(independent_path),
            "p_matches": True,
            "beta_matches": True,
            "extension_polynomial_matches": True,
            "all_sample_checks_pass": True,
        },
        "bounded_matrix": {
            "expected": 12,
            "observed": len(rows),
            "completed": completed,
            "timed_out": timed_out,
            "other": other,
            "rows": rows,
        },
        "interpretation": {
            "structural": (
                "The independent Sage replay confirms that the split cubic "
                "Kummer action is the same order-three action as secp256k1 GLV."
            ),
            "solver": (
                "The bounded matrix is representation evidence only. Timeouts "
                "and slower cases are retained as scoped negative evidence."
            ),
            "forbidden": [
                "secp256k1 discrete-log recovery",
                "sub-Pollard claim",
                "asymptotic claim",
                "route promotion",
            ],
        },
    }
    (ROOT / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )

    lines = [
        "# Independent Sage replay for theta screen 002",
        "",
        "Scope: structural and bounded toy verification only.",
        "",
        "## Structural result",
        "",
        "The original Python/Sage producer and an independently written native-Sage producer agree on:",
        "",
        "- the secp256k1 field prime;",
        "- the repository GLV cube root beta;",
        "- irreducibility of `T^3+7`;",
        "- `alpha^p=beta*alpha`;",
        "- the induced Kummer/Frobenius/GLV identities;",
        "- the fact that the shifted cubic invariant is a scalar re-expression of `x^3`.",
        "",
        "## Bounded Singular matrix",
        "",
        f"- Expected cases: 12",
        f"- Observed cases: {len(rows)}",
        f"- Completed: {completed}",
        f"- Timed out: {timed_out}",
        f"- Other terminal states: {other}",
        "",
        "| Case | h | System | Order | Layout | Vars | Input terms | Status | Seconds | Peak MiB |",
        "|---|---:|---|---|---|---:|---:|---|---:|---:|",
    ]
    for row in rows:
        seconds = "" if row["seconds"] is None else f"{row['seconds']:.3f}"
        lines.append(
            f"| `{row['file']}` | {row['h']} | {row['system']} | "
            f"{row['order']} | {row['layout'] or ''} | {row['variables']} | "
            f"{row['input_terms']} | {row['status']} | {seconds} | "
            f"{row['peak_rss_mib']:.1f} |"
        )
    lines.extend(
        [
            "",
            "## Claim boundary",
            "",
            "A completed or favorable toy case is not an asymptotic result. A timeout or loss is retained only as a negative result for the declared representation, ordering, layout, field and budget.",
        ]
    )
    (ROOT / "SUMMARY.md").write_text("\n".join(lines) + "\n", encoding="utf-8")

    retained = sorted(
        path
        for path in ROOT.rglob("*")
        if path.is_file() and path.name != "SHA256SUMS"
    )
    checksum_lines = [
        f"{sha256(path)}  {path.relative_to(ROOT).as_posix()}" for path in retained
    ]
    (ROOT / "SHA256SUMS").write_text(
        "\n".join(checksum_lines) + "\n", encoding="utf-8"
    )

    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
