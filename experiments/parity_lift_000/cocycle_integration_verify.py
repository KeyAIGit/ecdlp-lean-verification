#!/usr/bin/env python3
"""Bounded validator for the local-to-global cocycle statements.

The script uses only synthetic odd cycles. It does not evaluate a real ECDLP
target, a secp256k1 key, or an unknown scalar.

It checks:

* prefix integration reconstructs a potential from one base value and all
  adjacent edge differences;
* a global gauge flip preserves every edge difference;
* a cyclic coboundary has zero total sum in Z/2Z;
* canonical parity on an odd cycle has an alternating edge on every ordinary
  step and one wrap defect;
* a constant-one edge assignment cannot be a global coboundary on an odd
  cycle;
* after removing a public coboundary, the surviving secp-like local factor is
  the constant nontrivial sign bit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


def deterministic_bit(order: int, index: int) -> int:
    digest = hashlib.sha256(
        f"COCYCLE-INTEGRATION-001:{order}:{index}".encode("ascii")
    ).digest()
    return digest[0] & 1


def check_order(order: int) -> dict[str, Any]:
    if order < 5 or order % 2 == 0:
        raise ValueError("order must be odd and at least five")

    potential = [deterministic_bit(order, k) for k in range(order)]
    potential[0] = 0
    edge = [potential[(k + 1) % order] ^ potential[k] for k in range(order)]

    reconstructed = [potential[0]]
    for k in range(order - 1):
        reconstructed.append(reconstructed[-1] ^ edge[k])
    assert reconstructed == potential

    gauge_flipped = [value ^ 1 for value in potential]
    gauge_edge = [
        gauge_flipped[(k + 1) % order] ^ gauge_flipped[k]
        for k in range(order)
    ]
    assert gauge_edge == edge
    assert sum(edge) % 2 == 0

    parity = [k & 1 for k in range(order)]
    parity_edge = [parity[(k + 1) % order] ^ parity[k] for k in range(order)]
    assert parity_edge[:-1] == [1] * (order - 1)
    assert parity_edge[-1] == 0
    assert sum(parity_edge) % 2 == 0

    constant_nontrivial_edge = [1] * order
    assert sum(constant_nontrivial_edge) % 2 == 1

    c = 1
    public_value = [((c * (k & 1)) ^ potential[k]) for k in range(order)]
    for k in range(order - 1):
        assert (
            potential[k + 1] ^ potential[k]
            == c ^ public_value[k + 1] ^ public_value[k]
        )

    return {
        "order": order,
        "path_vertices_checked": order,
        "ordinary_edges_checked": order - 1,
        "prefix_reconstruction": True,
        "global_gauge_flip_preserves_edges": True,
        "cycle_closure": True,
        "parity_cut": {
            "alternating_ordinary_edges": order - 1,
            "wrap_defects": 1,
        },
        "constant_nontrivial_edge_is_not_odd_cycle_coboundary": True,
        "public_coboundary_removal": True,
    }


def build_payload() -> dict[str, Any]:
    orders = list(range(5, 128, 2))
    checks = [check_order(order) for order in orders]
    return {
        "schema_version": 1,
        "experiment_id": "COCYCLE-INTEGRATION-001-BOUNDED-VALIDATOR",
        "scope": (
            "synthetic odd cycles only; no secp256k1 target and no unknown "
            "discrete logarithm"
        ),
        "coefficient_group": "Z/2Z",
        "orders": orders,
        "order_count": len(orders),
        "path_vertices_checked": sum(row["path_vertices_checked"] for row in checks),
        "ordinary_edges_checked": sum(
            row["ordinary_edges_checked"] for row in checks
        ),
        "all_passed": all(
            row["prefix_reconstruction"]
            and row["global_gauge_flip_preserves_edges"]
            and row["cycle_closure"]
            and row["constant_nontrivial_edge_is_not_odd_cycle_coboundary"]
            and row["public_coboundary_removal"]
            for row in checks
        ),
        "claims_checked": [
            "one base value plus all local edges uniquely reconstructs the path potential",
            "local edges are invariant under one global gauge flip",
            "a cyclic coboundary has zero total Z/2Z integral",
            "odd-cycle parity has one wrap defect",
            "the constant nontrivial edge is not a global coboundary on an odd cycle",
            "removing a public coboundary leaves the constant secp-like sign factor",
        ],
        "claim_boundary": (
            "This validates finite algebraic identities only. It is neither a "
            "parity algorithm nor a sub-square-root query lower bound."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()

    payload = build_payload()
    encoded = json.dumps(payload, indent=2, sort_keys=True)
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(encoded + "\n", encoding="utf-8")
    print(encoded)


if __name__ == "__main__":
    main()
