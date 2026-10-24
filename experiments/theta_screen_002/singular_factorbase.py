#!/usr/bin/env python3
"""
SageMath/Singular benchmark for the surviving full-point Jacobi/theta screen.

Example:
    sage -python experiments/theta_screen_002/singular_factorbase.py \
        --h 2 --system projective --order degrevlex \
        --layout intermediate_first --timeout 180 \
        --out experiments/theta_screen_002/results/h2_projective.json

The benchmark is synthetic and uses F_43 only. It does not target secp256k1.
"""
from __future__ import annotations

import argparse
import itertools
import json
import resource
import time
from dataclasses import asdict, dataclass
from pathlib import Path

from cysignals.alarm import AlarmInterrupt, alarm, cancel_alarm
from sage.all import GF, PolynomialRing, prod, version


PointJ = tuple[int, int, int]


def square_roots_table(p: int) -> dict[int, list[int]]:
    table: dict[int, list[int]] = {}
    for x in range(p):
        table.setdefault((x * x) % p, []).append(x)
    return table


def jacobi_points(p: int, a: int) -> list[PointJ]:
    roots = square_roots_table(p)
    points: list[PointJ] = []
    for s in range(p):
        for c in roots.get((1 - s * s) % p, []):
            for d in roots.get((1 - a * s * s) % p, []):
                points.append((s, c, d))
    return points


def jacobi_add(P: PointJ, Q: PointJ, p: int, a: int) -> PointJ | None:
    s1, c1, d1 = P
    s2, c2, d2 = Q
    denominator = (c2 * c2 + (d1 * s2) ** 2) % p
    if denominator == 0:
        return None
    inv = pow(denominator, -1, p)
    return (
        (c2 * s1 * d2 + d1 * s2 * c1) * inv % p,
        (c2 * c1 - d1 * s2 * s1 * d2) * inv % p,
        (d1 * d2 - a * s1 * c1 * s2 * c2) * inv % p,
    )


def jacobi_to_weierstrass(P: PointJ, p: int, a: int) -> tuple[int, int] | None:
    s, c, d = P
    q = (a * c - d + 1 - a) % p
    if q == 0:
        return None
    inv = pow(q, -1, p)
    return (
        (d - 1) * (1 - a) * inv % p,
        s * (1 - a) * a * inv % p,
    )


@dataclass(frozen=True)
class MultiCase:
    p: int
    a: int
    r_values: tuple[int, ...]
    x_values: tuple[int, ...]
    P1: PointJ
    P2: PointJ
    P3: PointJ
    target: PointJ


def select_case(p: int, a: int, h: int) -> MultiCase:
    by_r: dict[int, list[PointJ]] = {}
    for point in jacobi_points(p, a):
        if jacobi_to_weierstrass(point, p, a) is None:
            continue
        by_r.setdefault(point[0] * point[0] % p, []).append(point)

    valid: list[tuple[int, list[PointJ], list[int]]] = []
    for r, points in sorted(by_r.items()):
        xs = sorted(
            {
                jacobi_to_weierstrass(point, p, a)[0]
                for point in points
                if jacobi_to_weierstrass(point, p, a) is not None
            }
        )
        if len(xs) == 4:
            valid.append((r, points, xs))

    if len(valid) < h:
        raise ValueError(f"only {len(valid)} suitable r-classes, requested {h}")

    selected = valid[:h]
    r_values = tuple(row[0] for row in selected)
    all_points = [point for _, points, _ in selected for point in points]
    x_values = tuple(sorted({x for _, _, xs in selected for x in xs}))

    for P1, P2, P3 in itertools.permutations(all_points, 3):
        mapped_x = {
            jacobi_to_weierstrass(P1, p, a)[0],
            jacobi_to_weierstrass(P2, p, a)[0],
            jacobi_to_weierstrass(P3, p, a)[0],
        }
        if len(mapped_x) < 3:
            continue
        if h >= 3 and len({P1[0] ** 2 % p, P2[0] ** 2 % p, P3[0] ** 2 % p}) < 3:
            continue
        P12 = jacobi_add(P1, P2, p, a)
        if P12 is None:
            continue
        target = jacobi_add(P12, P3, p, a)
        if target is None or jacobi_to_weierstrass(target, p, a) is None:
            continue
        return MultiCase(p, a, r_values, x_values, P1, P2, P3, target)

    raise RuntimeError("no nondegenerate deterministic case found")


def semaev3(u, v, w, A, B):
    e1 = u + v + w
    e2 = u * v + u * w + v * w
    e3 = u * v * w
    return (B - e2) ** 2 - 4 * (A + e1) * e3


def direct_system(case: MultiCase, order: str):
    p, a = case.p, case.a
    field = GF(p)
    A = field(2 - a)
    B = field(1 - a)
    target_x = jacobi_to_weierstrass(case.target, p, a)[0]

    source = PolynomialRing(
        field, names=("x1", "x2", "x3", "x4", "X"), order="degrevlex"
    )
    x1, x2, x3, x4, X = source.gens()
    s4 = semaev3(x1, x2, X, A, B).resultant(
        semaev3(x3, x4, X, A, B), X
    )

    ring = PolynomialRing(field, names=("x1", "x2", "x3"), order=order)
    y1, y2, y3 = ring.gens()

    s4q = ring.zero()
    for exponents, coefficient in s4.dict().items():
        e1, e2, e3, e4, eX = exponents
        if eX != 0:
            raise AssertionError("resultant still contains the eliminated variable")
        s4q += (
            ring(coefficient)
            * y1**e1
            * y2**e2
            * y3**e3
            * ring(target_x) ** e4
        )

    factor_polynomials = [
        prod(variable - ring(value) for value in case.x_values)
        for variable in (y1, y2, y3)
    ]
    return ring, [s4q, *factor_polynomials]


def projective_system(case: MultiCase, order: str, layout: str):
    p, a = case.p, case.a
    field = GF(p)

    layouts = {
        "coordinate": (
            "s1", "s2", "s3",
            "c1", "c2", "c3",
            "d1", "d2", "d3",
            "S12", "C12", "D12", "Z12",
        ),
        "point": (
            "s1", "c1", "d1",
            "s2", "c2", "d2",
            "s3", "c3", "d3",
            "S12", "C12", "D12", "Z12",
        ),
        "intermediate_first": (
            "S12", "C12", "D12", "Z12",
            "s1", "c1", "d1",
            "s2", "c2", "d2",
            "s3", "c3", "d3",
        ),
    }
    ring = PolynomialRing(field, names=layouts[layout], order=order)
    values = dict(zip(layouts[layout], ring.gens()))

    s1, s2, s3 = values["s1"], values["s2"], values["s3"]
    c1, c2, c3 = values["c1"], values["c2"], values["c3"]
    d1, d2, d3 = values["d1"], values["d2"], values["d3"]
    S12, C12, D12, Z12 = (
        values["S12"], values["C12"], values["D12"], values["Z12"]
    )

    equations = []
    for s, c, d in ((s1, c1, d1), (s2, c2, d2), (s3, c3, d3)):
        equations.extend(
            [
                s**2 + c**2 - 1,
                ring(a) * s**2 + d**2 - 1,
                prod(s**2 - ring(r) for r in case.r_values),
            ]
        )

    # EFD mmadd-2001-ls, affine plus affine.
    s1d2 = s1 * d2
    d1s2 = d1 * s2
    U = c2 * c1
    V = d1s2 * s1d2
    equations.extend(
        [
            S12 - ((c2 + d1s2) * (c1 + s1d2) - U - V),
            C12 - (U - V),
            D12 - (d1 * d2 - ring(a) * s1 * s2 * U),
            Z12 - (c2**2 + d1s2**2),
        ]
    )

    # EFD madd-2001-ls, projective plus affine.
    z1c2 = Z12 * c3
    s1d2_b = S12 * d3
    d1s2_b = D12 * s3
    U2 = z1c2 * C12
    V2 = d1s2_b * s1d2_b
    S_out = (z1c2 + d1s2_b) * (C12 + s1d2_b) - U2 - V2
    C_out = U2 - V2
    D_out = Z12 * D12 * d3 - ring(a) * S12 * C12 * s3 * c3
    Z_out = z1c2**2 + d1s2_b**2

    sq, cq, dq = case.target
    equations.extend(
        [
            S_out - ring(sq) * Z_out,
            C_out - ring(cq) * Z_out,
            D_out - ring(dq) * Z_out,
        ]
    )

    return ring, equations


def polynomial_stats(polynomials) -> dict[str, int]:
    return {
        "equations": len(polynomials),
        "input_terms": sum(len(poly.dict()) for poly in polynomials),
        "input_max_total_degree": max(int(poly.total_degree()) for poly in polynomials),
    }


def solve(ring, equations, timeout: int) -> dict:
    started = time.perf_counter()
    try:
        alarm(timeout)
        basis = ring.ideal(equations).groebner_basis()
        cancel_alarm()
        elapsed = time.perf_counter() - started
        return {
            "status": "ok",
            "seconds": elapsed,
            "basis_polynomials": len(basis),
            "basis_terms": sum(len(poly.dict()) for poly in basis),
            "basis_max_total_degree": max(int(poly.total_degree()) for poly in basis),
            "peak_rss_mib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024.0,
        }
    except AlarmInterrupt:
        cancel_alarm()
        return {
            "status": "timeout",
            "timeout_seconds": timeout,
            "seconds_before_interrupt": time.perf_counter() - started,
            "peak_rss_mib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024.0,
        }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--h", type=int, required=True)
    parser.add_argument("--system", choices=("direct", "projective"), required=True)
    parser.add_argument("--order", choices=("lex", "deglex", "degrevlex"), required=True)
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument(
        "--layout",
        choices=("coordinate", "point", "intermediate_first"),
        default="coordinate",
        help="Variable layout for the projective system; ignored by the direct system.",
    )
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    case = select_case(43, 2, args.h)

    build_started = time.perf_counter()
    if args.system == "direct":
        ring, equations = direct_system(case, args.order)
    else:
        ring, equations = projective_system(case, args.order, args.layout)
    build_seconds = time.perf_counter() - build_started

    payload = {
        "scope": "bounded synthetic F_43 screen; no real-world ECDLP target",
        "sage_version": version(),
        "configuration": {
            "h": args.h,
            "factor_base_x_size": len(case.x_values),
            "system": args.system,
            "order": args.order,
            "timeout_seconds": args.timeout,
            "variable_layout": args.layout if args.system == "projective" else None,
        },
        "case": {
            **asdict(case),
            "r_values": list(case.r_values),
            "x_values": list(case.x_values),
        },
        "ring_variables": ring.ngens(),
        "build_seconds": build_seconds,
        "input": polynomial_stats(equations),
        "solve": solve(ring, equations, args.timeout),
        "guardrails": [
            "This is a solver and representation diagnostic, not asymptotic evidence.",
            "The Jacobi-native factor base deliberately favors the projective system.",
            "Success requires improving total scaling, not merely lowering polynomial degree.",
        ],
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
