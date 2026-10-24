#!/usr/bin/env python3
"""
Independent SageMath verification of the secp256k1 cubic theta/Kummer descent.

Run with:
    sage -python experiments/theta_screen_002/verify_secp.py

Scope:
    Structural identities only. No discrete-log instance is attacked.
"""
from __future__ import annotations

import json
from pathlib import Path

from sage.all import GF, PolynomialRing, Integer, version


P = Integer(2) ** 256 - Integer(2) ** 32 - Integer(977)
BETA_REPO = Integer(
    "7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE",
    16,
)


def main() -> None:
    assert P.is_prime(proof=False)

    Fp = GF(P, proof=False)
    beta = Fp(-7) ** ((P - 1) // 3)

    assert Integer(beta) == BETA_REPO
    assert beta != 1
    assert beta**2 + beta + 1 == 0
    assert beta**3 == 1

    RT = PolynomialRing(Fp, names=("T",))
    T = RT.gen()
    f = T**3 + 7
    assert f.is_irreducible()

    K = GF(P**3, name="alpha", modulus=f, proof=False)
    alpha = K.gen()
    b = K(beta)
    one = K.one()

    assert alpha**3 == -7
    assert alpha**P == b * alpha

    z0 = one / (one - b)
    denominator = (b - one) * alpha
    assert denominator != 0

    sample_x = [0, 1, 2, 3, 5, 8, 13, 21]
    checks = []

    for raw_x in sample_x:
        x = K(Fp(raw_x))
        z = (x - alpha) / denominator
        w = z - z0
        z_glv = (b * x - alpha) / denominator

        row = {
            "x": raw_x,
            "frobenius": z**P == b**2 * (z - one),
            "frobenius_squared": z ** (P**2) == one + b * z,
            "glv_equals_frobenius_squared": z_glv == z ** (P**2),
            "shift_linearizes_glv": (z_glv - z0) == b * w,
            "shift_is_scaled_x": w == x / denominator,
            "cubic_invariant": denominator**3 * w**3 == x**3,
        }
        assert all(value for key, value in row.items() if key != "x")
        checks.append(row)

    payload = {
        "scope": "structural SageMath verification; no ECDLP target",
        "sage_version": version(),
        "p": str(P),
        "beta_hex": hex(BETA_REPO),
        "extension_polynomial": "T^3 + 7",
        "identities": {
            "alpha_frobenius": "alpha^p = beta*alpha",
            "kummer_coordinate": "z = (x-alpha)/((beta-1)*alpha)",
            "frobenius_on_z": "z^p = beta^2*(z-1)",
            "glv_on_z": "z(beta*x) = 1 + beta*z = z^(p^2)",
            "fixed_point": "z0 = 1/(1-beta)",
            "shift": "w = z-z0 = x/((beta-1)*alpha)",
            "orbit_invariant": "((beta-1)*alpha)^3*w^3 = x^3",
        },
        "samples": checks,
        "conclusion": (
            "The cubic theta/Kummer coordinate and the GLV action generate one "
            "C3 action, not two independent C3 actions. After shifting to its "
            "fixed point, the cubic invariant is an invertible scalar multiple "
            "of x^3."
        ),
    }

    out = Path("experiments/theta_screen_002/verify_secp_result.json")
    out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(json.dumps(payload, indent=2))
    print(f"Wrote {out.resolve()}")


if __name__ == "__main__":
    main()
