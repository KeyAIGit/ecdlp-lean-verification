#!/usr/bin/env sage
"""
Independent native-Sage replay of the secp256k1 cubic Kummer/GLV identities.

This script intentionally does not import verify_secp.py. It derives the
relevant roots and field identities independently and writes a separate result.
It performs structural arithmetic only and never solves a discrete logarithm.
"""

import hashlib
import json
from pathlib import Path

from sage.all import GF, Integer, PolynomialRing
from sage.version import version as sage_version


P = Integer(2) ** 256 - Integer(2) ** 32 - Integer(977)
BETA_REPO = Integer(
    "7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE",
    16,
)

Fp = GF(P, proof=False)
R = PolynomialRing(Fp, names=("T",))
T = R.gen()

beta_roots = sorted(Integer(root) for root, multiplicity in (T**2 + T + 1).roots() if multiplicity == 1)
assert len(beta_roots) == 2
assert BETA_REPO in beta_roots
beta = Fp(BETA_REPO)
assert beta != 1
assert beta**2 + beta + 1 == 0
assert beta**3 == 1

f = T**3 + 7
assert f.is_irreducible()
K = GF(P**3, name="alpha", modulus=f, proof=False)
alpha = K.gen()
b = K(beta)
one = K.one()

assert alpha**3 == -7
frob_ratio = alpha**P / alpha
assert frob_ratio == b
assert alpha ** (P**2) == b**2 * alpha
assert alpha ** (P**3) == alpha

scale = (b - one) * alpha
z0 = one / (one - b)
assert scale != 0

sample_x = [0, 1, 2, 3, 5, 8, 13, 21, 34, 55]
checks = []
for raw_x in sample_x:
    x = K(Fp(raw_x))
    z = (x - alpha) / scale
    w = z - z0
    z_glv = (b * x - alpha) / scale

    row = {
        "x": int(raw_x),
        "z_frobenius": bool(z**P == b**2 * (z - one)),
        "z_frobenius_squared": bool(z ** (P**2) == one + b * z),
        "glv_equals_frobenius_squared": bool(z_glv == z ** (P**2)),
        "fixed_point_shift": bool(z_glv - z0 == b * w),
        "shift_equals_scaled_x": bool(scale * w == x),
        "cubic_invariant": bool(scale**3 * w**3 == x**3),
    }
    assert all(value for key, value in row.items() if key != "x")
    checks.append(row)

source_sha256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
payload = {
    "scope": "independent native-Sage structural replay; no ECDLP target",
    "sage_version": sage_version,
    "script_sha256": source_sha256,
    "p": str(P),
    "beta_hex": hex(BETA_REPO),
    "beta_roots_hex": [hex(value) for value in beta_roots],
    "extension_polynomial": "T^3 + 7",
    "exact_checks": {
        "extension_irreducible": True,
        "alpha_cubed": "alpha^3=-7",
        "frobenius_ratio": "alpha^p/alpha=beta",
        "frobenius_order_three": "alpha^(p^3)=alpha",
        "kummer_frobenius": "z^p=beta^2*(z-1)",
        "glv_action": "z(beta*x)=1+beta*z=z^(p^2)",
        "shift": "((beta-1)*alpha)*(z-z0)=x",
        "cubic_invariant": "((beta-1)*alpha)^3*(z-z0)^3=x^3",
    },
    "samples": checks,
    "conclusion": (
        "The split cubic Kummer coordinate and secp256k1 GLV expose the same "
        "order-three action. After the affine fixed-point shift, the invariant "
        "is only an invertible scalar re-expression of x^3."
    ),
}

out = Path("experiments/theta_screen_002/sage_replay/independent_verify_result.json")
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
print(json.dumps(payload, indent=2))
print(f"Wrote {out.resolve()}")
