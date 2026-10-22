#!/usr/bin/env python3
"""Generate and check the "x^3 + a x + b has no root in F_p" certificates.

The certificates are used in `Ecdlp/Proved/CubicNoRootCertificate.lean`, where the Lean
kernel re-checks them with `decide +kernel` (no `native_decide`). This script is the
generator of the per-curve block between the markers

    -- BEGIN GENERATED: scripts/certs/cubic_no_root_certs.py
    -- END GENERATED: scripts/certs/cubic_no_root_certs.py

Certificate for f = X^3 - A X - B over F_p (A = -a mod p, B = -b mod p):

  * g = X^p mod f, as a triple (c0, c1, c2) meaning c0 + c1 X + c2 X^2;
  * v with v * (g - X) = 1 mod f.

If r in F_p were a root of f, then r^p = r, so (g - X)(r) = 0, and v * (g - X) = 1
evaluated at r gives 0 = 1. Hence f has no root in F_p. The algorithm follows
pyca/verified-garbage `Proof/Weierstrass/Cubic.lean` (Apache-2.0 OR BSD-3-Clause, see
`THIRD_PARTY_NOTICES.md`); this file is an independent Python implementation.
verified-garbage (commit 38c744308fcd) already kernel-checks certificates for the same nine
curves; a certificate is unique, so the data generated here coincide with upstream's.

The staleness check (--check) is run manually; it is not wired into a CI workflow. The Lean
kernel re-checks the certificate data regardless, so correctness does not depend on it.

Parameters are cited from SEC 2 v2 (secp256k1), FIPS 186-5 / NIST SP 800-186 (P-192 ...
P-521) and RFC 5639 (brainpool). As non-load-bearing sanity checks the script also tests,
in Python only, that p and n pass Miller-Rabin, that G lies on the curve, that n * G = O, and
that 2p + 1 < 3n. None of these Python checks is a Lean proof; the Lean file proves only
what its theorems state.

Usage:
  python3 scripts/certs/cubic_no_root_certs.py           # run the sanity checks, print summary
  python3 scripts/certs/cubic_no_root_certs.py --write   # rewrite the generated Lean block
  python3 scripts/certs/cubic_no_root_certs.py --check   # fail if the Lean block is stale
"""
from __future__ import annotations

import argparse
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "Ecdlp" / "Proved" / "CubicNoRootCertificate.lean"
BEGIN = "-- BEGIN GENERATED: scripts/certs/cubic_no_root_certs.py"
END = "-- END GENERATED: scripts/certs/cubic_no_root_certs.py"

# name -> parameters. `repo` names the existing repository constants reused for that curve
# (their values are then fixed by the repository files; the kernel check of `xpow` fails if
# they differ from the values below).
CURVES: list[dict] = [
    dict(
        ns="secp256k1", title="secp256k1", source="SEC 2 v2, §2.4.1",
        repo=dict(p="Secp256k1.p", n="Secp256k1.n"),
        p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F, a=0, b=7,
        gx=0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
        gy=0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8,
        n=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141),
    dict(
        ns="p192", title="NIST P-192", source="FIPS 186-5 / NIST SP 800-186, §3.2.1.1",
        p=0xfffffffffffffffffffffffffffffffeffffffffffffffff, a=-3,
        b=0x64210519e59c80e70fa7e9ab72243049feb8deecc146b9b1,
        gx=0x188da80eb03090f67cbf20eb43a18800f4ff0afd82ff1012,
        gy=0x07192b95ffc8da78631011ed6b24cdd573f977a11e794811,
        n=0xffffffffffffffffffffffff99def836146bc9b1b4d22831),
    dict(
        ns="p224", title="NIST P-224", source="FIPS 186-5 / NIST SP 800-186, §3.2.1.2",
        p=0xffffffffffffffffffffffffffffffff000000000000000000000001, a=-3,
        b=0xb4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4,
        gx=0xb70e0cbd6bb4bf7f321390b94a03c1d356c21122343280d6115c1d21,
        gy=0xbd376388b5f723fb4c22dfe6cd4375a05a07476444d5819985007e34,
        n=0xffffffffffffffffffffffffffff16a2e0b8f03e13dd29455c5c2a3d),
    dict(
        ns="p256", title="NIST P-256", source="FIPS 186-5 / NIST SP 800-186, §3.2.1.3",
        repo=dict(p="Ecdlp.P256.p", b="Ecdlp.P256.b", n="Ecdlp.P256.n"),
        p=0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff, a=-3,
        b=0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b,
        gx=0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296,
        gy=0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5,
        n=0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551),
    dict(
        ns="p384", title="NIST P-384", source="FIPS 186-5 / NIST SP 800-186, §3.2.1.4",
        p=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff,
        a=-3,
        b=0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef,
        gx=0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7,
        gy=0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f,
        n=0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973),
    dict(
        ns="p521", title="NIST P-521", source="FIPS 186-5 / NIST SP 800-186, §3.2.1.5",
        p=2**521 - 1, a=-3,
        b=0x0051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00,
        gx=0x00c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66,
        gy=0x011839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650,
        n=0x01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409),
    dict(
        ns="brainpoolP256r1", title="brainpoolP256r1", source="RFC 5639, §3.4",
        p=0xA9FB57DBA1EEA9BC3E660A909D838D726E3BF623D52620282013481D1F6E5377,
        a=0x7D5A0975FC2C3057EEF67530417AFFE7FB8055C126DC5C6CE94A4B44F330B5D9,
        b=0x26DC5C6CE94A4B44F330B5D9BBD77CBF958416295CF7E1CE6BCCDC18FF8C07B6,
        gx=0x8BD2AEB9CB7E57CB2C4B482FFC81B7AFB9DE27E1E3BD23C23A4453BD9ACE3262,
        gy=0x547EF835C3DAC4FD97F8461A14611DC9C27745132DED8E545C1D54C72F046997,
        n=0xA9FB57DBA1EEA9BC3E660A909D838D718C397AA3B561A6F7901E0E82974856A7),
    dict(
        ns="brainpoolP384r1", title="brainpoolP384r1", source="RFC 5639, §3.6",
        p=0x8CB91E82A3386D280F5D6F7E50E641DF152F7109ED5456B412B1DA197FB71123ACD3A729901D1A71874700133107EC53,
        a=0x7BC382C63D8C150C3C72080ACE05AFA0C2BEA28E4FB22787139165EFBA91F90F8AA5814A503AD4EB04A8C7DD22CE2826,
        b=0x04A8C7DD22CE28268B39B55416F0447C2FB77DE107DCD2A62E880EA53EEB62D57CB4390295DBC9943AB78696FA504C11,
        gx=0x1D1C64F068CF45FFA2A63A81B7C13F6B8847A3E77EF14FE3DB7FCAFE0CBD10E8E826E03436D646AAEF87B2E247D4AF1E,
        gy=0x8ABE1D7520F9C2A45CB1EB8E95CFD55262B70B29FEEC5864E19C054FF99129280E4646217791811142820341263C5315,
        n=0x8CB91E82A3386D280F5D6F7E50E641DF152F7109ED5456B31F166E6CAC0425A7CF3AB6AF6B7FC3103B883202E9046565),
    dict(
        ns="brainpoolP512r1", title="brainpoolP512r1", source="RFC 5639, §3.7",
        p=0xAADD9DB8DBE9C48B3FD4E6AE33C9FC07CB308DB3B3C9D20ED6639CCA703308717D4D9B009BC66842AECDA12AE6A380E62881FF2F2D82C68528AA6056583A48F3,
        a=0x7830A3318B603B89E2327145AC234CC594CBDD8D3DF91610A83441CAEA9863BC2DED5D5AA8253AA10A2EF1C98B9AC8B57F1117A72BF2C7B9E7C1AC4D77FC94CA,
        b=0x3DF91610A83441CAEA9863BC2DED5D5AA8253AA10A2EF1C98B9AC8B57F1117A72BF2C7B9E7C1AC4D77FC94CADC083E67984050B75EBAE5DD2809BD638016F723,
        gx=0x81AEE4BDD82ED9645A21322E9C4C6A9385ED9F70B5D916C1B43B62EEF4D0098EFF3B1F78E2D0D48D50D1687B93B97D5F7C6D5047406A5E688B352209BCB9F822,
        gy=0x7DDE385D566332ECC0EABFA9CF7822FDF209F70024A57B1AA000C55B881F8111B2DCDE494A5F485E5BCA4BD88A2763AED1CA2B2FA8F0540678CD1E0F3AD80892,
        n=0xAADD9DB8DBE9C48B3FD4E6AE33C9FC07CB308DB3B3C9D20ED6639CCA70330870553E5C414CA92619418661197FAC10471DB1D381085DDADDB58796829CA90069),
]


# ---------------------------------------------------------------- arithmetic
def mul_t(p: int, A: int, B: int, u: tuple, v: tuple) -> tuple:
    """Product in F_p[X]/(X^3 - A X - B); mirrors `mulT` in the Lean file."""
    d0 = u[0] * v[0]
    d1 = u[0] * v[1] + u[1] * v[0]
    d2 = u[0] * v[2] + u[1] * v[1] + u[2] * v[0]
    d3 = u[1] * v[2] + u[2] * v[1]
    d4 = u[2] * v[2]
    return ((d0 + d3 * B) % p, (d1 + d3 * A + d4 * B) % p, (d2 + d4 * A) % p)


def pow_t(p: int, A: int, B: int, fuel: int, u: tuple, e: int) -> tuple:
    """Square-and-multiply with fuel; mirrors `powT` in the Lean file."""
    if fuel == 0 or e == 0:
        return (1, 0, 0)
    sq = pow_t(p, A, B, fuel - 1, mul_t(p, A, B, u, u), e // 2)
    return sq if e % 2 == 0 else mul_t(p, A, B, u, sq)


def inverse_t(p: int, A: int, B: int, h: tuple) -> tuple:
    """Solve v * h = 1 in F_p[X]/(X^3 - A X - B) by Gaussian elimination."""
    cols = [mul_t(p, A, B, e, h) for e in ((1, 0, 0), (0, 1, 0), (0, 0, 1))]
    m = [[cols[j][i] for j in range(3)] + [1 if i == 0 else 0] for i in range(3)]
    for c in range(3):
        piv = next(r for r in range(c, 3) if m[r][c] % p)
        m[c], m[piv] = m[piv], m[c]
        iv = pow(m[c][c], -1, p)
        m[c] = [x * iv % p for x in m[c]]
        for r in range(3):
            if r != c and m[r][c]:
                f = m[r][c]
                m[r] = [(x - f * y) % p for x, y in zip(m[r], m[c])]
    return tuple(m[i][3] for i in range(3))


def is_probable_prime(n: int, rounds: int = 40) -> bool:
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    rng = random.Random(n)  # deterministic per input
    for _ in range(rounds):
        x = pow(rng.randrange(2, n - 1), d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def ec_mul(p: int, a: int, k: int, P):
    """Affine double-and-add on y^2 = x^3 + a x + b; None is the point at infinity."""
    def add(P, Q):
        if P is None:
            return Q
        if Q is None:
            return P
        (x1, y1), (x2, y2) = P, Q
        if x1 == x2 and (y1 + y2) % p == 0:
            return None
        if P == Q:
            lam = (3 * x1 * x1 + a) * pow(2 * y1, -1, p) % p
        else:
            lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
        x3 = (lam * lam - x1 - x2) % p
        return (x3, (lam * (x1 - x3) - y1) % p)
    R = None
    while k:
        if k & 1:
            R = add(R, P)
        P = add(P, P)
        k >>= 1
    return R


# ---------------------------------------------------------------- certificates
def certificate(c: dict) -> dict:
    p = c["p"]
    a = c["a"] % p
    b = c["b"] % p
    A, B = (-a) % p, (-b) % p
    fuel = p.bit_length()
    g = pow_t(p, A, B, fuel, (0, 1, 0), p)
    h = (g[0], (g[1] - 1) % p, g[2])
    v = inverse_t(p, A, B, h)
    assert mul_t(p, A, B, v, (g[0], (g[1] + p - 1) % p, g[2])) == (1, 0, 0)
    return dict(p=p, a=a, b=b, A=A, B=B, fuel=fuel, g=g, v=v)


def sanity(c: dict) -> list[str]:
    p, n = c["p"], c["n"]
    a, b = c["a"] % p, c["b"] % p
    G = (c["gx"], c["gy"])
    checks = {
        "p probable prime": is_probable_prime(p),
        "n probable prime": is_probable_prime(n),
        "G on curve": (G[1] ** 2 - G[0] ** 3 - a * G[0] - b) % p == 0,
        "discriminant nonzero": (4 * a ** 3 + 27 * b ** 2) % p != 0,
        "n * G = O": ec_mul(p, a, n, G) is None,
        "2p + 1 < 3n": 2 * p + 1 < 3 * n,
    }
    return [k for k, ok in checks.items() if not ok]


def lean_hex(x: int) -> str:
    return "0x" + format(x, "x")


def lean_block(c: dict) -> str:
    k = certificate(c)
    ns, repo = c["ns"], c.get("repo", {})
    a_is_m3 = c["a"] == -3
    lines = [f"/-! ### {c['title']} ({c['source']}) -/", "", f"namespace {ns}", ""]
    if "p" in repo:
        lines += [f"/-- Field prime `p` of {c['title']}: the repository constant `{repo['p']}`. -/",
                  f"abbrev p : ℕ := {repo['p']}"]
    else:
        lines += [f"/-- Field prime `p` of {c['title']} ({c['source']}). -/",
                  f"def p : ℕ := {lean_hex(c['p'])}"]
    lines.append("")
    if a_is_m3:
        lines += ["/-- Coefficient `a = −3`, as the residue `p − 3`. -/", "def a : ℕ := p - 3"]
    else:
        lines += [f"/-- Coefficient `a` of {c['title']} ({c['source']}). -/",
                  f"def a : ℕ := {lean_hex(c['a'])}" if c["a"] > 9 else f"def a : ℕ := {c['a']}"]
    lines.append("")
    if "b" in repo:
        lines += [f"/-- Coefficient `b`: the repository constant `{repo['b']}`. -/",
                  f"abbrev b : ℕ := {repo['b']}"]
    else:
        lines += [f"/-- Coefficient `b` of {c['title']} ({c['source']}). -/",
                  f"def b : ℕ := {lean_hex(c['b'])}" if c["b"] > 9 else f"def b : ℕ := {c['b']}"]
    lines.append("")
    if "n" in repo:
        lines += [f"/-- Published base-point order `n`: the repository constant `{repo['n']}`. -/",
                  f"abbrev n : ℕ := {repo['n']}"]
    else:
        lines += [f"/-- Published base-point order `n` of {c['title']} ({c['source']}). This file",
                  "does not prove that `n` is prime or that the base point has order `n`. -/",
                  f"def n : ℕ := {lean_hex(c['n'])}"]
    lines += [
        "",
        "/-- Certificate data: `A = −a mod p`. -/",
        f"def A : ℕ := {k['A']}",
        "",
        "/-- Certificate data: `B = −b mod p`. -/",
        f"def B : ℕ := {k['B']}",
        "",
        "/-- Certificate data: `g = X^p mod (X³ − A X − B)`. -/",
        f"def g : Tri := ({k['g'][0]},",
        f"  {k['g'][1]},",
        f"  {k['g'][2]})",
        "",
        "/-- Certificate data: the inverse of `g − X` modulo `X³ − A X − B`. -/",
        f"def v : Tri := ({k['v'][0]},",
        f"  {k['v'][1]},",
        f"  {k['v'][2]})",
        "",
        "/-- Kernel check: `X^p ≡ g (mod X³ − A X − B)`. -/",
        f"theorem xpow : powT p A B {k['fuel']} (0, 1, 0) p = g := by decide +kernel",
        "",
        "/-- Kernel check: `v · (g − X) ≡ 1 (mod X³ − A X − B)`. -/",
        "theorem inv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0) := by",
        "  decide +kernel",
        "",
        f"/-- **`x³ + a x + b` has no root in `𝔽_p`** for {c['title']}. -/",
        "theorem cubic_ne_zero [Fact p.Prime] :",
        "    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 :=",
        f"  cubic_ne_zero_of_cert p A B {k['fuel']} a b (by decide +kernel) (by decide +kernel)",
        "    (by decide +kernel) g v xpow inv",
        "",
        "/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/",
        "theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by decide +kernel",
        "",
        f"/-- **Conditional exact count** for {c['title']}: assuming `[Fact p.Prime]`, for a curve",
        "`y² = x³ + a x + b` over `𝔽_p` with `[W.IsElliptic]` (Δ ≠ 0), any point of additive order",
        "`n` forces `#E(𝔽_p) = n`. Nonsingularity and the order of a point are hypotheses here,",
        "not proved facts. -/",
        "theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))",
        "    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)",
        "    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}",
        "    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n :=",
        "  natCard_point_eq_of_noRoot cubic_ne_zero (by decide +kernel) two_mul_add_one_lt_three_mul",
        "    W h₁ h₂ h₃ h₄ h₆ hG",
        "",
        f"end {ns}",
    ]
    return "\n".join(lines)


def generated_block() -> str:
    return "\n\n".join(lean_block(c) for c in CURVES)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()

    failures = []
    for c in CURVES:
        bad = sanity(c)
        k = certificate(c)
        status = "OK" if not bad else "FAIL: " + ", ".join(bad)
        print(f"{c['title']:16s} p bits={k['fuel']:3d}  certificate OK  sanity {status}")
        failures += bad
    if failures:
        return 1

    block = generated_block()
    if not (args.write or args.check):
        return 0
    text = LEAN.read_text(encoding="utf-8")
    head, sep1, rest = text.partition(BEGIN + "\n")
    _, sep2, tail = rest.partition(END)
    if not (sep1 and sep2):
        print(f"markers not found in {LEAN.relative_to(ROOT)}", file=sys.stderr)
        return 1
    new = head + BEGIN + "\n\n" + block + "\n\n" + END + tail
    if args.write:
        LEAN.write_text(new, encoding="utf-8")
        print(f"wrote {LEAN.relative_to(ROOT)}")
        return 0
    if new != text:
        print(f"{LEAN.relative_to(ROOT)}: generated certificate block is stale; "
              "run scripts/certs/cubic_no_root_certs.py --write", file=sys.stderr)
        return 1
    print(f"{LEAN.relative_to(ROOT)}: generated certificate block is current")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
