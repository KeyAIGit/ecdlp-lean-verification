#!/usr/bin/env python3
"""Recursive Pratt primality certificate for secp256k1 p and n, with Lean emission.

Proves `m` prime via `Nat.lucas_primality`: a witness `a` of order m-1, plus a
recursive certificate for every prime q | m-1. This script builds, *verifies*, and
emits the Lean proof (one `pr_<m>` theorem per non-trivial prime, bottom-up).

The Lean kernel checks every emitted arithmetic leaf:
- witness powers: `decide +kernel` on `Ecdlp.Kernel.powMod`, which computes them on
  `Nat`; `Ecdlp.Kernel.kpow_eq_one` / `kpow_ne_one` (`Ecdlp/Proved/KernelPowMod.lean`)
  move them into `ZMod m`;
- the factorisation of m-1 and the side conditions `1 < m`, `e < 2^bits`:
  `decide +kernel` on `Nat` arithmetic (multiplication, powers, subtraction);
- primality of each prime factor below `SMALL` (2^20): `norm_num`.
No `native_decide` is emitted.

Usage:  python3 scripts/pratt_certificate.py            # verify both
        python3 scripts/pratt_certificate.py lean p|n   # emit Lean to stdout
"""
import sys
from sympy import factorint, isprime

SMALL = 1 << 20  # below this, Lean's `norm_num` proves primality directly

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def witness(m):
    facs = list(factorint(m - 1))
    for a in range(2, 500):
        if pow(a, m - 1, m) == 1 and all(pow(a, (m - 1) // q, m) != 1 for q in facs):
            return a
    raise RuntimeError(m)

def cert(m):
    assert isprime(m), m
    if m < SMALL:
        return {"m": m, "small": True}
    f = factorint(m - 1)
    return {"m": m, "a": witness(m), "factors": list(f.items()),
            "children": [cert(q) for q in f]}

def verify(c):
    m = c["m"]
    if c.get("small"):
        return isprime(m)
    a = c["a"]
    assert pow(a, m - 1, m) == 1
    prod = 1
    for q, e in c["factors"]:
        assert pow(a, (m - 1) // q, m) != 1
        prod *= q ** e
    assert prod == m - 1
    return all(verify(ch) for ch in c["children"])

def ref(q):
    return f"(show Nat.Prime {q} by norm_num)" if q < SMALL else f"pr_{q}"

def emit(c):
    """One `pr_<m>` theorem (assumes children already emitted)."""
    m, a, facs = c["m"], c["a"], c["factors"]
    _terms = [f"{q} ^ {e}" for q, e in facs]
    prod = _terms[-1]
    for _t in reversed(_terms[:-1]):
        prod = f"{_t} * ({prod})"
    # Kernel leaves: `e < 2^bits` holds for every exponent used (e <= m - 1 < 2^bits).
    bits = m.bit_length()
    kargs = f"{a} {bits} _ (Nat.cast_ofNat).symm (by decide +kernel) (by decide +kernel) (by decide +kernel)"
    leaf = f"exact Ecdlp.Kernel.kpow_ne_one _ {kargs}"
    L = [f"theorem pr_{m} : Nat.Prime {m} := by",
         f"  refine lucas_primality {m} ({a} : ZMod {m}) (Ecdlp.Kernel.kpow_eq_one _ {kargs}) ?_",
         f"  intro q hq hqd",
         f"  rw [show ({m} : ℕ) - 1 = {prod} by decide +kernel] at hqd"]
    def win(q, hyp, pad):
        L.append(f"{pad}rw [(Nat.prime_dvd_prime_iff_eq hq {ref(q)}).mp "
                 f"(hq.dvd_of_dvd_pow {hyp})]; {leaf}")
    def go(rem, hyp, pad):
        if len(rem) == 1:
            win(rem[0][0], hyp, pad)
        else:
            L.append(f"{pad}rcases (Nat.Prime.dvd_mul hq).mp {hyp} with h | h")
            L.append(f"{pad}· " + f"rw [(Nat.prime_dvd_prime_iff_eq hq {ref(rem[0][0])}).mp "
                     f"(hq.dvd_of_dvd_pow h)]; {leaf}")
            L.append(f"{pad}·")
            go(rem[1:], "h", pad + "  ")
    go(facs, "hqd", "  ")
    return "\n".join(L)

def collect(c, out, seen):
    if c.get("small") or c["m"] in seen:
        return
    for ch in c["children"]:
        collect(ch, out, seen)
    seen.add(c["m"])
    out.append(c)

def lean_file(which):
    return lean_file_for("secp256k1", which)

# Curve configs: each fills the same three slots the emitter needs — the modulus values,
# the Lean constant namespace (`<const>.p` / `<const>.n`), and the import that defines them.
# secp256k1 is the reference; p256 reuses the identical Pratt/lucas_primality pattern for a
# second curve (the Research OS cross-domain check).
CURVES = {
    "secp256k1": {
        "p": p, "n": n,
        "const": "Secp256k1", "import": "Ecdlp.Secp256k1Verified",
        "thm": "secp256k1", "ns": "Ecdlp.Primality", "label": "secp256k1",
    },
    "p256": {
        "p": 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff,
        "n": 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551,
        "const": "Ecdlp.P256", "import": "Ecdlp.Proved.P256Curve",
        "thm": "p256", "ns": "Ecdlp.P256.Primality", "label": "NIST P-256",
    },
}


def lean_file_for(curve, which):
    cfg = CURVES[curve]
    m = cfg[which]
    c = cert(m)
    assert verify(c)
    nodes = []
    collect(c, nodes, set())
    head = (f"import Mathlib\nimport {cfg['import']}\nimport Ecdlp.Proved.KernelPowMod\n\n"
            f"/-! # Machine-checked primality of {cfg['label']} `{which}` (Pratt certificate, "
            f"generated by `scripts/pratt_certificate.py`). Witness a={c['a']}, "
            f"{len(nodes)} recursive nodes. The Lean kernel checks every arithmetic leaf: "
            f"witness powers by `decide +kernel` on `Ecdlp.Kernel.powMod`, each factorisation "
            f"of `m - 1` by `decide +kernel` on `Nat` arithmetic, and the primality of each "
            f"prime factor below 2^20 by `norm_num`; no `native_decide`. -/"
            f"\n\nnamespace {cfg['ns']}\n"
            f"open Nat\n")
    body = "\n\n".join(emit(x) for x in nodes)
    tail = (f"\n\n/-- {cfg['label']} {which} is prime (full Pratt certificate). -/\n"
            f"theorem {cfg['thm']}_{which}_prime : Nat.Prime {cfg['const']}.{which} := pr_{m}\n\n"
            f"instance : Fact (Nat.Prime {cfg['const']}.{which}) := ⟨{cfg['thm']}_{which}_prime⟩\n\n"
            f"end {cfg['ns']}\n")
    return head + "\n" + body + tail


if __name__ == "__main__":
    # Usage: pratt_certificate.py lean <p|n> [curve]   (curve defaults to secp256k1)
    if len(sys.argv) >= 3 and sys.argv[1] == "lean":
        curve = sys.argv[3] if len(sys.argv) >= 4 else "secp256k1"
        print(lean_file_for(curve, sys.argv[2]))
    else:
        for cname, cfg in CURVES.items():
            for nm in ("p", "n"):
                c = cert(cfg[nm]); verify(c)
                _nodes = []
                collect(c, _nodes, set())
                print(f"{cname} {nm}: verified, a={c['a']}, nodes={len(_nodes)}")
