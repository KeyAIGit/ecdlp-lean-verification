import Mathlib
import Ecdlp.Secp256k1Verified
import Ecdlp.Proved.P256Curve

/-!
# OPEN TARGET (frozen statements): kernel-checked certificates that `x³ + a x + b` has no root in `𝔽_p`

The exact-count theorem `Ecdlp.Weierstrass.natCard_point_eq_of_addOrderOf`
(`PrimeOrderCardinality.lean`) needs the 2-torsion cubic to have no root in `𝔽_p`. This file
supplies a certificate format for that fact and checks it for nine standard curves.

This file is an **open stem** (statements frozen before proof; each proof is `sorry`).
It is not imported by `Ecdlp.lean`, not built, and excluded from the no-`sorry` gate. The
proof is intended to land in `Ecdlp/Proved/CubicNoRootCertificate.lean`, which consumes this stem.
The certificate data (`A`, `B`, `g`, `v` per curve) is part of the proof, not of the
frozen statements.

## Certificate

Write `f = X³ − A X − B` with `A ≡ −a`, `B ≡ −b (mod p)`, and represent residues modulo `f` as
triples `c₀ + c₁X + c₂X²` of natural numbers (`Tri`). The certificate is two triples:

* `g = X^p mod f`, computed by square-and-multiply (`powT`);
* `v` with `v · (g − X) ≡ 1 (mod f)`.

If `r ∈ 𝔽_p` were a root of `f`, evaluation at `r` is a ring map, `r^p = r` (`ZMod.pow_card`),
so `(g − X)(r) = 0`, and `v · (g − X) ≡ 1` would give `0 = 1` (`noRoot_of_cert`).

All arithmetic is on `ℕ`, so the per-curve checks `xpow` and `inv` are closed by
`decide +kernel`: the kernel evaluates them (with its GMP-accelerated `Nat` operations), and
no `native_decide` is used anywhere in this file. The remaining hypothesis `[Fact p.Prime]` is
a hypothesis of the theorems, not an axiom; it is discharged for secp256k1 and P-256 by the
Pratt certificates elsewhere in the repository, and not discharged here for the other curves.

## Curves

secp256k1 (SEC 2 v2 §2.4.1), NIST P-192, P-224, P-256, P-384, P-521 (FIPS 186-5, curves
specified in NIST SP 800-186 §3.2.1.1–§3.2.1.5) and brainpoolP256r1, brainpoolP384r1,
brainpoolP512r1 (RFC 5639 §3.4, §3.6, §3.7). For secp256k1 and P-256 the repository's own
constants are reused. For each curve the file states

* `cubic_ne_zero`: `x³ + a x + b ≠ 0` for every `x : ZMod p` (assuming `p` prime);
* `two_mul_add_one_lt_three_mul`: `2p + 1 < 3n`;
* `card_eq_of_addOrderOf`: a conditional exact count, `#E(𝔽_p) = n` for any curve
  `y² = x³ + a x + b` over `𝔽_p` that has a point of additive order `n`.

For curves other than secp256k1 and P-256 this file does **not** prove that `p` or `n` is
prime, nor that the published base point has order `n`. In the proof module the per-curve
block is generated, and checked for staleness, by `scripts/certs/cubic_no_root_certs.py`.

## Provenance

The certificate algorithm follows pyca/verified-garbage `Proof/Weierstrass/Cubic.lean`
(`noRoot_of_cert`, Apache-2.0 OR BSD-3-Clause; see `THIRD_PARTY_NOTICES.md`). The Lean code
here is written for this repository and its `ZMod p` statements.
-/

namespace Ecdlp.CubicCert

/-- A residue `c₀ + c₁X + c₂X²` modulo a monic cubic, with coefficients in `ℕ`. -/
abbrev Tri := ℕ × ℕ × ℕ

/-- Product in `𝔽_p[X]/(X³ − A X − B)`, reducing with `X³ = A X + B` and
`X⁴ = A X² + B X`. -/
def mulT (p A B : ℕ) (u v : Tri) : Tri :=
  let d0 := u.1 * v.1
  let d1 := u.1 * v.2.1 + u.2.1 * v.1
  let d2 := u.1 * v.2.2 + u.2.1 * v.2.1 + u.2.2 * v.1
  let d3 := u.2.1 * v.2.2 + u.2.2 * v.2.1
  let d4 := u.2.2 * v.2.2
  ((d0 + d3 * B) % p, (d1 + d3 * A + d4 * B) % p, (d2 + d4 * A) % p)

/-- `u ^ e` in `𝔽_p[X]/(X³ − A X − B)` for `e < 2 ^ fuel`, by square-and-multiply.
Structural recursion on `fuel`, so the kernel can unfold it. -/
def powT (p A B : ℕ) : ℕ → Tri → ℕ → Tri
  | 0, _, _ => (1, 0, 0)
  | n + 1, u, e =>
    if e = 0 then (1, 0, 0)
    else if e % 2 = 0 then powT p A B n (mulT p A B u u) (e / 2)
    else mulT p A B u (powT p A B n (mulT p A B u u) (e / 2))

/-- **Soundness of the no-root certificate.** If `g = X^p mod (X³ − A X − B)` and
`v · (g − X) ≡ 1`, then `X³ − A X − B` has no root in `ZMod p` (for `p` prime). -/
theorem noRoot_of_cert (p A B n : ℕ) [Fact p.Prime] (hn : p < 2 ^ n) (g v : Tri)
    (hg : powT p A B n (0, 1, 0) p = g)
    (hv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0)) :
    ∀ r : ZMod p, r ^ 3 ≠ A * r + B := by
  sorry

/-- **Certificate in short-Weierstrass form.** With `A + a ≡ 0` and `B + b ≡ 0 (mod p)` checked
on `ℕ`, a valid certificate shows `x³ + a x + b ≠ 0` for every `x : ZMod p`. -/
theorem cubic_ne_zero_of_cert (p A B n : ℕ) [Fact p.Prime] (a b : ℕ)
    (hA : (A + a) % p = 0) (hB : (B + b) % p = 0) (hn : p < 2 ^ n) (g v : Tri)
    (hg : powT p A B n (0, 1, 0) p = g)
    (hv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0)) :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 := by
  sorry

/-- **Exact count from a no-root fact over `ZMod p`.** For `p` an odd prime, a curve
`y² = x³ + a x + b` over `ZMod p` whose cubic has no root, and a point of additive order `n`
with `2p + 1 < 3n`, the curve has exactly `n` points. A specialization of
`natCard_point_eq_of_addOrderOf`. -/
theorem natCard_point_eq_of_noRoot {p a b n : ℕ} [Fact p.Prime]
    (hcubic : ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0) (hp2 : p ≠ 2)
    (hlt : 2 * p + 1 < 3 * n) (W : WeierstrassCurve (ZMod p)) [W.IsElliptic]
    (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = (a : ZMod p))
    (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point} (hG : addOrderOf G = n) :
    Nat.card W.toAffine.Point = n := by
  sorry

/-! ### secp256k1 (SEC 2 v2, §2.4.1) -/

namespace secp256k1

/-- Field prime `p` of secp256k1: the repository constant `Secp256k1.p`. -/
abbrev p : ℕ := Secp256k1.p

/-- Coefficient `a` of secp256k1 (SEC 2 v2, §2.4.1). -/
def a : ℕ := 0

/-- Coefficient `b` of secp256k1 (SEC 2 v2, §2.4.1). -/
def b : ℕ := 7

/-- Published base-point order `n`: the repository constant `Secp256k1.n`. -/
abbrev n : ℕ := Secp256k1.n

/-- **`x³ + a x + b` has no root in `𝔽_p`** for secp256k1. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 := by
  sorry

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by
  sorry

/-- **Conditional exact count** for secp256k1: for a curve `y² = x³ + a x + b` over
`𝔽_p` (with `p` prime), any point of additive order `n` forces `#E(𝔽_p) = n`. The order
of a point is a hypothesis here, not a proved fact. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n := by
  sorry

end secp256k1

/-! ### NIST P-192 (FIPS 186-5 / NIST SP 800-186, §3.2.1.1) -/

namespace p192

/-- Field prime `p` of NIST P-192 (FIPS 186-5 / NIST SP 800-186, §3.2.1.1). -/
def p : ℕ := 0xfffffffffffffffffffffffffffffffeffffffffffffffff

/-- Coefficient `a = −3`, as the residue `p − 3`. -/
def a : ℕ := p - 3

/-- Coefficient `b` of NIST P-192 (FIPS 186-5 / NIST SP 800-186, §3.2.1.1). -/
def b : ℕ := 0x64210519e59c80e70fa7e9ab72243049feb8deecc146b9b1

/-- Published base-point order `n` of NIST P-192 (FIPS 186-5 / NIST SP 800-186, §3.2.1.1). This file
does not prove that `n` is prime or that the base point has order `n`. -/
def n : ℕ := 0xffffffffffffffffffffffff99def836146bc9b1b4d22831

/-- **`x³ + a x + b` has no root in `𝔽_p`** for NIST P-192. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 := by
  sorry

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by
  sorry

/-- **Conditional exact count** for NIST P-192: for a curve `y² = x³ + a x + b` over
`𝔽_p` (with `p` prime), any point of additive order `n` forces `#E(𝔽_p) = n`. The order
of a point is a hypothesis here, not a proved fact. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n := by
  sorry

end p192

/-! ### NIST P-224 (FIPS 186-5 / NIST SP 800-186, §3.2.1.2) -/

namespace p224

/-- Field prime `p` of NIST P-224 (FIPS 186-5 / NIST SP 800-186, §3.2.1.2). -/
def p : ℕ := 0xffffffffffffffffffffffffffffffff000000000000000000000001

/-- Coefficient `a = −3`, as the residue `p − 3`. -/
def a : ℕ := p - 3

/-- Coefficient `b` of NIST P-224 (FIPS 186-5 / NIST SP 800-186, §3.2.1.2). -/
def b : ℕ := 0xb4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4

/-- Published base-point order `n` of NIST P-224 (FIPS 186-5 / NIST SP 800-186, §3.2.1.2). This file
does not prove that `n` is prime or that the base point has order `n`. -/
def n : ℕ := 0xffffffffffffffffffffffffffff16a2e0b8f03e13dd29455c5c2a3d

/-- **`x³ + a x + b` has no root in `𝔽_p`** for NIST P-224. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 := by
  sorry

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by
  sorry

/-- **Conditional exact count** for NIST P-224: for a curve `y² = x³ + a x + b` over
`𝔽_p` (with `p` prime), any point of additive order `n` forces `#E(𝔽_p) = n`. The order
of a point is a hypothesis here, not a proved fact. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n := by
  sorry

end p224

/-! ### NIST P-256 (FIPS 186-5 / NIST SP 800-186, §3.2.1.3) -/

namespace p256

/-- Field prime `p` of NIST P-256: the repository constant `Ecdlp.P256.p`. -/
abbrev p : ℕ := Ecdlp.P256.p

/-- Coefficient `a = −3`, as the residue `p − 3`. -/
def a : ℕ := p - 3

/-- Coefficient `b`: the repository constant `Ecdlp.P256.b`. -/
abbrev b : ℕ := Ecdlp.P256.b

/-- Published base-point order `n`: the repository constant `Ecdlp.P256.n`. -/
abbrev n : ℕ := Ecdlp.P256.n

/-- **`x³ + a x + b` has no root in `𝔽_p`** for NIST P-256. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 := by
  sorry

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by
  sorry

/-- **Conditional exact count** for NIST P-256: for a curve `y² = x³ + a x + b` over
`𝔽_p` (with `p` prime), any point of additive order `n` forces `#E(𝔽_p) = n`. The order
of a point is a hypothesis here, not a proved fact. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n := by
  sorry

end p256

/-! ### NIST P-384 (FIPS 186-5 / NIST SP 800-186, §3.2.1.4) -/

namespace p384

/-- Field prime `p` of NIST P-384 (FIPS 186-5 / NIST SP 800-186, §3.2.1.4). -/
def p : ℕ := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff

/-- Coefficient `a = −3`, as the residue `p − 3`. -/
def a : ℕ := p - 3

/-- Coefficient `b` of NIST P-384 (FIPS 186-5 / NIST SP 800-186, §3.2.1.4). -/
def b : ℕ := 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef

/-- Published base-point order `n` of NIST P-384 (FIPS 186-5 / NIST SP 800-186, §3.2.1.4). This file
does not prove that `n` is prime or that the base point has order `n`. -/
def n : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973

/-- **`x³ + a x + b` has no root in `𝔽_p`** for NIST P-384. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 := by
  sorry

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by
  sorry

/-- **Conditional exact count** for NIST P-384: for a curve `y² = x³ + a x + b` over
`𝔽_p` (with `p` prime), any point of additive order `n` forces `#E(𝔽_p) = n`. The order
of a point is a hypothesis here, not a proved fact. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n := by
  sorry

end p384

/-! ### NIST P-521 (FIPS 186-5 / NIST SP 800-186, §3.2.1.5) -/

namespace p521

/-- Field prime `p` of NIST P-521 (FIPS 186-5 / NIST SP 800-186, §3.2.1.5). -/
def p : ℕ := 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

/-- Coefficient `a = −3`, as the residue `p − 3`. -/
def a : ℕ := p - 3

/-- Coefficient `b` of NIST P-521 (FIPS 186-5 / NIST SP 800-186, §3.2.1.5). -/
def b : ℕ := 0x51953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00

/-- Published base-point order `n` of NIST P-521 (FIPS 186-5 / NIST SP 800-186, §3.2.1.5). This file
does not prove that `n` is prime or that the base point has order `n`. -/
def n : ℕ := 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409

/-- **`x³ + a x + b` has no root in `𝔽_p`** for NIST P-521. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 := by
  sorry

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by
  sorry

/-- **Conditional exact count** for NIST P-521: for a curve `y² = x³ + a x + b` over
`𝔽_p` (with `p` prime), any point of additive order `n` forces `#E(𝔽_p) = n`. The order
of a point is a hypothesis here, not a proved fact. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n := by
  sorry

end p521

/-! ### brainpoolP256r1 (RFC 5639, §3.4) -/

namespace brainpoolP256r1

/-- Field prime `p` of brainpoolP256r1 (RFC 5639, §3.4). -/
def p : ℕ := 0xa9fb57dba1eea9bc3e660a909d838d726e3bf623d52620282013481d1f6e5377

/-- Coefficient `a` of brainpoolP256r1 (RFC 5639, §3.4). -/
def a : ℕ := 0x7d5a0975fc2c3057eef67530417affe7fb8055c126dc5c6ce94a4b44f330b5d9

/-- Coefficient `b` of brainpoolP256r1 (RFC 5639, §3.4). -/
def b : ℕ := 0x26dc5c6ce94a4b44f330b5d9bbd77cbf958416295cf7e1ce6bccdc18ff8c07b6

/-- Published base-point order `n` of brainpoolP256r1 (RFC 5639, §3.4). This file
does not prove that `n` is prime or that the base point has order `n`. -/
def n : ℕ := 0xa9fb57dba1eea9bc3e660a909d838d718c397aa3b561a6f7901e0e82974856a7

/-- **`x³ + a x + b` has no root in `𝔽_p`** for brainpoolP256r1. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 := by
  sorry

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by
  sorry

/-- **Conditional exact count** for brainpoolP256r1: for a curve `y² = x³ + a x + b` over
`𝔽_p` (with `p` prime), any point of additive order `n` forces `#E(𝔽_p) = n`. The order
of a point is a hypothesis here, not a proved fact. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n := by
  sorry

end brainpoolP256r1

/-! ### brainpoolP384r1 (RFC 5639, §3.6) -/

namespace brainpoolP384r1

/-- Field prime `p` of brainpoolP384r1 (RFC 5639, §3.6). -/
def p : ℕ := 0x8cb91e82a3386d280f5d6f7e50e641df152f7109ed5456b412b1da197fb71123acd3a729901d1a71874700133107ec53

/-- Coefficient `a` of brainpoolP384r1 (RFC 5639, §3.6). -/
def a : ℕ := 0x7bc382c63d8c150c3c72080ace05afa0c2bea28e4fb22787139165efba91f90f8aa5814a503ad4eb04a8c7dd22ce2826

/-- Coefficient `b` of brainpoolP384r1 (RFC 5639, §3.6). -/
def b : ℕ := 0x4a8c7dd22ce28268b39b55416f0447c2fb77de107dcd2a62e880ea53eeb62d57cb4390295dbc9943ab78696fa504c11

/-- Published base-point order `n` of brainpoolP384r1 (RFC 5639, §3.6). This file
does not prove that `n` is prime or that the base point has order `n`. -/
def n : ℕ := 0x8cb91e82a3386d280f5d6f7e50e641df152f7109ed5456b31f166e6cac0425a7cf3ab6af6b7fc3103b883202e9046565

/-- **`x³ + a x + b` has no root in `𝔽_p`** for brainpoolP384r1. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 := by
  sorry

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by
  sorry

/-- **Conditional exact count** for brainpoolP384r1: for a curve `y² = x³ + a x + b` over
`𝔽_p` (with `p` prime), any point of additive order `n` forces `#E(𝔽_p) = n`. The order
of a point is a hypothesis here, not a proved fact. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n := by
  sorry

end brainpoolP384r1

/-! ### brainpoolP512r1 (RFC 5639, §3.7) -/

namespace brainpoolP512r1

/-- Field prime `p` of brainpoolP512r1 (RFC 5639, §3.7). -/
def p : ℕ := 0xaadd9db8dbe9c48b3fd4e6ae33c9fc07cb308db3b3c9d20ed6639cca703308717d4d9b009bc66842aecda12ae6a380e62881ff2f2d82c68528aa6056583a48f3

/-- Coefficient `a` of brainpoolP512r1 (RFC 5639, §3.7). -/
def a : ℕ := 0x7830a3318b603b89e2327145ac234cc594cbdd8d3df91610a83441caea9863bc2ded5d5aa8253aa10a2ef1c98b9ac8b57f1117a72bf2c7b9e7c1ac4d77fc94ca

/-- Coefficient `b` of brainpoolP512r1 (RFC 5639, §3.7). -/
def b : ℕ := 0x3df91610a83441caea9863bc2ded5d5aa8253aa10a2ef1c98b9ac8b57f1117a72bf2c7b9e7c1ac4d77fc94cadc083e67984050b75ebae5dd2809bd638016f723

/-- Published base-point order `n` of brainpoolP512r1 (RFC 5639, §3.7). This file
does not prove that `n` is prime or that the base point has order `n`. -/
def n : ℕ := 0xaadd9db8dbe9c48b3fd4e6ae33c9fc07cb308db3b3c9d20ed6639cca70330870553e5c414ca92619418661197fac10471db1d381085ddaddb58796829ca90069

/-- **`x³ + a x + b` has no root in `𝔽_p`** for brainpoolP512r1. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 := by
  sorry

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by
  sorry

/-- **Conditional exact count** for brainpoolP512r1: for a curve `y² = x³ + a x + b` over
`𝔽_p` (with `p` prime), any point of additive order `n` forces `#E(𝔽_p) = n`. The order
of a point is a hypothesis here, not a proved fact. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n := by
  sorry

end brainpoolP512r1

end Ecdlp.CubicCert
