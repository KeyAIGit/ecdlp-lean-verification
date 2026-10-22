import Mathlib
import Ecdlp.Secp256k1Verified
import Ecdlp.Proved.P256Curve
import Ecdlp.Proved.PrimeOrderCardinality

/-!
# Kernel-checked certificates that `x³ + a x + b` has no root in `𝔽_p`

The exact-count theorem `Ecdlp.Weierstrass.natCard_point_eq_of_addOrderOf`
(`PrimeOrderCardinality.lean`) needs the 2-torsion cubic to have no root in `𝔽_p`. This file
supplies a certificate format for that fact and checks it for nine standard curves.

## Certificate

Write `f = X³ − A X − B` with `A ≡ −a`, `B ≡ −b (mod p)`, and represent residues modulo `f` as
triples `c₀ + c₁X + c₂X²` of natural numbers (`Tri`). The certificate is two triples:

* `g = X^p mod f`, computed by square-and-multiply (`powT`);
* `v` with `v · (g − X) ≡ 1 (mod f)`.

If `r ∈ 𝔽_p` were a root of `f`, evaluation at `r` is a ring map, `r^p = r` (`ZMod.pow_card`),
so `(g − X)(r) = 0`, and `v · (g − X) ≡ 1` would give `0 = 1` (`noRoot_of_cert`).

All arithmetic is on `ℕ`, so the per-curve checks `xpow` and `inv` are closed by
`decide +kernel`: they are checked by kernel reduction, including the kernel's built-in
GMP-backed `Nat` arithmetic (part of the standard kernel); no compiler trust, and no
`native_decide` is used anywhere in this file. The remaining hypothesis `[Fact p.Prime]` is
a hypothesis of the theorems, not an axiom; it is discharged for secp256k1 and P-256 by the
Pratt certificates elsewhere in the repository, and not discharged here for the other curves.

## Curves

secp256k1 (SEC 2 v2 §2.4.1), NIST P-192, P-224, P-256, P-384, P-521 (FIPS 186-5, curves
specified in NIST SP 800-186 §3.2.1.1–§3.2.1.5) and brainpoolP256r1, brainpoolP384r1,
brainpoolP512r1 (RFC 5639 §3.4, §3.6, §3.7). For secp256k1 and P-256 the repository's own
constants are reused. For each curve the file proves

* `cubic_ne_zero`: `x³ + a x + b ≠ 0` for every `x : ZMod p` (assuming `p` prime);
* `two_mul_add_one_lt_three_mul`: `2p + 1 < 3n`;
* `card_eq_of_addOrderOf`: a conditional exact count under `[Fact p.Prime]`: `#E(𝔽_p) = n`
  for any curve `W` with `[W.IsElliptic]` (Δ ≠ 0) and equation `y² = x³ + a x + b` over `𝔽_p`
  that has a point of additive order `n`.

For curves other than secp256k1 and P-256 this file does **not** prove that `p` or `n` is
prime, that the curve is nonsingular, nor that the published base point has order `n`. The
per-curve block is generated, and checked for staleness, by
`scripts/certs/cubic_no_root_certs.py` (a manual check; no CI workflow runs it).

## Provenance (third-party code)

`Tri`, `mulT`, `powT`, `evalT`, `evalT_mulT`, `evalT_powT` and `noRoot_of_cert` are adapted from
pyca/verified-garbage, file `lean/VerifiedGarbage/Proof/Weierstrass/Cubic.lean` at commit
`38c744308fcd` (namespace `VG.Proof.Weierstrass`). That project is licensed Apache-2.0 OR
BSD-3-Clause ("Individual contributors"); the code is used here under Apache-2.0. See
`THIRD_PARTY_NOTICES.md`. Changes made here: the namespace, docstrings and formatting; the
`ite_eq_left`/`ite_eq_right` rewrites in `evalT_powT` replaced by `if_pos`/`if_neg`; and
`cubic_ne_zero_of_cert`, adapted from VG's `noTwoTorsion_of_cert`, is stated for natural-number
coefficients over `ZMod p` instead of VG's specification curve type. `natCard_point_eq_of_noRoot`
and the per-curve block are written for this repository.

## Prior results (same upstream commit)

verified-garbage already kernel-checks the no-root (no rational 2-torsion) fact for the same
nine curves: `VG.Proof.P256.noTwoTorsion`, and for the other eight curves the `noTwoTorsion`
field of `VG.Proof.<Curve>.good` (built by `Good.of_cert`). For P-256/P-384/P-521 it also
establishes `#E = n`, inside the proof of `VG.Proof.Weierstrass.primeOrder_of`, as
`Nat.card (wcC C).Point = C.n`; there `wcC C` is Mathlib's `WeierstrassCurve.Affine` over
`ZMod C.p`, built from the specification curve `C`. That count is not exported: the exported
`VG.Proof.<Curve>.primeOrder` states that every point other than the identity has order `n`.
This repository's addition for that count is the exported theorem `p256_card_point_eq_n` for
`Ecdlp.P256.P256` (`P256CardinalityExact.lean`). The certificates here were regenerated
independently (by `scripts/certs/cubic_no_root_certs.py`; a certificate is unique, so the
data coincide with upstream's). The ledger therefore lists the per-curve block as
upstream-derived, outside the headline count.
-/

namespace Ecdlp.CubicCert

open Ecdlp.Weierstrass

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

section Eval

variable {p : ℕ}

/-- Evaluate a triple at `r : ZMod p`. -/
def evalT (r : ZMod p) (u : Tri) : ZMod p := u.1 + u.2.1 * r + u.2.2 * r ^ 2

variable {A B : ℕ} {r : ZMod p} (hr : r ^ 3 = A * r + B)
include hr

/-- At a root `r` of `X³ − A X − B`, evaluation turns `mulT` into multiplication. -/
theorem evalT_mulT (u v : Tri) : evalT r (mulT p A B u v) = evalT r u * evalT r v := by
  simp only [evalT, mulT, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
  linear_combination (-((u.2.1 * v.2.2 + u.2.2 * v.2.1 : ZMod p) + u.2.2 * v.2.2 * r)) * hr

/-- At a root `r` of `X³ − A X − B`, evaluation turns `powT` into a power, provided the
exponent fits in the fuel. -/
theorem evalT_powT (n : ℕ) (u : Tri) (e : ℕ) (he : e < 2 ^ n) :
    evalT r (powT p A B n u e) = evalT r u ^ e := by
  have h1 : evalT r ((1, 0, 0) : Tri) = 1 := by
    simp only [evalT, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero]
  induction n generalizing u e with
  | zero =>
    have : e = 0 := by simpa using he
    subst this
    rw [powT, h1, _root_.pow_zero]
  | succ n ih =>
    by_cases h0 : e = 0
    · subst h0
      rw [powT, if_pos rfl, h1, _root_.pow_zero]
    have he2 : e / 2 < 2 ^ n := by
      rw [Nat.pow_succ] at he
      omega
    have hsplit : evalT r u ^ e = (evalT r u * evalT r u) ^ (e / 2) * evalT r u ^ (e % 2) := by
      rw [← sq, ← pow_mul, ← pow_add]
      congr 1
      omega
    rw [powT, if_neg h0]
    by_cases h2 : e % 2 = 0
    · rw [if_pos h2, ih _ _ he2, evalT_mulT hr, hsplit, h2, _root_.pow_zero, mul_one]
    · rw [if_neg h2, evalT_mulT hr, ih _ _ he2, evalT_mulT hr, hsplit,
        show e % 2 = 1 by omega, pow_one, mul_comm]

end Eval

/-- **Soundness of the no-root certificate.** If `g = X^p mod (X³ − A X − B)` and
`v · (g − X) ≡ 1`, then `X³ − A X − B` has no root in `ZMod p` (for `p` prime). -/
theorem noRoot_of_cert (p A B n : ℕ) [Fact p.Prime] (hn : p < 2 ^ n) (g v : Tri)
    (hg : powT p A B n (0, 1, 0) p = g)
    (hv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0)) :
    ∀ r : ZMod p, r ^ 3 ≠ A * r + B := by
  intro r hr
  have hx : evalT r ((0, 1, 0) : Tri) = r := by
    simp only [evalT, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero, one_mul, zero_add]
  have hgr : evalT r g = r := by
    rw [← hg, evalT_powT hr _ _ _ hn, hx, ZMod.pow_card]
  have hh : evalT r ((g.1, (g.2.1 + p - 1) % p, g.2.2) : Tri) = 0 := by
    have hp1 : 1 ≤ g.2.1 + p := by
      have := (Fact.out : p.Prime).one_lt
      omega
    have : evalT r ((g.1, (g.2.1 + p - 1) % p, g.2.2) : Tri) = evalT r g - r := by
      simp only [evalT, ZMod.natCast_mod, Nat.cast_sub hp1, Nat.cast_add, ZMod.natCast_self,
        Nat.cast_one]
      ring
    rw [this, hgr, sub_self]
  have := evalT_mulT hr v (g.1, (g.2.1 + p - 1) % p, g.2.2)
  rw [hv, hh, mul_zero] at this
  simp only [evalT, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] at this
  exact one_ne_zero this

/-- **Certificate in short-Weierstrass form.** With `A + a ≡ 0` and `B + b ≡ 0 (mod p)` checked
on `ℕ`, a valid certificate shows `x³ + a x + b ≠ 0` for every `x : ZMod p`. -/
theorem cubic_ne_zero_of_cert (p A B n : ℕ) [Fact p.Prime] (a b : ℕ)
    (hA : (A + a) % p = 0) (hB : (B + b) % p = 0) (hn : p < 2 ^ n) (g v : Tri)
    (hg : powT p A B n (0, 1, 0) p = g)
    (hv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0)) :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 := by
  intro x hx
  have hA' : (A : ZMod p) + a = 0 := by
    rw [← Nat.cast_add, ← ZMod.natCast_mod, hA, Nat.cast_zero]
  have hB' : (B : ZMod p) + b = 0 := by
    rw [← Nat.cast_add, ← ZMod.natCast_mod, hB, Nat.cast_zero]
  exact noRoot_of_cert p A B n hn g v hg hv x (by linear_combination hx - x * hA' - hB')

/-- **Exact count from a no-root fact over `ZMod p`.** For `p` an odd prime, a curve
`y² = x³ + a x + b` over `ZMod p` with `[W.IsElliptic]` (Δ ≠ 0) whose cubic has no root, and a
point of additive order `n` with `2p + 1 < 3n`, the curve has exactly `n` points. A
specialization of `natCard_point_eq_of_addOrderOf`. -/
theorem natCard_point_eq_of_noRoot {p a b n : ℕ} [Fact p.Prime]
    (hcubic : ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0) (hp2 : p ≠ 2)
    (hlt : 2 * p + 1 < 3 * n) (W : WeierstrassCurve (ZMod p)) [W.IsElliptic]
    (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = (a : ZMod p))
    (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point} (hG : addOrderOf G = n) :
    Nat.card W.toAffine.Point = n := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
  refine natCard_point_eq_of_addOrderOf W h₁ h₃ h2 ?_ hG (by rw [ZMod.card]; exact hlt)
  intro x hx
  apply hcubic x
  rw [h₂, h₄, h₆] at hx
  linear_combination hx

-- BEGIN GENERATED: scripts/certs/cubic_no_root_certs.py

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

/-- Certificate data: `A = −a mod p`. -/
def A : ℕ := 0

/-- Certificate data: `B = −b mod p`. -/
def B : ℕ := 115792089237316195423570985008687907853269984665640564039457584007908834671656

/-- Certificate data: `g = X^p mod (X³ − A X − B)`. -/
def g : Tri := (0,
  55594575648329892869085402983802832744385952214688224221778511981742606582254,
  0)

/-- Certificate data: the inverse of `g − X` modulo `X³ − A X − B`. -/
def v : Tri := (0,
  0,
  46758632835564736012269203954919337884311706168562511263687580192619680188360)

/-- Kernel check: `X^p ≡ g (mod X³ − A X − B)`. -/
theorem xpow : powT p A B 256 (0, 1, 0) p = g := by decide +kernel

/-- Kernel check: `v · (g − X) ≡ 1 (mod X³ − A X − B)`. -/
theorem inv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0) := by
  decide +kernel

/-- **`x³ + a x + b` has no root in `𝔽_p`** for secp256k1. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 :=
  cubic_ne_zero_of_cert p A B 256 a b (by decide +kernel) (by decide +kernel)
    (by decide +kernel) g v xpow inv

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by decide +kernel

/-- **Conditional exact count** for secp256k1: assuming `[Fact p.Prime]`, for a curve
`y² = x³ + a x + b` over `𝔽_p` with `[W.IsElliptic]` (Δ ≠ 0), any point of additive order
`n` forces `#E(𝔽_p) = n`. Nonsingularity and the order of a point are hypotheses here,
not proved facts. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n :=
  natCard_point_eq_of_noRoot cubic_ne_zero (by decide +kernel) two_mul_add_one_lt_three_mul
    W h₁ h₂ h₃ h₄ h₆ hG

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

/-- Certificate data: `A = −a mod p`. -/
def A : ℕ := 3

/-- Certificate data: `B = −b mod p`. -/
def B : ℕ := 3821946189377736946095495508010214631314800642229133723214

/-- Certificate data: `g = X^p mod (X³ − A X − B)`. -/
def g : Tri := (897772426216857905740464718317648918394375021027244704353,
  6216008227648530967744815138875139188844756526337129907353,
  2689664654584911429047662352445008748844766839681540128463)

/-- Certificate data: the inverse of `g − X` modulo `X³ − A X − B`. -/
def v : Tri := (3076984081099336410538445874700673783096882824010410041625,
  4871298686935519674170250204910228760438566091784467946767,
  105597762148406811168096478311383789005400348177979944870)

/-- Kernel check: `X^p ≡ g (mod X³ − A X − B)`. -/
theorem xpow : powT p A B 192 (0, 1, 0) p = g := by decide +kernel

/-- Kernel check: `v · (g − X) ≡ 1 (mod X³ − A X − B)`. -/
theorem inv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0) := by
  decide +kernel

/-- **`x³ + a x + b` has no root in `𝔽_p`** for NIST P-192. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 :=
  cubic_ne_zero_of_cert p A B 192 a b (by decide +kernel) (by decide +kernel)
    (by decide +kernel) g v xpow inv

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by decide +kernel

/-- **Conditional exact count** for NIST P-192: assuming `[Fact p.Prime]`, for a curve
`y² = x³ + a x + b` over `𝔽_p` with `[W.IsElliptic]` (Δ ≠ 0), any point of additive order
`n` forces `#E(𝔽_p) = n`. Nonsingularity and the order of a point are hypotheses here,
not proved facts. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n :=
  natCard_point_eq_of_noRoot cubic_ne_zero (by decide +kernel) two_mul_add_one_lt_three_mul
    W h₁ h₂ h₃ h₄ h₆ hG

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

/-- Certificate data: `A = −a mod p`. -/
def A : ℕ := 3

/-- Certificate data: `B = −b mod p`. -/
def B : ℕ := 8001660381584031794258346542525704258053235291346987067722831626317

/-- Certificate data: `g = X^p mod (X³ − A X − B)`. -/
def g : Tri := (13007951209251912699848910225737052564727108533249858001778075138108,
  6736638939299569244310158594083072418848545257754494280867682426394,
  20455971062524683444742559974151104391194361993401379142621028729827)

/-- Certificate data: the inverse of `g − X` modulo `X³ − A X − B`. -/
def v : Tri := (1261710631285627074303005901530361786216288604486499842249704943048,
  4447412785031720342771701563499662000791675740805516550464163634437,
  9439789507511725786058244597052783711805086828869674293526675889612)

/-- Kernel check: `X^p ≡ g (mod X³ − A X − B)`. -/
theorem xpow : powT p A B 224 (0, 1, 0) p = g := by decide +kernel

/-- Kernel check: `v · (g − X) ≡ 1 (mod X³ − A X − B)`. -/
theorem inv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0) := by
  decide +kernel

/-- **`x³ + a x + b` has no root in `𝔽_p`** for NIST P-224. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 :=
  cubic_ne_zero_of_cert p A B 224 a b (by decide +kernel) (by decide +kernel)
    (by decide +kernel) g v xpow inv

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by decide +kernel

/-- **Conditional exact count** for NIST P-224: assuming `[Fact p.Prime]`, for a curve
`y² = x³ + a x + b` over `𝔽_p` with `[W.IsElliptic]` (Δ ≠ 0), any point of additive order
`n` forces `#E(𝔽_p) = n`. Nonsingularity and the order of a point are hypotheses here,
not proved facts. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n :=
  natCard_point_eq_of_noRoot cubic_ne_zero (by decide +kernel) two_mul_add_one_lt_three_mul
    W h₁ h₂ h₃ h₄ h₆ hG

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

/-- Certificate data: `A = −a mod p`. -/
def A : ℕ := 3

/-- Certificate data: `B = −b mod p`. -/
def B : ℕ := 74733725485204106633371317169360305120971702399296588640698374994827630452660

/-- Certificate data: `g = X^p mod (X³ − A X − B)`. -/
def g : Tri := (66434390973925144466073271287821796038003695194169110494110089305650096453661,
  12402202686218762177567235911775779164004716598278868847786114277539554646092,
  24678849118215552148312087830792888746041224110560601850711771001608500700145)

/-- Certificate data: the inverse of `g − X` modulo `X³ − A X − B`. -/
def v : Tri := (76626890310466861426869089647039036757962535851890885406097439786770458211455,
  74462945259064871768191128030512052509059297803194871526163573358218695456204,
  34768139465301476436978405170953382516735956999154666452188405812258086013549)

/-- Kernel check: `X^p ≡ g (mod X³ − A X − B)`. -/
theorem xpow : powT p A B 256 (0, 1, 0) p = g := by decide +kernel

/-- Kernel check: `v · (g − X) ≡ 1 (mod X³ − A X − B)`. -/
theorem inv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0) := by
  decide +kernel

/-- **`x³ + a x + b` has no root in `𝔽_p`** for NIST P-256. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 :=
  cubic_ne_zero_of_cert p A B 256 a b (by decide +kernel) (by decide +kernel)
    (by decide +kernel) g v xpow inv

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by decide +kernel

/-- **Conditional exact count** for NIST P-256: assuming `[Fact p.Prime]`, for a curve
`y² = x³ + a x + b` over `𝔽_p` with `[W.IsElliptic]` (Δ ≠ 0), any point of additive order
`n` forces `#E(𝔽_p) = n`. Nonsingularity and the order of a point are hypotheses here,
not proved facts. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n :=
  natCard_point_eq_of_noRoot cubic_ne_zero (by decide +kernel) two_mul_add_one_lt_three_mul
    W h₁ h₂ h₃ h₄ h₆ hG

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

/-- Certificate data: `A = −a mod p`. -/
def A : ℕ := 3

/-- Certificate data: `B = −b mod p`. -/
def B : ℕ := 11821812636434773334430028259754565712022833414103878146519586102257032530187009463911005323375192894096167211881744

/-- Certificate data: `g = X^p mod (X³ − A X − B)`. -/
def g : Tri := (8300902441410358810024883245706595788071887638472987429650051756787010122663664392654234716054658334410824607717835,
  36451842499335230207230939190122359435795929611070366073564430331459357452117665764765104949638877581977396150453386,
  15550551877492060201127078427218509008503925815996229619149120823729355824416602968196515686102139833725391182697242)

/-- Certificate data: the inverse of `g − X` modulo `X³ − A X − B`. -/
def v : Tri := (23037766613497683937702734290281044719364893268180251583910224888989381657771069200037813904257325918671976092329602,
  8235438212423615602427778915669574859600037698862346933589434399495169446996583974901273360826717582835190849638831,
  12157362177932134139146813183752135342286725243554133716818896354380897714709611791313184492360272402950851405460538)

/-- Kernel check: `X^p ≡ g (mod X³ − A X − B)`. -/
theorem xpow : powT p A B 384 (0, 1, 0) p = g := by decide +kernel

/-- Kernel check: `v · (g − X) ≡ 1 (mod X³ − A X − B)`. -/
theorem inv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0) := by
  decide +kernel

/-- **`x³ + a x + b` has no root in `𝔽_p`** for NIST P-384. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 :=
  cubic_ne_zero_of_cert p A B 384 a b (by decide +kernel) (by decide +kernel)
    (by decide +kernel) g v xpow inv

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by decide +kernel

/-- **Conditional exact count** for NIST P-384: assuming `[Fact p.Prime]`, for a curve
`y² = x³ + a x + b` over `𝔽_p` with `[W.IsElliptic]` (Δ ≠ 0), any point of additive order
`n` forces `#E(𝔽_p) = n`. Nonsingularity and the order of a point are hypotheses here,
not proved facts. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n :=
  natCard_point_eq_of_noRoot cubic_ne_zero (by decide +kernel) two_mul_add_one_lt_three_mul
    W h₁ h₂ h₃ h₄ h₆ hG

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

/-- Certificate data: `A = −a mod p`. -/
def A : ℕ := 3

/-- Certificate data: `B = −b mod p`. -/
def B : ℕ := 5770948622056875440470788408314587647333227701191621660399877064689590067246921036108850903087694931728704179094774544727683535468125630900431700802636071167

/-- Certificate data: `g = X^p mod (X³ − A X − B)`. -/
def g : Tri := (4860891086045056853561103990765776437896461732719963324290057395732751086103788161954116339572232800690457337429123819664279834135875092463554593205804047047,
  5623913033336113422386236864006719062755991763864609197545100619433248161746017032673051834216465799515469811516542321474225029959858163827729884161696537584,
  1001953287042776430710398404157808389686486783711671042552203031726396048646933945084221650544610877143419486981178519186421076931920775674509717542655505052)

/-- Certificate data: the inverse of `g − X` modulo `X³ − A X − B`. -/
def v : Tri := (5556850081864827842302249485475501585472702946772625307642304195702912034363837867267334216347521692509406916620096684956176894315447091116492501000392161958,
  2592645775458497527836362227091103884154287512470494672274301275565663408730650270660448980645397363205839490313252565391972848223674401530161387302727484004,
  3919380404691066388712376322317341026252002696138380915147944189379687824774581460974855590730258562532022938584569429027963361353339635641909491533809725330)

/-- Kernel check: `X^p ≡ g (mod X³ − A X − B)`. -/
theorem xpow : powT p A B 521 (0, 1, 0) p = g := by decide +kernel

/-- Kernel check: `v · (g − X) ≡ 1 (mod X³ − A X − B)`. -/
theorem inv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0) := by
  decide +kernel

/-- **`x³ + a x + b` has no root in `𝔽_p`** for NIST P-521. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 :=
  cubic_ne_zero_of_cert p A B 521 a b (by decide +kernel) (by decide +kernel)
    (by decide +kernel) g v xpow inv

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by decide +kernel

/-- **Conditional exact count** for NIST P-521: assuming `[Fact p.Prime]`, for a curve
`y² = x³ + a x + b` over `𝔽_p` with `[W.IsElliptic]` (Δ ≠ 0), any point of additive order
`n` forces `#E(𝔽_p) = n`. Nonsingularity and the order of a point are hypotheses here,
not proved facts. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n :=
  natCard_point_eq_of_noRoot cubic_ne_zero (by decide +kernel) two_mul_add_one_lt_three_mul
    W h₁ h₂ h₃ h₄ h₆ hG

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

/-- Certificate data: `A = −a mod p`. -/
def A : ℕ := 20186768791719234177182518232823303015917335661467841094348773256267632057758

/-- Certificate data: `B = −b mod p`. -/
def B : ℕ := 59307723899723505379734048839207128830087524142019970636688749144398190758849

/-- Certificate data: `g = X^p mod (X³ − A X − B)`. -/
def g : Tri := (6934312191461072874148100761682709823469295718683001920214272321718106639743,
  74730866787797357883289511930108312968771754820441431075655545456776372037232,
  24103594246436844333297699615940947720531226414641076004148624174016432703105)

/-- Certificate data: the inverse of `g − X` modulo `X³ − A X − B`. -/
def v : Tri := (5347744486777530706669047377084680431416082047222058099865314757079289018413,
  36567706687211352878623830248023275230139348886519930341788893933933071887964,
  57300115342307814829368171194017451425362166738975514114819334576929185469628)

/-- Kernel check: `X^p ≡ g (mod X³ − A X − B)`. -/
theorem xpow : powT p A B 256 (0, 1, 0) p = g := by decide +kernel

/-- Kernel check: `v · (g − X) ≡ 1 (mod X³ − A X − B)`. -/
theorem inv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0) := by
  decide +kernel

/-- **`x³ + a x + b` has no root in `𝔽_p`** for brainpoolP256r1. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 :=
  cubic_ne_zero_of_cert p A B 256 a b (by decide +kernel) (by decide +kernel)
    (by decide +kernel) g v xpow inv

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by decide +kernel

/-- **Conditional exact count** for brainpoolP256r1: assuming `[Fact p.Prime]`, for a curve
`y² = x³ + a x + b` over `𝔽_p` with `[W.IsElliptic]` (Δ ≠ 0), any point of additive order
`n` forces `#E(𝔽_p) = n`. Nonsingularity and the order of a point are hypotheses here,
not proved facts. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n :=
  natCard_point_eq_of_noRoot cubic_ne_zero (by decide +kernel) two_mul_add_one_lt_three_mul
    W h₁ h₂ h₃ h₄ h₆ hG

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

/-- Certificate data: `A = −a mod p`. -/
def A : ℕ := 2610291730521071877789955317311056531572656531832425707992085991374752909090535788598219135866672173564987199570989

/-- Certificate data: `B = −b mod p`. -/
def B : ℕ := 20942138915226687079740064800278915318369473570620200579237210552582040317534372214534105522044775205974636771123266

/-- Certificate data: `g = X^p mod (X³ − A X − B)`. -/
def g : Tri := (15298734606309199264420805533508030890414563944865334671512276287980469130952691092095033434054904617589085651229424,
  11068186017202743673118810097581550772766737817903064248079785514094454210086250096998177788174923242769800729139125,
  5443622384506312450156513124064629656210090739227743791001374481785671329407903472242873611627734644954640700142187)

/-- Certificate data: the inverse of `g − X` modulo `X³ − A X − B`. -/
def v : Tri := (18045346159989301294719205289786962596468003789292587159741834949006371209014629163014746348076599162029150578683262,
  1976113098210081074617925902571799281931794102930411075466637102904693541261693854282593756972459711385728480861278,
  4643256948357306801182104578797069499791313285794868896678261438458615860465573791712519540292328347437871877550575)

/-- Kernel check: `X^p ≡ g (mod X³ − A X − B)`. -/
theorem xpow : powT p A B 384 (0, 1, 0) p = g := by decide +kernel

/-- Kernel check: `v · (g − X) ≡ 1 (mod X³ − A X − B)`. -/
theorem inv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0) := by
  decide +kernel

/-- **`x³ + a x + b` has no root in `𝔽_p`** for brainpoolP384r1. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 :=
  cubic_ne_zero_of_cert p A B 384 a b (by decide +kernel) (by decide +kernel)
    (by decide +kernel) g v xpow inv

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by decide +kernel

/-- **Conditional exact count** for brainpoolP384r1: assuming `[Fact p.Prime]`, for a curve
`y² = x³ + a x + b` over `𝔽_p` with `[W.IsElliptic]` (Δ ≠ 0), any point of additive order
`n` forces `#E(𝔽_p) = n`. Nonsingularity and the order of a point are hypotheses here,
not proved facts. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n :=
  natCard_point_eq_of_noRoot cubic_ne_zero (by decide +kernel) two_mul_add_one_lt_three_mul
    W h₁ h₂ h₃ h₄ h₆ hG

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

/-- Certificate data: `A = −a mod p`. -/
def A : ℕ := 2654101649677169323990181508682774098087893873475608284207686741749755096132276341889943335783972980074294676707863468103742060282484210298004808763552809

/-- Certificate data: `B = −b mod p`. -/
def B : ℕ := 5703173199321265492381753230817075505630700634460852593016273518463877833830288943454409175703674331205645756879453574140199082811088933301729003745530320

/-- Certificate data: `g = X^p mod (X³ − A X − B)`. -/
def g : Tri := (1171207495004172184870350888846736138287303023485176906012618281211713437683792754554487831602135902082002900222626154888623984832190465825804542440156758,
  8084232344484297400096973808713771151807802980077000277155885356866384898318055411291502310474576666020856034767232292921921200356795942821699510525638530,
  8946525268153297803678489203520925023466257242991388711508304401945186994333131060379100434708771280975428123247921998263945934840348532173621471775822375)

/-- Certificate data: the inverse of `g − X` modulo `X³ − A X − B`. -/
def v : Tri := (1803314254406975735450288165685996255159518649509801042516748854645051387409671406770237299640480790704019033082794117735071555073817603589011800439246700,
  5423510712171489546644718125848465800445423157029586731376840833885116518002476487579816819625716701205282987784671943974892074197635932083426899437475869,
  1980640283309979095730852824049519563548238190526698414050554203846063330593484879663419473345296546803597274808794758955751942903882298593095810355797106)

/-- Kernel check: `X^p ≡ g (mod X³ − A X − B)`. -/
theorem xpow : powT p A B 512 (0, 1, 0) p = g := by decide +kernel

/-- Kernel check: `v · (g − X) ≡ 1 (mod X³ − A X − B)`. -/
theorem inv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0) := by
  decide +kernel

/-- **`x³ + a x + b` has no root in `𝔽_p`** for brainpoolP512r1. -/
theorem cubic_ne_zero [Fact p.Prime] :
    ∀ x : ZMod p, x ^ 3 + (a : ZMod p) * x + (b : ZMod p) ≠ 0 :=
  cubic_ne_zero_of_cert p A B 512 a b (by decide +kernel) (by decide +kernel)
    (by decide +kernel) g v xpow inv

/-- `2p + 1 < 3n`, the size condition of the exact-count theorem. -/
theorem two_mul_add_one_lt_three_mul : 2 * p + 1 < 3 * n := by decide +kernel

/-- **Conditional exact count** for brainpoolP512r1: assuming `[Fact p.Prime]`, for a curve
`y² = x³ + a x + b` over `𝔽_p` with `[W.IsElliptic]` (Δ ≠ 0), any point of additive order
`n` forces `#E(𝔽_p) = n`. Nonsingularity and the order of a point are hypotheses here,
not proved facts. -/
theorem card_eq_of_addOrderOf [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = (a : ZMod p)) (h₆ : W.a₆ = (b : ZMod p)) {G : W.toAffine.Point}
    (hG : addOrderOf G = n) : Nat.card W.toAffine.Point = n :=
  natCard_point_eq_of_noRoot cubic_ne_zero (by decide +kernel) two_mul_add_one_lt_three_mul
    W h₁ h₂ h₃ h₄ h₆ hG

end brainpoolP512r1

-- END GENERATED: scripts/certs/cubic_no_root_certs.py

end Ecdlp.CubicCert
