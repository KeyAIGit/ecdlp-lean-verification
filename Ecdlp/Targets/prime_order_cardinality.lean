import Mathlib
import Ecdlp.Proved.AffinePointFinite

/-!
# OPEN TARGET (frozen statements): exact point count `#E(𝔽) = n` from a point of order `n` with `2·#𝔽 + 1 < 3n`

A curve-generic form of the argument behind `secp256k1_card_point_eq_n`
(`CurveCardinalityExact.lean`). It avoids the Hasse bound and Schoof's algorithm.

Let `W` be a Weierstrass curve over a finite field `F` with `a₁ = a₃ = 0` and `2 ≠ 0` in `F`.
Suppose the cubic `x³ + a₂x² + a₄x + a₆` has no root in `F`, and some point `G` has
`addOrderOf G = n` with `2·#F + 1 < 3n`. Then `#W(F) = n`.

This file is an **open stem** (statements frozen before proof; each proof is `sorry`).
It is not imported by `Ecdlp.lean`, not built, and excluded from the no-`sorry` gate. The
proof is intended to land in `Ecdlp/Proved/PrimeOrderCardinality.lean`, which consumes this stem.

## Route

1. **`n ∣ #E`**: Lagrange (`addOrderOf_dvd_natCard`).
2. **`#E ≤ 2·#F + 1`** (`natCard_point_le`): for every `x` the affine points `(x, y)` have
   `y` among the at most two roots of the monic quadratic
   `Y² + (a₁x + a₃)Y − (x³ + a₂x² + a₄x + a₆)`. Summing over `x` and adding the point at
   infinity gives the bound. This holds for every Weierstrass curve over a finite field.
3. **No nonzero 2-torsion** (`exists_cubic_root_of_two_nsmul_eq_zero`): when `a₁ = a₃ = 0`
   and `2 ≠ 0`, a point `P ≠ 0` with `2 • P = 0` has `y = 0`, so its `x` is a root of the
   cubic. The no-root hypothesis excludes this.
4. **Group theory** (`natCard_eq_of_dvd_of_lt_three_mul`): if `n ∣ #A ≤ N < 3n` and `A` has
   no element of order 2, then `#A = n`. A multiple `kn` below `3n` has `k ∈ {1, 2}`, and
   `k = 2` would give an element of order 2 by additive Cauchy.

Neither `n` nor `#F` needs to be prime. The no-root hypothesis is discharged for concrete
curves by the kernel-checked certificate in `CubicNoRootCertificate.lean`.

## Scope

The bound `#E ≤ 2·#F + 1` leaves room for about `2h` multiples of `n` when `n ≈ #F / h`.
So this argument reaches cofactor-1 curves only; a curve with cofactor `h ≥ 2` needs the
Hasse bound, which Mathlib v4.31 does not provide.

## Provenance

The same argument (prime point order, `#E ≤ 2p + 1`, no rational 2-torsion) is formalized for
the specification curves of pyca/verified-garbage (`VG.Proof.Weierstrass.primeOrder_of`,
Apache-2.0 OR BSD-3-Clause; see `THIRD_PARTY_NOTICES.md`). The code here is written against
Mathlib's `WeierstrassCurve.Affine.Point` and reuses this repository's
`instFinitePoint`; it generalizes the secp256k1-specific steps of
`CurveCardinalityExact.lean`.
-/

namespace Ecdlp.Weierstrass

open Polynomial WeierstrassCurve.Affine

/-- **Group-theoretic core.** In a finite additive group `A` with no element of order 2, if
`n ∣ #A` and `#A ≤ N < 3n`, then `#A = n`. No primality of `n` is needed. -/
theorem natCard_eq_of_dvd_of_lt_three_mul {A : Type*} [AddGroup A] [Finite A]
    {n N : ℕ} (hdvd : n ∣ Nat.card A) (hle : Nat.card A ≤ N) (hlt : N < 3 * n)
    (h2 : ∀ Q : A, (2 : ℕ) • Q = 0 → Q = 0) : Nat.card A = n := by
  sorry

/-- **`#E(F) ≤ 2·#F + 1`** for every Weierstrass curve over a finite field. Each `x ∈ F`
carries at most two affine points, because their `y`-coordinates are roots of the monic
quadratic `Y² + (a₁x + a₃)Y − (x³ + a₂x² + a₄x + a₆)`. The `+ 1` is the point at infinity. -/
theorem natCard_point_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) :
    Nat.card W.Point ≤ 2 * Fintype.card F + 1 := by
  sorry

/-- **A nonzero 2-torsion point gives a root of the cubic.** On a Weierstrass curve with
`a₁ = a₃ = 0` over a field with `2 ≠ 0`, a point `P ≠ 0` with `2 • P = 0` is affine with
`y = 0`, so its `x`-coordinate solves `x³ + a₂x² + a₄x + a₆ = 0`. -/
theorem exists_cubic_root_of_two_nsmul_eq_zero {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (h2 : (2 : F) ≠ 0)
    {P : W.toAffine.Point} (hP : (2 : ℕ) • P = 0) (hP0 : P ≠ 0) :
    ∃ x : F, x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ = 0 := by
  sorry

/-- **Exact point count from a point of order `n`.** Let `W` have `a₁ = a₃ = 0` over a finite
field with `2 ≠ 0`, and suppose `x³ + a₂x² + a₄x + a₆` has no root. If some point has additive
order `n` and `2·#F + 1 < 3n`, then `#W(F) = n`. -/
theorem natCard_point_eq_of_addOrderOf {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (h2 : (2 : F) ≠ 0)
    (hcubic : ∀ x : F, x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ ≠ 0)
    {G : W.toAffine.Point} {n : ℕ} (hG : addOrderOf G = n)
    (hlt : 2 * Fintype.card F + 1 < 3 * n) :
    Nat.card W.toAffine.Point = n := by
  sorry

/-- **Prime-order form.** The same count when the input is a prime `n` with `n • G = 0` and
`G ≠ 0` (so `addOrderOf G = n`). -/
theorem card_eq_of_prime_order_point {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (h2 : (2 : F) ≠ 0)
    (hcubic : ∀ x : F, x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ ≠ 0)
    {n : ℕ} [Fact n.Prime] (G : W.toAffine.Point) (hGn : n • G = 0) (hG0 : G ≠ 0)
    (hlt : 2 * Fintype.card F + 1 < 3 * n) :
    Nat.card W.toAffine.Point = n := by
  sorry

end Ecdlp.Weierstrass
