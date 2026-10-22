import Mathlib
import Ecdlp.Proved.Secp256k1Curve
import Ecdlp.Proved.DivisionPolynomial

/-!
# The point-level 2-torsion characterization for secp256k1 (both directions)

`TwoTorsion.lean` proved the *forward, `x`-coordinate* half of the classical criterion
`ψₙ(x_P) = 0 ⟺ [n]P = O`: an order-2 `x`-coordinate is a root of `Ψ₂Sq`. Here we prove
the **full, both-directions criterion at the level of points, for `n = 2`**:

  `2 • P = 0  ⟺  P.y = 0`   for an affine point `P = (x, y)` of secp256k1.

This is exactly the bridge `ψ₂ ↔ E[2]` that Mathlib's division-polynomial file records only
as a keyword/TODO (Mathlib supplies the polynomials `ψₙ` and their degrees, but **not** the
theorem tying them to actual torsion points). Its content: a nonzero affine point has order
dividing 2 iff it is fixed by negation, and for secp256k1 (`a₁ = a₃ = 0`, so `-（x,y) =
(x,-y)`) that means `y = -y`, i.e. `2y = 0`, i.e. `y = 0` (char `≠ 2`). Combined with the
curve equation this says the affine 2-torsion is exactly `{(x, 0) : x³ + 7 = 0}` — the
roots of `Ψ₂Sq = 4(X³+7)`. Needs the machine-checked primality of `p` (for the point group
and `2 ≠ 0`); no other axioms.
-/

namespace Ecdlp.Curve

open WeierstrassCurve.Affine

variable [Fact (Nat.Prime Secp256k1.p)]

/-- **Point-level 2-torsion criterion: `2 • P = 0 ⟺ y = 0`.** An affine point `P = (x, y)`
of secp256k1 has order dividing 2 iff its `Y`-coordinate vanishes — the both-directions
`ψ₂ ↔ E[2]` bridge (`n = 2`) that upgrades the forward-only `secp256k1_Ψ₂Sq_root_of_two_torsion`.
`2 • P = 0 ⟺ P = -P` (`add_eq_zero_iff_eq_neg`), and `-（x,y) = (x,-y)` for secp256k1, so the
condition is `y = -y`, i.e. `y = 0` in characteristic `≠ 2`. -/
theorem secp256k1_two_nsmul_eq_zero_iff
    (x y : ZMod Secp256k1.p) (h : secp256k1.toAffine.Nonsingular x y) :
    (2 : ℕ) • (Point.some x y h) = 0 ↔ y = 0 := by
  have h2ne : (2 : ZMod Secp256k1.p) ≠ 0 := by
    have h2 : ((2 : ℕ) : ZMod Secp256k1.p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; decide +kernel
    simpa using h2
  have hnegY : secp256k1.toAffine.negY x y = -y := by
    simp [WeierstrassCurve.Affine.negY, secp256k1]
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq, hnegY]
  constructor
  · rintro ⟨-, hy⟩
    have h2y : (2 : ZMod Secp256k1.p) * y = 0 := by linear_combination hy
    rcases mul_eq_zero.mp h2y with h2 | hy0
    · exact absurd h2 h2ne
    · exact hy0
  · intro hy
    subst hy
    exact ⟨rfl, by ring⟩

end Ecdlp.Curve
