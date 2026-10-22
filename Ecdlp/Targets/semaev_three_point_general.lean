import Mathlib
import Ecdlp.Proved.SemaevThree

/-!
# OPEN TARGET — Semaev `S₃` on Mathlib's group law for a general short Weierstrass curve

Frozen statements for the point-level layer of `Ecdlp/Proved/SemaevThree.lean`, recorded
before any proof search.

**What the base already proves.** `SemaevThree.lean` proves, for `y² = x³ + a·x + b` over a
field, the coordinate-level forward direction (`S₃_eq_zero_of_chord`, `S₃_eq_zero_of_tangent`),
the coordinate-level reverse direction (`S₃_root_of_eq_zero`) and their combination
`S₃_eq_zero_iff` (under `x₁ ≠ x₂`). On Mathlib's point group it proves only the forward
direction, only for secp256k1, and in two cases with case hypotheses:
`secp256k1_semaev_three_point` (`x₁ ≠ x₂`) and `secp256k1_semaev_three_point_double`
(`P₁ = P₂`, not 2-torsion). `Ecdlp/Proved/PointDecomposition.lean` restates these two cases
in decomposition form (`secp256k1_point_decomposition_semaev`,
`secp256k1_point_decomposition_semaev_double`: `R = P₁ + P₂ ⇒ S₃(x₁, x₂, x(R)) = 0`).

**What this target states.** For a curve `W` in short normal form (`[W.IsShortNF]`, i.e.
`a₁ = a₂ = a₃ = 0`; `a = W.a₄` and `b = W.a₆` arbitrary) over any field `K`, with points in
Mathlib's `WeierstrassCurve.Affine.Point` group:

* `S₃_eq_addSubMap` (over any commutative ring): `S₃(x₁,x₂,X) = f₂·X² − f₁·X + f₀`, where
  `(f₀, f₁, f₂)` are the components of Mathlib's `WeierstrassCurve.addSubMap` evaluated at
  `(x₁·x₂, x₁+x₂, 1)`.
* `S₃_eq_zero_of_add_add_eq_zero`: three affine points with `P₁ + P₂ + P₃ = 0` give
  `S₃(x₁,x₂,x₃) = 0`, with no `x₁ ≠ x₂` and no non-2-torsion hypothesis.
* `S₃_eq_zero_iff_exists_point`: for fixed affine `P₁, P₂` and any `x₃ : K`,
  `S₃(x₁,x₂,x₃) = 0` iff some affine point `P₃` with `x`-coordinate `x₃` satisfies
  `P₁ + P₂ + P₃ = 0` or `P₁ − P₂ + P₃ = 0`.
* `S₃_eq_zero_iff_signed_sum`: for three fixed affine points, `S₃(x₁,x₂,x₃) = 0` iff
  `P₁ ± P₂ ± P₃ = 0` for some choice of signs.
* `secp256k1_semaev_three_point_iff`: the signed-sum statement for `secp256k1`.

The only hypotheses on the curve are the class `W.IsShortNF` and the nonsingularity of the
given points; there is no hypothesis on the discriminant, on `W.IsElliptic` or on the
characteristic. `[DecidableEq K]` is required by Mathlib's addition on `W.toAffine.Point`.
Point-level statements for `S₄` or `Sₘ`, projective (`xRep`) forms, and fixed-target,
`HValue` or `frozenC` semantics are not part of this target.

**Related work in Mathlib.** The pinned Mathlib (`v4.31.0`, rev `fabf563a`) defines
`WeierstrassCurve.addSubMap`, documented as the map on coordinate vectors
`(x(P)·x(Q) : x(P)+x(Q) : 1) ↦ (x(P+Q)·x(P−Q) : x(P+Q)+x(P−Q) : 1)`, with a TODO to show that
it does so. Mathlib PR #43292 (commit `69fe4f49`, included from tag `v4.34.0` on, not available at
this pin) proves `WeierstrassCurve.Affine.Point.sym2x_add_sub_eq_addSubMap_sym2x`: for any
Weierstrass curve over a field, `sym2x (P + Q) (P − Q)` equals `addSubMap W` applied to
`sym2x P Q` up to a nonzero scalar. Read through `S₃_eq_addSubMap`, that theorem places
`x(P₁+P₂)` and `x(P₁−P₂)` as the roots of `S₃(x₁,x₂,·)` (projectively; one root is at
infinity when `P₁ = ±P₂`), which overlaps `S₃_eq_zero_iff_exists_point`. This target does
not move the Mathlib pin.

**Related work in this repository, not on `main`.** Open draft PR #345
(`agent/ecdlp-m16-kummer-local-fiber`, in the stacked M16 chain #343–#355) proves, for
secp256k1 base-changed to the chosen algebraic closure of `𝔽_p`, the projective local fiber
`HValue_barKummer_zero_iff`: `HValue(κ(P), κ(Q), W) = 0` iff `W` normalizes to `κ(P+Q)` or
`κ(P−Q)`, where `κ` is the Kummer coordinate. With `HValue_affine_eq_S₃` from the same chain,
its affine case corresponds to the secp256k1 instance over `𝔽̄_p` of
`S₃_eq_zero_iff_exists_point`. This target is stated over the base field, for every curve
in short normal form, in affine form on Mathlib's points, and adds no `HValue` or `frozenC`
semantics.

This stem is **not imported and not built**; every `sorry` below is an open obligation.
-/

namespace Ecdlp.Semaev

open WeierstrassCurve

/-- **`S₃` through Mathlib's `addSubMap`.** For a Weierstrass curve `W` in short normal form
over a commutative ring, `S₃(x₁,x₂,x₃) = f₂·x₃² − f₁·x₃ + f₀`, where `(f₀, f₁, f₂)` is
`W.addSubMap` evaluated at `(x₁·x₂, x₁+x₂, 1)`. -/
theorem S₃_eq_addSubMap {F : Type*} [CommRing F] (W : WeierstrassCurve F) [W.IsShortNF]
    (x₁ x₂ x₃ : F) :
    S₃ W.a₄ W.a₆ x₁ x₂ x₃ =
      (W.addSubMap 2).eval ![x₁ * x₂, x₁ + x₂, 1] * x₃ ^ 2
        - (W.addSubMap 1).eval ![x₁ * x₂, x₁ + x₂, 1] * x₃
        + (W.addSubMap 0).eval ![x₁ * x₂, x₁ + x₂, 1] := by
  sorry

variable {K : Type*} [Field K] [DecidableEq K]

open WeierstrassCurve.Affine in
/-- **Forward direction of `S₃` on the point group of a short Weierstrass curve.** If three
affine points of `W` (short normal form, over a field) satisfy `P₁ + P₂ + P₃ = 0`, then
`S₃(x₁,x₂,x₃) = 0`. There is no `x₁ ≠ x₂` and no non-2-torsion hypothesis. -/
theorem S₃_eq_zero_of_add_add_eq_zero (W : WeierstrassCurve K) [W.IsShortNF]
    {x₁ y₁ x₂ y₂ x₃ y₃ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (h₃ : W.toAffine.Nonsingular x₃ y₃)
    (hsum : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ + Point.some x₃ y₃ h₃ = 0) :
    S₃ W.a₄ W.a₆ x₁ x₂ x₃ = 0 := by
  sorry

open WeierstrassCurve.Affine in
/-- **`S₃` on the point group: a zero in the third variable is the `x`-coordinate of a point
completing `P₁ ± P₂` to zero.** For fixed affine points `P₁, P₂` of `W` (short normal form,
over a field) and any `x₃ : K`: `S₃(x₁,x₂,x₃) = 0` iff there is an affine point
`P₃ = (x₃, y₃)` of `W` with `P₁ + P₂ + P₃ = 0` or `P₁ − P₂ + P₃ = 0`. -/
theorem S₃_eq_zero_iff_exists_point (W : WeierstrassCurve K) [W.IsShortNF]
    {x₁ y₁ x₂ y₂ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂) (x₃ : K) :
    S₃ W.a₄ W.a₆ x₁ x₂ x₃ = 0 ↔
      ∃ (y₃ : K) (h₃ : W.toAffine.Nonsingular x₃ y₃),
        Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ + Point.some x₃ y₃ h₃ = 0 ∨
        Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ + Point.some x₃ y₃ h₃ = 0 := by
  sorry

open WeierstrassCurve.Affine in
/-- **`S₃` on the point group: the signed-sum characterization.** For three affine points
`P₁, P₂, P₃` of `W` (short normal form, over a field): `S₃(x₁,x₂,x₃) = 0` iff
`P₁ + ε₂•P₂ + ε₃•P₃ = 0` for some signs `ε₂, ε₃ ∈ {1, −1}`. -/
theorem S₃_eq_zero_iff_signed_sum (W : WeierstrassCurve K) [W.IsShortNF]
    {x₁ y₁ x₂ y₂ x₃ y₃ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (h₃ : W.toAffine.Nonsingular x₃ y₃) :
    S₃ W.a₄ W.a₆ x₁ x₂ x₃ = 0 ↔
      ∃ ε₂ ε₃ : ℤˣ, Point.some x₁ y₁ h₁ + (ε₂ : ℤ) • Point.some x₂ y₂ h₂
        + (ε₃ : ℤ) • Point.some x₃ y₃ h₃ = 0 := by
  sorry

open Ecdlp.Curve

variable [Fact (Nat.Prime Secp256k1.p)]

open WeierstrassCurve.Affine in
/-- **`S₃` on secp256k1 points: the signed-sum characterization.** Specialization of
`S₃_eq_zero_iff_signed_sum` to `secp256k1` (`a = 0`, `b = 7`): for three affine points of
`secp256k1.toAffine.Point`, `S₃(x₁,x₂,x₃) = 0` iff `P₁ ± P₂ ± P₃ = 0` for some choice of
signs. -/
theorem secp256k1_semaev_three_point_iff
    {x₁ y₁ x₂ y₂ x₃ y₃ : ZMod Secp256k1.p}
    (h₁ : secp256k1.toAffine.Nonsingular x₁ y₁)
    (h₂ : secp256k1.toAffine.Nonsingular x₂ y₂)
    (h₃ : secp256k1.toAffine.Nonsingular x₃ y₃) :
    S₃ (0 : ZMod Secp256k1.p) 7 x₁ x₂ x₃ = 0 ↔
      ∃ ε₂ ε₃ : ℤˣ, Point.some x₁ y₁ h₁ + (ε₂ : ℤ) • Point.some x₂ y₂ h₂
        + (ε₃ : ℤ) • Point.some x₃ y₃ h₃ = 0 := by
  sorry

end Ecdlp.Semaev
