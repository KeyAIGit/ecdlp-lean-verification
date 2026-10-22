import Mathlib
import Ecdlp.Proved.SemaevThree

/-!
# Semaev `S₃` on Mathlib's group law for a general short Weierstrass curve

Point-level layer of `Ecdlp/Proved/SemaevThree.lean`. The statements were frozen in
`Ecdlp/Targets/semaev_three_point_general.lean` before any proof search and are proved here
unchanged.

**What the base already proves.** `SemaevThree.lean` proves, for `y² = x³ + a·x + b` over a
field, the coordinate-level forward direction (`S₃_eq_zero_of_chord`, `S₃_eq_zero_of_tangent`),
the coordinate-level reverse direction (`S₃_root_of_eq_zero`) and their combination
`S₃_eq_zero_iff` (under `x₁ ≠ x₂`). On Mathlib's point group it proves only the forward
direction, only for secp256k1, and in two cases with case hypotheses:
`secp256k1_semaev_three_point` (`x₁ ≠ x₂`) and `secp256k1_semaev_three_point_double`
(`P₁ = P₂`, not 2-torsion). `Ecdlp/Proved/PointDecomposition.lean` restates these two cases
in decomposition form.

**What this file proves.** For a curve `W` in short normal form (`[W.IsShortNF]`, i.e.
`a₁ = a₂ = a₃ = 0`; `a = W.a₄` and `b = W.a₆` arbitrary) over any field `K`, with points in
Mathlib's `WeierstrassCurve.Affine.Point` group:

* `S₃_eq_addSubMap` (over any commutative ring): `S₃(x₁,x₂,X) = f₂·X² − f₁·X + f₀`, where
  `(f₀, f₁, f₂)` are the components of Mathlib's `WeierstrassCurve.addSubMap` evaluated at
  `(x₁·x₂, x₁+x₂, 1)`. This is a polynomial identity; it does not prove the property of
  `addSubMap` that Mathlib's TODO asks for.
* `S₃_eq_zero_of_add_add_eq_zero`: three affine points with `P₁ + P₂ + P₃ = 0` give
  `S₃(x₁,x₂,x₃) = 0`, with no `x₁ ≠ x₂` and no non-2-torsion hypothesis.
* `S₃_eq_zero_iff_exists_point`: for fixed affine `P₁, P₂` and any `x₃ : K`,
  `S₃(x₁,x₂,x₃) = 0` iff some affine point `P₃` with `x`-coordinate `x₃` satisfies
  `P₁ + P₂ + P₃ = 0` or `P₁ − P₂ + P₃ = 0`.
* `S₃_eq_zero_iff_signed_sum`: for three fixed affine points, `S₃(x₁,x₂,x₃) = 0` iff
  `P₁ ± P₂ ± P₃ = 0` for some choice of signs.
* `secp256k1_semaev_three_point_iff`: the signed-sum statement for `secp256k1`, through a
  local `IsShortNF` instance; primality of `p` stays a hypothesis.

The only hypotheses on the curve are the class `W.IsShortNF` and the nonsingularity of the
given points; there is no hypothesis on the discriminant, on `W.IsElliptic` or on the
characteristic. `[DecidableEq K]` is required by Mathlib's addition on `W.toAffine.Point`.
Point-level statements for `S₄` or `Sₘ`, projective (`xRep`) forms, and fixed-target,
`HValue` or `frozenC` semantics are not part of this file.

**Proof outline.** The single geometric step is the private lemma
`S₃_eq_zero_of_add_eq_some`: if `P₁ + P₂` is the affine point `(x, y)`, then
`S₃(x₁,x₂,x) = 0`. It unfolds Mathlib's chord and tangent formulas (`Point.add_of_X_ne`,
`Point.add_of_Y_ne`, `slope_of_X_ne`, `slope_of_Y_ne`) and applies `S₃_eq_zero_of_chord` or
`S₃_eq_zero_of_tangent`; the vertical case `P₂ = −P₁` cannot have an affine sum. The reverse
step (private `exists_add_or_sub_of_S₃_eq_zero`) uses `S₃_root_of_eq_zero` when `x₁ ≠ x₂`.
When `x₁ = x₂`, the curve equation gives `S₃(x₁,x₁,X) = (3x₁² + a)² − 4y₁²·(X + 2x₁)`. If
`2y₁ = 0` this is the constant `(3x₁² + a)²`, nonzero by nonsingularity, so `S₃ = 0` cannot
hold; otherwise its zero is `x(2P₁)`, and `P₁ + P₂` or `P₁ − P₂` equals `2P₁`.

**Related work in Mathlib.** The pinned Mathlib (`v4.31.0`, rev `fabf563a`) defines
`WeierstrassCurve.addSubMap`, documented as the map on coordinate vectors
`(x(P)·x(Q) : x(P)+x(Q) : 1) ↦ (x(P+Q)·x(P−Q) : x(P+Q)+x(P−Q) : 1)`, with a TODO to show that
it does so. Mathlib PR #43292 (commit `69fe4f49`, included from tag `v4.34.0` on, not available
at this pin) proves `WeierstrassCurve.Affine.Point.sym2x_add_sub_eq_addSubMap_sym2x`: for any
Weierstrass curve over a field, `sym2x (P + Q) (P − Q)` equals `addSubMap W` applied to
`sym2x P Q` up to a nonzero scalar. Read through `S₃_eq_addSubMap`, that theorem places
`x(P₁+P₂)` and `x(P₁−P₂)` as the roots of `S₃(x₁,x₂,·)` (projectively; one root is at infinity
when `P₁ = ±P₂`), which overlaps `S₃_eq_zero_iff_exists_point`. This file does not move the
Mathlib pin.

**Related work in this repository, not on `main`.** Open draft PR #345
(`agent/ecdlp-m16-kummer-local-fiber`, in the stacked M16 chain #343–#355) proves, for
secp256k1 base-changed to the chosen algebraic closure of `𝔽_p`, the projective local fiber
`HValue_barKummer_zero_iff`: `HValue(κ(P), κ(Q), W) = 0` iff `W` normalizes to `κ(P+Q)` or
`κ(P−Q)`, where `κ` is the Kummer coordinate. With `HValue_affine_eq_S₃` from the same chain,
its affine case corresponds to the secp256k1 instance over `𝔽̄_p` of
`S₃_eq_zero_iff_exists_point`. This file is stated over the base field, for every curve in
short normal form, in affine form on Mathlib's points, and adds no `HValue` or `frozenC`
semantics.
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
  simp [S₃, WeierstrassCurve.addSubMap, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

variable {K : Type*} [Field K] [DecidableEq K]

omit [DecidableEq K] in
/-- On a curve in short normal form the affine equation is `y² = x³ + a₄·x + a₆`. -/
private lemma eq_of_equation (W : WeierstrassCurve K) [W.IsShortNF] {x y : K}
    (h : W.toAffine.Equation x y) : y ^ 2 = x ^ 3 + W.a₄ * x + W.a₆ := by
  have h' := (WeierstrassCurve.Affine.equation_iff (W := W.toAffine) x y).mp h
  have e₁ : W.toAffine.a₁ = 0 := W.a₁_of_isShortNF
  have e₂ : W.toAffine.a₂ = 0 := W.a₂_of_isShortNF
  have e₃ : W.toAffine.a₃ = 0 := W.a₃_of_isShortNF
  rw [e₁, e₂, e₃] at h'
  linear_combination h'

omit [DecidableEq K] in
/-- On a curve in short normal form `negY x y = -y`. -/
private lemma negY_eq (W : WeierstrassCurve K) [W.IsShortNF] (x y : K) :
    W.toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY]

open WeierstrassCurve.Affine in
/-- **Key lemma.** If the sum of two affine points is the affine point `(x, y)`, then
`S₃(x₁, x₂, x) = 0`. -/
private lemma S₃_eq_zero_of_add_eq_some (W : WeierstrassCurve K) [W.IsShortNF]
    {x₁ y₁ x₂ y₂ x y : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (h : W.toAffine.Nonsingular x y)
    (hadd : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x y h) :
    S₃ W.a₄ W.a₆ x₁ x₂ x = 0 := by
  have e₁ : W.toAffine.a₁ = 0 := W.a₁_of_isShortNF
  have e₂ : W.toAffine.a₂ = 0 := W.a₂_of_isShortNF
  have e₄ : W.toAffine.a₄ = W.a₄ := rfl
  have c₁ := eq_of_equation W h₁.1
  have c₂ := eq_of_equation W h₂.1
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ W.toAffine.negY x₁ y₂ := by
      intro hy
      rw [Point.add_of_Y_eq rfl hy] at hadd
      exact Point.some_ne_zero h hadd.symm
    obtain rfl : y₁ = y₂ := Y_eq_of_Y_ne h₁.1 h₂.1 rfl hy
    rw [Point.add_of_Y_ne hy, Point.some.injEq] at hadd
    have hX := hadd.1
    have h2y : 2 * y₁ ≠ 0 := by
      intro h0; apply hy; rw [negY_eq]; linear_combination h0
    have hs : W.toAffine.slope x₁ x₁ y₁ y₁ = (3 * x₁ ^ 2 + W.a₄) / (2 * y₁) := by
      rw [slope_of_Y_ne rfl hy, negY_eq, e₁, e₂, e₄]
      congr 1 <;> ring
    rw [hs, WeierstrassCurve.Affine.addX, e₁, e₂] at hX
    have key : (3 * x₁ ^ 2 + W.a₄) ^ 2 / (2 * y₁) ^ 2 = x + 2 * x₁ := by
      rw [← div_pow]; linear_combination hX
    rw [div_eq_iff (pow_ne_zero 2 h2y)] at key
    exact S₃_eq_zero_of_tangent W.a₄ W.a₆ x₁ y₁ x c₁ (by linear_combination -key)
  · rw [Point.add_of_X_ne hx, Point.some.injEq] at hadd
    have hX := hadd.1
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    rw [slope_of_X_ne hx, WeierstrassCurve.Affine.addX, e₁, e₂] at hX
    have key : (y₁ - y₂) ^ 2 / (x₁ - x₂) ^ 2 = x₁ + x₂ + x := by
      rw [← div_pow]; linear_combination hX
    rw [div_eq_iff (pow_ne_zero 2 hd)] at key
    exact S₃_eq_zero_of_chord W.a₄ W.a₆ x₁ y₁ x₂ y₂ x c₁ c₂ hx (by linear_combination -key)

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
  rw [add_eq_zero_iff_eq_neg, Point.neg_some] at hsum
  exact S₃_eq_zero_of_add_eq_some W h₁ h₂ _ hsum

open WeierstrassCurve.Affine in
/-- **Reverse step.** If `S₃(x₁,x₂,x₃) = 0`, then `P₁ + P₂` or `P₁ − P₂` is an affine point
with `x`-coordinate `x₃`. -/
private lemma exists_add_or_sub_of_S₃_eq_zero (W : WeierstrassCurve K) [W.IsShortNF]
    {x₁ y₁ x₂ y₂ x₃ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hS : S₃ W.a₄ W.a₆ x₁ x₂ x₃ = 0) :
    ∃ (y : K) (h : W.toAffine.Nonsingular x₃ y),
      Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y h ∨
      Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ = Point.some x₃ y h := by
  have e₁ : W.toAffine.a₁ = 0 := W.a₁_of_isShortNF
  have e₂ : W.toAffine.a₂ = 0 := W.a₂_of_isShortNF
  have e₃ : W.toAffine.a₃ = 0 := W.a₃_of_isShortNF
  have e₄ : W.toAffine.a₄ = W.a₄ := rfl
  have c₁ := eq_of_equation W h₁.1
  have c₂ := eq_of_equation W h₂.1
  have mk : ∀ {X Y : K} (hXY : W.toAffine.Nonsingular X Y), X = x₃ →
      ∃ (y : K) (h : W.toAffine.Nonsingular x₃ y), Point.some X Y hXY = Point.some x₃ y h := by
    rintro X Y hXY rfl
    exact ⟨Y, hXY, rfl⟩
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ W.toAffine.negY x₁ y₁ := by
      intro hy
      rw [negY_eq] at hy
      have h2 : 2 * y₁ = 0 := by linear_combination hy
      have hns := ((WeierstrassCurve.Affine.nonsingular_iff (W := W.toAffine) x₁ y₁).mp h₁).2
      rw [e₁, e₂, e₃, e₄] at hns
      have hA : 3 * x₁ ^ 2 + W.a₄ ≠ 0 := by
        rcases hns with hns | hns
        · intro h0; apply hns; linear_combination -h0
        · exact absurd (by linear_combination hy) hns
      apply hA
      have hS' : S₃ W.a₄ W.a₆ x₁ x₁ x₃ = (3 * x₁ ^ 2 + W.a₄) ^ 2 := by
        simp only [S₃]
        linear_combination (4 * (x₃ + 2 * x₁)) * c₁ - (2 * y₁ * (x₃ + 2 * x₁)) * h2
      rw [hS'] at hS
      exact pow_eq_zero_iff two_ne_zero |>.mp hS
    have h2y : 2 * y₁ ≠ 0 := by
      intro h0; apply hy; rw [negY_eq]; linear_combination h0
    have hs : W.toAffine.slope x₁ x₁ y₁ y₁ = (3 * x₁ ^ 2 + W.a₄) / (2 * y₁) := by
      rw [slope_of_Y_ne rfl hy, negY_eq, e₁, e₂, e₄]
      congr 1 <;> ring
    have hdbl : 4 * y₁ ^ 2 * (x₃ + 2 * x₁) = (3 * x₁ ^ 2 + W.a₄) ^ 2 := by
      simp only [S₃] at hS
      linear_combination -hS + 4 * (x₃ + 2 * x₁) * c₁
    have hX : W.toAffine.addX x₁ x₁ (W.toAffine.slope x₁ x₁ y₁ y₁) = x₃ := by
      have key : ((3 * x₁ ^ 2 + W.a₄) / (2 * y₁)) ^ 2 = x₃ + 2 * x₁ := by
        rw [div_pow, div_eq_iff (pow_ne_zero 2 h2y)]
        linear_combination -hdbl
      rw [hs, WeierstrassCurve.Affine.addX, e₁, e₂]
      linear_combination key
    obtain ⟨y, h, hP⟩ := mk (nonsingular_add h₁ h₁ fun hxy => hy hxy.2) hX
    rcases Y_eq_of_X_eq h₂.1 h₁.1 rfl with rfl | hy₂
    · exact ⟨y, h, Or.inl (by rw [Point.add_of_Y_ne hy]; exact hP)⟩
    · have hsub : Point.some x₁ y₁ h₁ - Point.some x₁ y₂ h₂
          = Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁ := by
        rw [sub_eq_add_neg, Point.neg_some]
        congr 1
        simp only [Point.some.injEq, true_and]
        rw [hy₂, negY_negY]
      exact ⟨y, h, Or.inr (by rw [hsub, Point.add_of_Y_ne hy]; exact hP)⟩
  · have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    rcases S₃_root_of_eq_zero W.a₄ W.a₆ x₁ y₁ x₂ y₂ x₃ c₁ c₂ hS with hr | hr
    · have hX : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) = x₃ := by
        have key : ((y₁ - y₂) / (x₁ - x₂)) ^ 2 = x₁ + x₂ + x₃ := by
          rw [div_pow, div_eq_iff (pow_ne_zero 2 hd)]
          linear_combination -hr
        rw [slope_of_X_ne hx, WeierstrassCurve.Affine.addX, e₁, e₂]
        linear_combination key
      obtain ⟨y, h, hP⟩ := mk (nonsingular_add h₁ h₂ fun hxy => hx hxy.1) hX
      exact ⟨y, h, Or.inl (by rw [Point.add_of_X_ne hx]; exact hP)⟩
    · have hn : W.toAffine.Nonsingular x₂ (W.toAffine.negY x₂ y₂) :=
        (nonsingular_neg x₂ y₂).mpr h₂
      have hX : W.toAffine.addX x₁ x₂
          (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) = x₃ := by
        have key : ((y₁ - -y₂) / (x₁ - x₂)) ^ 2 = x₁ + x₂ + x₃ := by
          rw [div_pow, div_eq_iff (pow_ne_zero 2 hd)]
          linear_combination -hr
        rw [slope_of_X_ne hx, negY_eq, WeierstrassCurve.Affine.addX, e₁, e₂]
        linear_combination key
      obtain ⟨y, h, hP⟩ := mk (nonsingular_add h₁ hn fun hxy => hx hxy.1) hX
      exact ⟨y, h, Or.inr (by rw [sub_eq_add_neg, Point.neg_some, Point.add_of_X_ne hx]; exact hP)⟩

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
  constructor
  · intro hS
    obtain ⟨y, h, hP | hP⟩ := exists_add_or_sub_of_S₃_eq_zero W h₁ h₂ hS
    · refine ⟨W.toAffine.negY x₃ y, (nonsingular_neg x₃ y).mpr h, Or.inl ?_⟩
      rw [hP, ← Point.neg_some]
      exact add_neg_cancel _
    · refine ⟨W.toAffine.negY x₃ y, (nonsingular_neg x₃ y).mpr h, Or.inr ?_⟩
      rw [hP, ← Point.neg_some]
      exact add_neg_cancel _
  · rintro ⟨y₃, h₃, hs | hs⟩
    · exact S₃_eq_zero_of_add_add_eq_zero W h₁ h₂ h₃ hs
    · rw [sub_eq_add_neg, Point.neg_some] at hs
      exact S₃_eq_zero_of_add_add_eq_zero W h₁ _ h₃ hs

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
  rw [S₃_eq_zero_iff_exists_point W h₁ h₂ x₃]
  constructor
  · rintro ⟨y, h, hs | hs⟩ <;>
      rcases (Point.X_eq_iff (h₁ := h) (h₂ := h₃)).mp rfl with he | he <;>
      rw [he] at hs
    · exact ⟨1, 1, by simpa using hs⟩
    · exact ⟨1, -1, by simpa using hs⟩
    · exact ⟨-1, 1, by simpa [sub_eq_add_neg] using hs⟩
    · exact ⟨-1, -1, by simpa [sub_eq_add_neg] using hs⟩
  · rintro ⟨ε₂, ε₃, hs⟩
    rcases Int.units_eq_one_or ε₂ with rfl | rfl <;>
      rcases Int.units_eq_one_or ε₃ with rfl | rfl <;>
      simp only [Units.val_one, Units.val_neg, one_zsmul, neg_zsmul] at hs
    · exact ⟨y₃, h₃, Or.inl hs⟩
    · exact ⟨_, (nonsingular_neg x₃ y₃).mpr h₃, Or.inl hs⟩
    · exact ⟨y₃, h₃, Or.inr (by rw [sub_eq_add_neg]; exact hs)⟩
    · exact ⟨_, (nonsingular_neg x₃ y₃).mpr h₃, Or.inr (by rw [sub_eq_add_neg]; exact hs)⟩

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
  haveI : secp256k1.IsShortNF := ⟨rfl, rfl, rfl⟩
  exact S₃_eq_zero_iff_signed_sum secp256k1 h₁ h₂ h₃

end Ecdlp.Semaev
