import Mathlib
import Ecdlp.Proved.Secp256k1Curve

/-!
# The GLV endomorphism of secp256k1 — first building block

This file begins constructing a *missing object*: the GLV endomorphism of secp256k1,
the rational self-map `(x, y) ↦ (β·x, y)` where `β ∈ 𝔽_p` is the GLV cube-root factor
(`β² + β + 1 = 0`, equivalently `β³ = 1`; `Secp256k1.beta`). It is the endomorphism that
acts as scalar multiplication by `λ` on the base-point subgroup and powers the GLV
scalar-decomposition speed-up. On the abstract side `Ecdlp.Torsion.zmultiples_le_torsionBy`
and `Ecdlp/Targets/glv_root_mod_n_condition_008.lean` capture "`φ` acts as `[λ]`"; here we
start the concrete object on the actual curve.

**Rung 1 (this file): the map preserves the curve equation** — `(x,y)` on `Y²=X³+7`
implies `(β·x, y)` is too, because `(β·x)³ = β³·x³ = x³`. This is the `Equation` half of
turning `(x,y)↦(β·x,y)` into a genuine `WeierstrassCurve.Affine.Point → Point` map; the
remaining rungs (nonsingularity, then the additive-homomorphism property via the affine
addition formula) are the harder next steps toward the full endomorphism object.
-/

namespace Ecdlp.Curve

/-- **The GLV endomorphism preserves the secp256k1 curve equation.** If `(x, y)` solves
`Y² = X³ + 7`, so does `(β·x, y)`: since `β³ = 1`, `(β·x)³ = β³·x³ = x³`, leaving the
right-hand side unchanged. First step in building the GLV endomorphism as an object on
`secp256k1.toAffine.Point`. -/
theorem secp256k1_glv_preserves_equation
    (x y : ZMod Secp256k1.p)
    (h : secp256k1.toAffine.Equation x y) :
    secp256k1.toAffine.Equation ((Secp256k1.beta : ZMod Secp256k1.p) * x) y := by
  -- β² + β + 1 = 0 in 𝔽_p, lifted from the machine-checked Nat-level eigenvalue fact
  have hβeig : (Secp256k1.beta : ZMod Secp256k1.p) ^ 2
      + (Secp256k1.beta : ZMod Secp256k1.p) + 1 = 0 := by
    have h0 : ((Secp256k1.beta ^ 2 + Secp256k1.beta + 1 : ℕ) : ZMod Secp256k1.p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero Secp256k1.beta_field_eigenvalue_kernel
    push_cast at h0
    linear_combination h0
  -- hence β³ = 1  (β³ − 1 = (β − 1)(β² + β + 1))
  have hβ3 : (Secp256k1.beta : ZMod Secp256k1.p) ^ 3 = 1 := by
    linear_combination ((Secp256k1.beta : ZMod Secp256k1.p) - 1) * hβeig
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  simp only [secp256k1, zero_mul, mul_zero, add_zero, zero_add, mul_one] at h ⊢
  have hcube : ((Secp256k1.beta : ZMod Secp256k1.p) * x) ^ 3 = x ^ 3 := by
    rw [mul_pow, hβ3, one_mul]
  rw [hcube]
  exact h

/-- **The GLV endomorphism preserves nonsingularity.** If `(x, y)` is a smooth point of
secp256k1, so is `(β·x, y)`. The smoothness witness for `Y² = X³ + 7` is
`3x² ≠ 0 ∨ y ≠ -y` (the partial-derivative non-vanishing condition, with `a₁=a₂=a₃=a₄=0`).
Under `x ↦ β·x` the second disjunct is untouched, and the first transfers because `β` is a
unit (`β³ = 1` forces `β ≠ 0`, so `β²` is nonzero and `3(βx)² = 3β²x² ≠ 0 ⟺ 3x² ≠ 0`).
Combined with `secp256k1_glv_preserves_equation`, this is the full `Nonsingular` half needed
to lift `(x,y) ↦ (β·x, y)` to a map on `secp256k1.toAffine.Point`. -/
theorem secp256k1_glv_preserves_nonsingular
    [Fact (Nat.Prime Secp256k1.p)]
    (x y : ZMod Secp256k1.p)
    (h : secp256k1.toAffine.Nonsingular x y) :
    secp256k1.toAffine.Nonsingular ((Secp256k1.beta : ZMod Secp256k1.p) * x) y := by
  -- β² + β + 1 = 0 in 𝔽_p (lifted from the machine-checked Nat-level eigenvalue fact)
  have hβeig : (Secp256k1.beta : ZMod Secp256k1.p) ^ 2
      + (Secp256k1.beta : ZMod Secp256k1.p) + 1 = 0 := by
    have h0 : ((Secp256k1.beta ^ 2 + Secp256k1.beta + 1 : ℕ) : ZMod Secp256k1.p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero Secp256k1.beta_field_eigenvalue_kernel
    push_cast at h0
    linear_combination h0
  -- β ≠ 0: if β = 0 then β² + β + 1 = 1 ≠ 0, contradicting hβeig
  have hβ0 : (Secp256k1.beta : ZMod Secp256k1.p) ≠ 0 := by
    intro hb
    rw [hb] at hβeig
    norm_num at hβeig
  -- β² ≠ 0 since β ≠ 0 (𝔽_p has no zero divisors)
  have hβsq : (Secp256k1.beta : ZMod Secp256k1.p) ^ 2 ≠ 0 := pow_ne_zero 2 hβ0
  rw [WeierstrassCurve.Affine.nonsingular_iff] at h ⊢
  obtain ⟨heq, hsmooth⟩ := h
  refine ⟨secp256k1_glv_preserves_equation x y heq, ?_⟩
  -- reduce both smoothness conditions using the secp256k1 a-invariants
  simp only [secp256k1, zero_mul, mul_zero, add_zero, zero_add, sub_zero, neg_zero] at hsmooth ⊢
  -- hsmooth : (0 : ZMod p) ≠ 3 * x ^ 2  ∨  y ≠ -y
  -- goal    : (0 : ZMod p) ≠ 3 * (β * x) ^ 2  ∨  y ≠ -y
  rcases hsmooth with hx | hy
  · -- left disjunct: transfer 3x² ≠ 0 to 3(βx)² ≠ 0
    refine Or.inl ?_
    -- 3 * (β * x) ^ 2 = β ^ 2 * (3 * x ^ 2)
    have hxne : (3 : ZMod Secp256k1.p) * x ^ 2 ≠ 0 := fun h => hx h.symm
    have : (3 : ZMod Secp256k1.p) * (Secp256k1.beta * x) ^ 2
        = Secp256k1.beta ^ 2 * (3 * x ^ 2) := by ring
    rw [this]
    exact (mul_ne_zero hβsq hxne).symm
  · -- right disjunct: y ≠ -y is unchanged
    exact Or.inr hy

/-- **The GLV endomorphism as a self-map of the secp256k1 point group.** Sends the
point at infinity to itself and an affine point `(x, y)` to `(β·x, y)`, whose
nonsingularity is supplied by `secp256k1_glv_preserves_nonsingular`. This packages the
two preservation lemmas (rungs 1–2) into a genuine `Point → Point` map — the object on
which the additive-homomorphism property `φ(P+Q)=φ(P)+φ(Q)` will be proved next. -/
def glvPoint [Fact (Nat.Prime Secp256k1.p)] :
    secp256k1.toAffine.Point → secp256k1.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (↑Secp256k1.beta * x) y (secp256k1_glv_preserves_nonsingular x y h)

@[simp]
theorem glvPoint_zero [Fact (Nat.Prime Secp256k1.p)] :
    glvPoint (0 : secp256k1.toAffine.Point) = 0 :=
  rfl

@[simp]
theorem glvPoint_some [Fact (Nat.Prime Secp256k1.p)]
    (x y : ZMod Secp256k1.p) (h : secp256k1.toAffine.Nonsingular x y) :
    glvPoint (.some x y h)
      = .some (↑Secp256k1.beta * x) y (secp256k1_glv_preserves_nonsingular x y h) :=
  rfl

end Ecdlp.Curve
