import Mathlib
import Ecdlp.Proved.Secp256k1Curve
import Ecdlp.Proved.GlvEndomorphism
import Ecdlp.Proved.GlvSlopeAll
import Ecdlp.Proved.GlvAddFormula

/-!
# The GLV endomorphism is an additive homomorphism (the object, completed)

`glvPoint : secp256k1.toAffine.Point → secp256k1.toAffine.Point` (the GLV map
`(x, y) ↦ (β·x, y)`, `Ecdlp/Proved/GlvEndomorphism.lean`) respects the group law:

  `glvPoint (P + Q) = glvPoint P + glvPoint Q`.

This is the capstone of the rung ladder. Mathlib computes `P + Q` from a single slope
`ℓ`; the proof is driven by three facts already verified:

* `secp256k1_glv_slope`  — the slope scales by `β²` (all branches);
* `secp256k1_glv_addX`   — then the new `X`-coordinate scales by `β`;
* `secp256k1_glv_addY`   — and the `Y`-coordinate is unchanged.

So the GLV image of the sum `(x₃, y₃)` is `(β·x₃, y₃) = glvPoint (P+Q)`. The two
degenerate branches (a summand at infinity; `P = -Q`, where both sums are `0`) are
handled directly. `negY x y = -y` is `x`-independent for secp256k1, and `β ≠ 0`, so the
"`P = -Q`" test `x₁ = x₂ ∧ y₁ = negY x₂ y₂` is preserved verbatim under `x ↦ β·x` — which
is what lets the *same* addition branch be taken on both sides.

With this, `glvPoint` is a bona fide endomorphism of the secp256k1 point group: the
structural fact behind the GLV scalar decomposition and a genuine entry in the
isogeny/endomorphism layer.
-/

namespace Ecdlp.Curve

open WeierstrassCurve.Affine

variable [Fact (Nat.Prime Secp256k1.p)]

/-- **The GLV endomorphism is additive: `glvPoint (P + Q) = glvPoint P + glvPoint Q`.**
The completed homomorphism property of the secp256k1 GLV map `(x, y) ↦ (β·x, y)`. -/
theorem glvPoint_add (P Q : secp256k1.toAffine.Point) :
    glvPoint (P + Q) = glvPoint P + glvPoint Q := by
  -- β ≠ 0 in 𝔽_p (from β² + β + 1 = 0).
  have hβ0 : (Secp256k1.beta : ZMod Secp256k1.p) ≠ 0 := by
    have hβeig : (Secp256k1.beta : ZMod Secp256k1.p) ^ 2
        + (Secp256k1.beta : ZMod Secp256k1.p) + 1 = 0 := by
      have h0 : ((Secp256k1.beta ^ 2 + Secp256k1.beta + 1 : ℕ) : ZMod Secp256k1.p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact Nat.dvd_of_mod_eq_zero Secp256k1.beta_field_eigenvalue_kernel
      push_cast at h0; linear_combination h0
    intro hb; rw [hb] at hβeig; norm_num at hβeig
  -- negY is x-independent for secp256k1 (a₁ = a₃ = 0): negY _ y = -y.
  have hnegY : ∀ a y : ZMod Secp256k1.p, secp256k1.toAffine.negY a y = -y := by
    intro a y; simp [WeierstrassCurve.Affine.negY, secp256k1]
  cases P with
  | zero =>
    show glvPoint (0 + Q) = glvPoint 0 + glvPoint Q
    rw [zero_add, glvPoint_zero, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      show glvPoint (Point.some x₁ y₁ h₁ + 0)
        = glvPoint (Point.some x₁ y₁ h₁) + glvPoint 0
      rw [add_zero, glvPoint_zero, add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = secp256k1.toAffine.negY x₂ y₂
      · -- Vertical branch: P = -Q, so both sums are the point at infinity.
        obtain ⟨hx, hy⟩ := hxy
        have hβx : (Secp256k1.beta : ZMod Secp256k1.p) * x₁
            = (Secp256k1.beta : ZMod Secp256k1.p) * x₂ := by rw [hx]
        have hβy : y₁
            = secp256k1.toAffine.negY ((Secp256k1.beta : ZMod Secp256k1.p) * x₂) y₂ := by
          rw [hnegY]; rw [hnegY] at hy; exact hy
        rw [Point.add_of_Y_eq hx hy, glvPoint_zero, glvPoint_some, glvPoint_some,
          Point.add_of_Y_eq hβx hβy]
      · -- General branch: the same non-vertical addition is taken on both sides.
        have hxy' : ¬((Secp256k1.beta : ZMod Secp256k1.p) * x₁
            = (Secp256k1.beta : ZMod Secp256k1.p) * x₂
            ∧ y₁ = secp256k1.toAffine.negY ((Secp256k1.beta : ZMod Secp256k1.p) * x₂) y₂) := by
          rintro ⟨he, hn⟩
          refine hxy ⟨mul_left_cancel₀ hβ0 he, ?_⟩
          rw [hnegY]; rw [hnegY] at hn; exact hn
        -- `some.injEq` drops the `Nonsingular` proof field (a `Prop`, so
        -- proof-irrelevant), leaving exactly the two coordinate equalities.
        rw [Point.add_some hxy, glvPoint_some, glvPoint_some, glvPoint_some,
          Point.add_some hxy', Point.some.injEq]
        refine ⟨?_, ?_⟩
        · -- X-coordinate: β·addX = addX after slope→β²·slope and addX→β·addX.
          rw [secp256k1_glv_slope, secp256k1_glv_addX]
        · -- Y-coordinate: unchanged after slope→β²·slope and addY invariance.
          rw [secp256k1_glv_slope, secp256k1_glv_addY]

end Ecdlp.Curve
