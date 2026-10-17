import Mathlib
import Ecdlp.Proved.Secp256k1Curve
import Ecdlp.Proved.GlvEndomorphism
import Ecdlp.Proved.GlvHom

/-!
# The GLV endomorphism is a primitive cube root of unity: `φ² + φ + 1 = 0`

The capstone CM fact: `glvPoint` satisfies its minimal polynomial `x² + x + 1` on the
whole secp256k1 point group,

  `glvPoint (glvPoint P) + glvPoint P + P = 0`   for every `P`.

This says `glvPoint` is a primitive cube root of unity in `End(E)` — the
complex-multiplication-by-`ℤ[ζ₃]` structure of the `j = 0` curve, and the algebraic
heart of GLV (it does NOT need the scalar `λ` or point counting; see `notes/GLV_LAMBDA.md`).

**Why it holds.** For `P = (x, y)`, the three points `P = (x,y)`, `φP = (βx, y)`,
`φ²P = (β²x, y)` share the `Y`-coordinate `y`, so they are collinear on the horizontal
line `Y = y`. The first two already sum to `−P`: the secant/tangent slope is `0` (equal
`Y`'s), giving new `X = −(β² + β)x = x` (using `β² + β = −1`) and `Y = −y`, i.e.
`φ²P + φP = −P`; adding `P` gives `0` via `add_of_Y_eq`. The proof splits on `x = 0`
(the three coincide at a 3-torsion point `(0, ±√7)`, doubling formula) vs `x ≠ 0`
(`β²x ≠ βx`, secant formula).
-/

namespace Ecdlp.Curve

open WeierstrassCurve.Affine

variable [Fact (Nat.Prime Secp256k1.p)]

/-- **`φ² + φ + 1 = 0`: the GLV endomorphism is a primitive cube root of unity.** -/
theorem secp256k1_glv_cube_relation (P : secp256k1.toAffine.Point) :
    glvPoint (glvPoint P) + glvPoint P + P = 0 := by
  -- β eigenvalue facts.
  have hbeig : (Secp256k1.beta : ZMod Secp256k1.p) ^ 2
      + (Secp256k1.beta : ZMod Secp256k1.p) + 1 = 0 := by
    have h0 : ((Secp256k1.beta ^ 2 + Secp256k1.beta + 1 : ℕ) : ZMod Secp256k1.p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero Secp256k1.beta_field_eigenvalue_kernel
    push_cast at h0; linear_combination h0
  have hb0 : (Secp256k1.beta : ZMod Secp256k1.p) ≠ 0 := by
    intro hb; rw [hb] at hbeig; norm_num at hbeig
  have hb1 : (Secp256k1.beta : ZMod Secp256k1.p) ≠ 1 := by
    intro hb; rw [hb] at hbeig
    have h3 : (3 : ZMod Secp256k1.p) = 0 := by linear_combination hbeig
    have hne3 : ((3 : ℕ) : ZMod Secp256k1.p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; decide +kernel
    exact hne3 (by exact_mod_cast h3)
  -- Closed arithmetic facts. Route through `Nat.cast`/`ZMod.natCast_eq_zero_iff` so the
  -- remaining goal is a closed `Nat` divisibility fact that the kernel decides
  -- (`decide +kernel`) without unfolding `ZMod` arithmetic or the ambient
  -- `[Fact p.Prime]` instance, matching the pattern elsewhere in this repo (e.g.
  -- `Secp256k1Curve.lean`'s `secp256k1_generator_nonsingular`).
  have h7ne : (7 : ZMod Secp256k1.p) ≠ 0 := by
    have h7 : ((7 : ℕ) : ZMod Secp256k1.p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; decide +kernel
    simpa using h7
  have h2ne : (2 : ZMod Secp256k1.p) ≠ 0 := by
    have h2 : ((2 : ℕ) : ZMod Secp256k1.p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; decide +kernel
    simpa using h2
  -- `negY _ y = -y` for secp256k1.
  have hnegY : ∀ a w : ZMod Secp256k1.p, secp256k1.toAffine.negY a w = -w := by
    intro a w; simp [WeierstrassCurve.Affine.negY, secp256k1]
  cases P with
  | zero =>
    -- `cases` yields the raw constructor `Point.zero`; coerce it to `0` (defeq) so the
    -- `glvPoint_zero` simp lemma keys correctly, then everything collapses.
    show glvPoint (glvPoint 0) + glvPoint 0 + 0 = 0
    simp only [glvPoint_zero, add_zero]
  | some x y h =>
    simp only [glvPoint_some]
    set b : ZMod Secp256k1.p := (Secp256k1.beta : ZMod Secp256k1.p) with hbdef
    by_cases hx0 : x = 0
    · -- Coincident / 3-torsion case: the three points are all `(0, y)`.
      subst hx0
      -- `(0,y)` on the curve forces `y² = 7`, so `y ≠ 0`.
      have hy0 : y ≠ 0 := by
        intro hy
        apply h7ne
        have heq : secp256k1.toAffine.Equation 0 y :=
          ((WeierstrassCurve.Affine.nonsingular_iff 0 y).mp h).1
        rw [WeierstrassCurve.Affine.equation_iff] at heq
        simp only [secp256k1] at heq
        rw [hy] at heq
        linear_combination -heq
      have hyne : y ≠ secp256k1.toAffine.negY (b * 0) y := by
        rw [hnegY]; intro hc
        apply hy0
        have h2y : (2 : ZMod Secp256k1.p) * y = 0 := by linear_combination hc
        rcases mul_eq_zero.mp h2y with h2 | hy
        · exact absurd h2 h2ne
        · exact hy
      rw [Point.add_of_Y_ne hyne]
      have hxe : (b * (b * 0) : ZMod Secp256k1.p) = b * 0 := by ring
      refine Point.add_of_Y_eq ?_ ?_
      · rw [slope_of_Y_ne hxe hyne]
        simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, secp256k1]
        ring
      · rw [slope_of_Y_ne hxe hyne]
        simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
          WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, secp256k1]
        ring
    · -- Generic case: `β²x ≠ βx`, the secant formula.
      have hne : (b * (b * x) : ZMod Secp256k1.p) ≠ b * x := by
        intro hc
        apply hx0
        have h1 : (b * x) * (b - 1) = 0 := by linear_combination hc
        rcases mul_eq_zero.mp h1 with h2 | h3
        · rcases mul_eq_zero.mp h2 with h4 | h5
          · exact absurd h4 hb0
          · exact h5
        · exact absurd (sub_eq_zero.mp h3) hb1
      rw [Point.add_of_X_ne hne]
      refine Point.add_of_Y_eq ?_ ?_
      · -- new X-coordinate `= x`, using `β² + β + 1 = 0`.
        rw [slope_of_X_ne hne]
        simp only [sub_self, zero_div, WeierstrassCurve.Affine.addX, secp256k1]
        linear_combination (-x) * hbeig
      · -- new Y-coordinate `= negY x y = -y`.
        rw [slope_of_X_ne hne]
        simp only [sub_self, zero_div, WeierstrassCurve.Affine.addY,
          WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
          WeierstrassCurve.Affine.addX, secp256k1]
        ring

end Ecdlp.Curve
