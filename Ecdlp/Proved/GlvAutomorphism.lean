import Mathlib
import Ecdlp.Proved.Secp256k1Curve
import Ecdlp.Proved.GlvEndomorphism

/-!
# The GLV endomorphism is an automorphism of order dividing 3

`glvPoint : (x,y) ↦ (β·x, y)` is built from multiplication by the cube-root factor `β`
(`β³ = 1` in `𝔽_p`; `Ecdlp/Proved/GlvEndomorphism.lean`). Iterating it three times scales
the `X`-coordinate by `β³ = 1` and leaves `Y` untouched, so it returns every point to
itself:

  `glvPoint (glvPoint (glvPoint P)) = P`   for every `P`.

Thus `glvPoint` has order dividing 3 as a self-map, and — being additive
(`glvPoint_add`) — it is an **automorphism** of the secp256k1 point group with inverse
`glvPoint²`. This is the order-3 statement complementary to the minimal-polynomial
identity `φ² + φ + 1 = 0` (`Ecdlp/Proved/GlvMinPoly.lean`): together they exhibit `glvPoint`
as a primitive cube root of unity acting invertibly, the CM-by-`ℤ[ζ₃]` automorphism of the
`j = 0` curve. (Still no `λ`, no point counting — see `notes/GLV_LAMBDA.md`.)
-/

namespace Ecdlp.Curve

open WeierstrassCurve.Affine

variable [Fact (Nat.Prime Secp256k1.p)]

/-- **`glvPoint³ = id`: the GLV endomorphism has order dividing 3.** Applying the map
`(x,y) ↦ (β·x, y)` three times scales `x` by `β³ = 1`, so every point returns to itself. -/
theorem glvPoint_cube_eq_id (P : secp256k1.toAffine.Point) :
    glvPoint (glvPoint (glvPoint P)) = P := by
  -- β² + β + 1 = 0, hence β³ = 1 (both lifted from the machine-checked Nat eigenvalue fact).
  have hβeig : (Secp256k1.beta : ZMod Secp256k1.p) ^ 2
      + (Secp256k1.beta : ZMod Secp256k1.p) + 1 = 0 := by
    have h0 : ((Secp256k1.beta ^ 2 + Secp256k1.beta + 1 : ℕ) : ZMod Secp256k1.p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero Secp256k1.beta_field_eigenvalue_kernel
    push_cast at h0; linear_combination h0
  have hβ3 : (Secp256k1.beta : ZMod Secp256k1.p) ^ 3 = 1 := by
    linear_combination ((Secp256k1.beta : ZMod Secp256k1.p) - 1) * hβeig
  cases P with
  | zero =>
    show glvPoint (glvPoint (glvPoint 0)) = 0
    simp only [glvPoint_zero]
  | some x y h =>
    simp only [glvPoint_some]
    rw [Point.some.injEq]
    refine ⟨?_, rfl⟩
    have hxx : (Secp256k1.beta : ZMod Secp256k1.p)
          * ((Secp256k1.beta : ZMod Secp256k1.p) * ((Secp256k1.beta : ZMod Secp256k1.p) * x))
        = (Secp256k1.beta : ZMod Secp256k1.p) ^ 3 * x := by ring
    rw [hxx, hβ3, one_mul]

/-- **The GLV endomorphism is bijective (an automorphism of the point group).** Immediate
from `glvPoint³ = id`: `glvPoint² ` is a two-sided inverse of `glvPoint`. -/
theorem glvPoint_bijective : Function.Bijective glvPoint :=
  Function.bijective_iff_has_inverse.mpr
    ⟨glvPoint ∘ glvPoint, fun P => by
        simpa only [Function.comp_apply] using glvPoint_cube_eq_id P,
      fun P => by simpa only [Function.comp_apply] using glvPoint_cube_eq_id P⟩

end Ecdlp.Curve
