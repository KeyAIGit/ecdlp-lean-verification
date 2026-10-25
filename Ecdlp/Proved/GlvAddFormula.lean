import Mathlib
import Ecdlp.Proved.Secp256k1Curve

/-!
# GLV β-equivariance of the affine addition formulae

With the slope identity `secp256k1_glv_slope` (`slope ↦ β²·slope`) in hand, the rest
of Mathlib's affine addition is mechanical. Mathlib computes `P + Q` from a single
slope `ℓ` via `addX x₁ x₂ ℓ = ℓ² - x₁ - x₂` and `addY x₁ x₂ y₁ ℓ = -(ℓ·(addX-x₁)+y₁)`
(for secp256k1, where `a₁=a₂=a₃=a₄=0`). This file records how those scale under the
GLV map `x ↦ β·x` together with the induced `ℓ ↦ β²·ℓ`:

* `addX (β·x₁) (β·x₂) (β²·ℓ) = β · addX x₁ x₂ ℓ`  — the new `X`-coordinate is `β·x₃`;
* `addY (β·x₁) (β·x₂) y₁ (β²·ℓ) = addY x₁ x₂ y₁ ℓ` — the `Y`-coordinate is unchanged.

Both are pure `β³ = 1` polynomial identities (`addX`/`addY` are polynomial in `ℓ, x, y`),
which is exactly why the GLV image of `(x₃, y₃)` is `(β·x₃, y₃) = glvPoint (P+Q)`.
These are the last algebraic facts before assembling `glvPoint_add` (the homomorphism).
-/

namespace Ecdlp.Curve

open WeierstrassCurve.Affine

variable [Fact (Nat.Prime Secp256k1.p)]

/-- The cube-root relation `β³ = 1` in `𝔽_p` (from `β² + β + 1 = 0`). -/
private theorem beta_cubed_eq_one :
    (Secp256k1.beta : ZMod Secp256k1.p) ^ 3 = 1 := by
  have hβeig : (Secp256k1.beta : ZMod Secp256k1.p) ^ 2
      + (Secp256k1.beta : ZMod Secp256k1.p) + 1 = 0 := by
    have h0 : ((Secp256k1.beta ^ 2 + Secp256k1.beta + 1 : ℕ) : ZMod Secp256k1.p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero Secp256k1.beta_field_eigenvalue_kernel
    push_cast at h0
    linear_combination h0
  linear_combination ((Secp256k1.beta : ZMod Secp256k1.p) - 1) * hβeig

/-- **GLV β-equivariance of `addX`.** Scaling both `X`-coordinates by `β` and the slope
by `β²` scales the resulting `X`-coordinate by `β` (uses `β⁴ = β`, i.e. `β³ = 1`). -/
theorem secp256k1_glv_addX (x₁ x₂ ℓ : ZMod Secp256k1.p) :
    secp256k1.toAffine.addX ((Secp256k1.beta : ZMod Secp256k1.p) * x₁)
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₂)
        ((Secp256k1.beta : ZMod Secp256k1.p) ^ 2 * ℓ)
      = (Secp256k1.beta : ZMod Secp256k1.p) * secp256k1.toAffine.addX x₁ x₂ ℓ := by
  have hβ3 := beta_cubed_eq_one
  simp only [WeierstrassCurve.Affine.addX, secp256k1]
  linear_combination ((Secp256k1.beta : ZMod Secp256k1.p) * ℓ ^ 2) * hβ3

/-- **GLV β-equivariance of `addY`.** Scaling both `X`-coordinates by `β` and the slope
by `β²` leaves the resulting `Y`-coordinate unchanged (uses `β⁶ = β³ = 1`). This is the
structural reason `glvPoint` acts as `(x, y) ↦ (β·x, y)` on a sum. -/
theorem secp256k1_glv_addY (x₁ x₂ y₁ ℓ : ZMod Secp256k1.p) :
    secp256k1.toAffine.addY ((Secp256k1.beta : ZMod Secp256k1.p) * x₁)
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₂) y₁
        ((Secp256k1.beta : ZMod Secp256k1.p) ^ 2 * ℓ)
      = secp256k1.toAffine.addY x₁ x₂ y₁ ℓ := by
  have hβ3 := beta_cubed_eq_one
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, secp256k1]
  linear_combination
    (-(Secp256k1.beta : ZMod Secp256k1.p) ^ 3 * ℓ ^ 3 - ℓ ^ 3
      + 2 * ℓ * x₁ + ℓ * x₂) * hβ3

end Ecdlp.Curve
