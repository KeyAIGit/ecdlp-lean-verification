import Mathlib
import Ecdlp.Proved.P256Cardinality

/-!
# OPEN TARGET (frozen statements): NIST P-256 exact point count `#E(𝔽_p) = n`

Upgrades `p256_n_dvd_card_point` (`n ∣ #E`, `P256Cardinality.lean`) to the exact count
`Nat.card P256.toAffine.Point = n`, i.e. P-256 has cofactor 1. No Hasse bound or Schoof
algorithm is used. The proof instantiates the curve-generic theorem
`Ecdlp.Weierstrass.natCard_point_eq_of_addOrderOf` (`PrimeOrderCardinality.lean`):

* `a₁ = a₃ = 0` and `2 ≠ 0` in `𝔽_p`;
* the 2-torsion cubic `x³ − 3x + b` has no root in `𝔽_p`: the kernel-checked certificate
  `Ecdlp.CubicCert.p256.cubic_ne_zero` (`CubicNoRootCertificate.lean`, `decide +kernel`);
* `addOrderOf G = n`: the existing `p256_generator_addOrderOf` (`P256GeneratorOrder.lean`);
* `2p + 1 < 3n`: `Ecdlp.CubicCert.p256.two_mul_add_one_lt_three_mul` (`decide +kernel`).

## Trust base

The certificate layer and the generic theorem use only `propext`, `Classical.choice` and
`Quot.sound`. The final count additionally inherits compiler trust (`Lean.ofReduceBool`) from
existing `native_decide` facts: `n • G = 0` and the base point's nonsingularity
(`P256GeneratorOrder.lean`), the curve facts in `P256Curve.lean`, and the Pratt certificates
for `p` and `n` (`P256PrimeP.lean`, `P256PrimeN.lean`). It is therefore a `native_decide`
result, not a pure-kernel one.

This file is an **open stem** (statements frozen before proof; each proof is `sorry`).
It is not imported by `Ecdlp.lean`, not built, and excluded from the no-`sorry` gate. The
proof is intended to land in `Ecdlp/Proved/P256CardinalityExact.lean`, which consumes this stem.
-/

open WeierstrassCurve.Affine

namespace Ecdlp.P256

/-- `2 ≠ 0` in the P-256 base field (`p` is odd). -/
theorem p256_two_ne_zero : (2 : ZMod p) ≠ 0 := by
  sorry

/-- **P-256 has no rational 2-torsion cubic root:** `x³ + a₂x² + a₄x + a₆ ≠ 0` for every
`x ∈ 𝔽_p`, from the kernel-checked certificate `Ecdlp.CubicCert.p256.cubic_ne_zero`. -/
theorem p256_no_two_torsion_cubic :
    ∀ x : ZMod p, x ^ 3 + P256.a₂ * x ^ 2 + P256.a₄ * x + P256.a₆ ≠ 0 := by
  sorry

/-- **The exact NIST P-256 point count: `#E(𝔽_p) = n`** (cofactor 1). From the curve-generic
`natCard_point_eq_of_addOrderOf`, the no-root certificate, and `addOrderOf G = n`. Inherits
`native_decide` compiler trust through `p256_generator_addOrderOf` and the primality
instances (see the module header). -/
theorem p256_card_point_eq_n : Nat.card P256.toAffine.Point = n := by
  sorry

end Ecdlp.P256
