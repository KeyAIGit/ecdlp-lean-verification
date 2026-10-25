import Mathlib
import Ecdlp.Proved.CurveCardinalityExact
import Ecdlp.Proved.GeneratorOrder
import Ecdlp.Proved.PrimeOrderCardinality
import Ecdlp.Proved.CubicNoRootCertificate

/-!
# secp256k1: `#E(𝔽_p) = n` through the curve-generic theorem

A second derivation of the existing `secp256k1_card_point_eq_n` (`CurveCardinalityExact.lean`),
with the same statement. That file uses a `j = 0`-specific step: `−7` is not a cube in `𝔽_p`,
shown by the cubic-residue exponent test (`secp256k1_neg7_pow_ne_one`, `decide +kernel`). Here
the same count is obtained from the curve-generic
`Ecdlp.Weierstrass.natCard_point_eq_of_addOrderOf` (`PrimeOrderCardinality.lean`), with the
2-torsion cubic `x³ + 7` excluded by the kernel-checked certificate
`Ecdlp.CubicCert.secp256k1.cubic_ne_zero` (`decide +kernel`).

The existing theorem and its proof are unchanged. This corollary is kernel-only: its other
inputs, `secp256k1_generator_addOrderOf` (`n • G = 0`, `GeneratorOrder.lean`), the curve facts
of `Secp256k1Curve.lean` and the Pratt certificates for `p` and `n`, are checked by
`decide +kernel` (the hypothesis `[Fact (Nat.Prime p)]` is discharged at use sites by the instance
in `Secp256k1PrimeP.lean`), and `#print axioms` shows only `propext`,
`Classical.choice` and `Quot.sound`.
-/

open WeierstrassCurve.Affine

namespace Ecdlp.Curve

variable [Fact (Nat.Prime Secp256k1.p)]

/-- **`#E(𝔽_p) = n` for secp256k1 via the curve-generic theorem.** Same statement as
`secp256k1_card_point_eq_n`; the 2-torsion step uses the curve-generic no-root certificate
instead of the `j = 0`-specific cube-residue witness. -/
theorem secp256k1_card_point_eq_n_general :
    Nat.card secp256k1.toAffine.Point = Secp256k1.n :=
  Ecdlp.CubicCert.secp256k1.card_eq_of_addOrderOf secp256k1 rfl rfl rfl
    (by simp [secp256k1, Ecdlp.CubicCert.secp256k1.a])
    (by simp [secp256k1, Ecdlp.CubicCert.secp256k1.b]) secp256k1_generator_addOrderOf

end Ecdlp.Curve
