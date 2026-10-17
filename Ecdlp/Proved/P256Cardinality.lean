import Mathlib
import Ecdlp.Proved.P256GeneratorOrder
import Ecdlp.Proved.AffinePointFinite

/-!
# NIST P-256: the rational-point group is finite, and `n ∣ #E(𝔽_p)`

Mirrors secp256k1's `Ecdlp/Proved/CurveCardinality.lean` for the P-256 domain. The first
verified rung about the curve cardinality `#E(𝔽_p)` itself (all prior P-256 point-counting
work stayed inside the base-point subgroup `⟨G⟩`). Two facts:

* `Finite P256.toAffine.Point` — the group of `𝔽_p`-rational points is finite (points inject
  into `Option (𝔽_p × 𝔽_p)`, which is finite since `𝔽_p` is). Without this, Mathlib's
  `Nat.card E.toAffine.Point` is junk `0`; with it, the count is real.
* `p256_n_dvd_card_point : P256.n ∣ Nat.card P256.toAffine.Point` — the prime base-point order
  divides `#E` (Lagrange on `⟨G⟩`, whose order is the proved `n`).

This is only the **weak keystone**: it pins `#E ∈ {n, 2n, 3n, …}`. The **strong keystone**
`#E = n` (cofactor 1) is proved in `P256CardinalityExact.lean` (`p256_card_point_eq_n`). The
secp256k1 `−7`-non-cube step (`CurveCardinalityExact.lean`) is `j = 0`-specific and is not used
there; instead the curve-generic `natCard_point_eq_of_addOrderOf` (`PrimeOrderCardinality.lean`:
`#E ≤ 2p+1 < 3n` and no rational 2-torsion) is applied with a kernel-checked certificate that
`x³ − 3x + b` has no root in `𝔽_p` (`CubicNoRootCertificate.lean`). No Hasse bound is needed.
-/

open WeierstrassCurve.Affine

namespace Ecdlp.P256

/-- The P-256 `𝔽_p`-rational point group is **finite** — a specialisation of the general
`WeierstrassCurve.Affine.instFinitePoint` (`Point ↪ Option (R × R)`, needing only `[CommRing R]`
`[Finite R]`), since `ZMod p` is a finite commutative ring. -/
instance instFiniteP256Point : Finite P256.toAffine.Point := inferInstance

/-- The concrete P-256 crypto subgroup `⟨G⟩ = zmultiples G`. -/
abbrev p256Grp : AddSubgroup P256.toAffine.Point := AddSubgroup.zmultiples p256G

/-- **`⟨G⟩` has exactly `n` elements**, from `Nat.card (zmultiples g) = addOrderOf g` and
`addOrderOf G = n`. -/
theorem p256_grp_card : Nat.card ↥p256Grp = n := by
  rw [Nat.card_zmultiples, p256_generator_addOrderOf]

/-- **`n ∣ #E(𝔽_p)`.** The prime base-point order divides the P-256 curve cardinality —
Lagrange applied to the subgroup `⟨G⟩` of proved order `n`. This is the weak keystone
(`#E ∈ {n, 2n, 3n, …}`); the strong keystone `#E = n` is `p256_card_point_eq_n` in
`P256CardinalityExact.lean` (see the header). -/
theorem p256_n_dvd_card_point :
    n ∣ Nat.card P256.toAffine.Point := by
  rw [← p256_grp_card]
  exact ⟨p256Grp.index, (AddSubgroup.card_mul_index p256Grp).symm⟩

end Ecdlp.P256
