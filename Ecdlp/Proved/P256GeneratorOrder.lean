import Mathlib
import Ecdlp.Proved.P256Curve
import Ecdlp.Proved.P256PrimeP
import Ecdlp.Proved.P256PrimeN

/-!
# The NIST P-256 base point: exact order `n` (weak point-counting keystone)

Mirrors secp256k1's `Ecdlp/Proved/GeneratorOrder.lean` for the second live domain. The SEC 2
generator `G = (Gx, Gy)`, realized in Mathlib's elliptic-curve point group `P256.toAffine.Point`,
has **exact order `n`** (the published prime group order), so `⟨G⟩` is cyclic of order `n`.

This is the **weak point-counting keystone**: it pins the cryptographic subgroup without
computing `#E(𝔽_p)` (no Hasse/Schoof). Proof: `n • G = 0` (native-evaluated 256-bit
double-and-add over 𝔽_p) and `G ≠ 0`, with `n` prime (`P256PrimeN`) — so `addOrderOf G = n`
by `addOrderOf_eq_prime`. Like every `native_decide` fact here it additionally trusts the Lean
compiler (`TRUST_REPORT.md`). By itself it does **not** give the strong keystone
`#E(𝔽_p) = n` (cofactor 1) — this is the base-point subgroup `⟨G⟩`. The strong keystone is
`p256_card_point_eq_n` (`P256CardinalityExact.lean`), which combines this order fact with
`#E ≤ 2p + 1 < 3n` and a certificate that P-256 has no rational 2-torsion; no Hasse bound.
-/

open WeierstrassCurve.Affine

namespace Ecdlp.P256

/-- The SEC 2 P-256 base point `G = (Gx, Gy)` is a nonsingular point of the curve. -/
theorem p256_generator_nonsingular :
    P256.toAffine.Nonsingular (Gx : ZMod p) (Gy : ZMod p) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  exact ⟨P256_generator_equation, by native_decide⟩

/-- The P-256 base point `G = (Gx, Gy)` as an element of the Mathlib point group. -/
def p256G : P256.toAffine.Point :=
  Point.some (Gx : ZMod p) (Gy : ZMod p) p256_generator_nonsingular

/-- `n • G = 0`: the published prime order annihilates the base point (native-evaluated). -/
theorem p256_generator_nsmul_n_eq_zero : (n : ℕ) • p256G = 0 := by native_decide

/-- The base point is not the group identity (it is an affine point). -/
theorem p256_generator_ne_zero : p256G ≠ 0 :=
  Point.some_ne_zero _

/-- **The NIST P-256 base point has exact order `n`** (the published prime group order), so
`⟨G⟩` is cyclic of order `n` — the weak point-counting keystone (no Hasse / `#E` needed). -/
theorem p256_generator_addOrderOf :
    addOrderOf p256G = n :=
  addOrderOf_eq_prime p256_generator_nsmul_n_eq_zero p256_generator_ne_zero

end Ecdlp.P256
