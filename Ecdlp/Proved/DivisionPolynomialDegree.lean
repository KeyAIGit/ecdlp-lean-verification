import Mathlib
import Ecdlp.Proved.DivisionPolynomial
import Ecdlp.Proved.Secp256k1PrimeP

/-!
# Degree of the secp256k1 2-division polynomial (torsion point count)

The 2-division polynomial `Ψ₂Sq = 4X³ + 28` has **degree 3** over `𝔽_p`, so it has
at most 3 roots — hence secp256k1 has at most 3 nontrivial 2-torsion `x`-coordinates,
i.e. `#E[2] ≤ 4` (the three order-2 points plus `O`). This is the first concrete
*torsion-count* fact, the degree side of the division-polynomial picture (Mathlib's
`DivisionPolynomial.Degree`). Uses the machine-checked primality of `p` (so `𝔽_p`
is a field / has no zero divisors and the leading coefficient `4 ≠ 0`).
-/

namespace Ecdlp.Curve

open Polynomial

/-- **`Ψ₂Sq` has degree 3.** The secp256k1 2-division polynomial `4X³ + 28` has
`natDegree = 3`, so at most 3 two-torsion `x`-coordinates exist (`#E[2] ≤ 4`). -/
theorem secp256k1_Ψ₂Sq_natDegree : secp256k1.Ψ₂Sq.natDegree = 3 := by
  have h4 : (4 : ZMod Secp256k1.p) ≠ 0 := by
    have h : ((4 : ℕ) : ZMod Secp256k1.p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; decide +kernel
    simpa using h
  rw [secp256k1_Ψ₂Sq, natDegree_add_eq_left_of_natDegree_lt]
  · rw [natDegree_C_mul h4, natDegree_X_pow]
  · rw [natDegree_C_mul h4, natDegree_X_pow, natDegree_C]; norm_num

/-- **At most 3 two-torsion `x`-coordinates.** Since `Ψ₂Sq` has degree 3, it has at
most 3 roots in `𝔽_p`; these are exactly the `x`-coordinates of the order-2 points,
so secp256k1 has at most 3 nontrivial 2-torsion points (`#E[2] ≤ 4` with `O`). -/
theorem secp256k1_two_torsion_x_card_le :
    Multiset.card secp256k1.Ψ₂Sq.roots ≤ 3 :=
  (Polynomial.card_roots' _).trans secp256k1_Ψ₂Sq_natDegree.le

/-- The 2-division polynomial is nonzero (it has degree 3), so the 2-torsion
`x`-coordinates form a proper finite set, not all of `𝔽_p`. -/
theorem secp256k1_Ψ₂Sq_ne_zero : secp256k1.Ψ₂Sq ≠ 0 := by
  intro h
  have h3 : secp256k1.Ψ₂Sq.natDegree = 3 := secp256k1_Ψ₂Sq_natDegree
  rw [h, natDegree_zero] at h3
  exact absurd h3 (by norm_num)

/-- **`deg Ψ₃ = 4`** (3-torsion count: `#E[3] ≤ 9`). The 3-division polynomial
`3X⁴ + 84X` has degree 4, so secp256k1 has at most 4 nontrivial 3-torsion
`x`-coordinates. The 3-torsion is the GLV-relevant torsion (the curve's CM by
`ℤ[ζ₃]` acts on `E[3]`). -/
theorem secp256k1_Ψ₃_natDegree : secp256k1.Ψ₃.natDegree = 4 := by
  have h3 : (3 : ZMod Secp256k1.p) ≠ 0 := by
    have h : ((3 : ℕ) : ZMod Secp256k1.p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; decide +kernel
    simpa using h
  rw [secp256k1_Ψ₃]
  compute_degree! <;> first | exact h3 | norm_num

end Ecdlp.Curve
