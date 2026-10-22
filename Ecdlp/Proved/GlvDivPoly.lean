import Mathlib
import Ecdlp.Proved.Secp256k1Curve
import Ecdlp.Proved.DivisionPolynomial
import Ecdlp.Proved.ThreeTorsionCard
import Ecdlp.Proved.MultiplicationFormula
import Ecdlp.Proved.CoprimePsi3Psi5
import Ecdlp.Proved.CoprimePsi3Psi7
import Ecdlp.Proved.CubeRoot

/-!
# The GLV covariance law for the secp256k1 division polynomials

The secp256k1 GLV endomorphism acts on `x`-coordinates by `x ↦ β·x`, where
`β` is a primitive cube root of unity mod `p` (`β³ = 1`, `β² + β + 1 = 0`;
see `Secp256k1.beta_field_eigenvalue` and `Secp256k1.beta_is_cube_root`).

For the `j = 0` curve `E : Y² = X³ + 7` the division polynomials are supported on a
single exponent residue class mod `3`, so `β` acts on each `ψ_m` by a single scalar:

  `ψ_m(β·x) = β^((m²−1)/2) · ψ_m(x)`.

The scalar `β^((m²−1)/2)` reduces mod the order `3` of `β`. Concretely, evaluated over
`𝔽_p`:

* `Ψ₃ = 3X⁴ + 84X` has exponents `≡ 1 (mod 3)`, and `(3²−1)/2 = 4 ≡ 1 (mod 3)`, so
  `Ψ₃(β·x) = β · Ψ₃(x)`.
* `preΨ' 5 = 5X¹² + 2660X⁹ − 11760X⁶ − 548800X³ − 614656` has exponents `≡ 0 (mod 3)`,
  and `(5²−1)/2 = 12 ≡ 0 (mod 3)`, so `preΨ' 5` is `β`-**invariant**.
* `preΨ' 7` (degree 24, all exponents `≡ 0 (mod 3)`) has `(7²−1)/2 = 24 ≡ 0 (mod 3)`,
  so `preΨ' 7` is `β`-**invariant**.
* `Ψ₂Sq = 4X³ + 28` has exponents `≡ 0 (mod 3)`, hence `β`-**invariant**.

## Why it matters: it explains the failed experiment #100

Experiment #100 tried to distinguish split vs. inert primes with the resultant test
`Res(ψ_l(X), ψ_l(β·X))`. For `l = 5` the map `X ↦ β·X` fixes `preΨ' 5` (it is
`β`-invariant, above), so `ψ₅(β·X) = ψ₅(X)` as polynomials and therefore

  `Res(preΨ' 5(X), preΨ' 5(β·X)) = Res(preΨ' 5, preΨ' 5) = 0`

identically — a resultant of a polynomial with itself vanishes. The test returned `0`
for structural reasons, carrying no arithmetic signal: it was ill-posed, not a real
distinguisher.

Each covariance identity below is a closed field identity, discharged by
`linear_combination` against the cube fact `β³ = 1`; the residual for `Ψ₃` is
`3·β·x⁴·(β³ − 1) = 0`, and for the invariant polynomials each exponent `3k` contributes
`x^{3k}·(β^{3k} − 1) = x^{3k}·(β³ − 1)·(β^{3(k−1)} + ⋯ + 1)`.
-/

namespace Ecdlp.Curve

open Polynomial

/-- The secp256k1 GLV field factor `β` is a cube root of unity: `β³ = 1`.
Derived from the primitive-root eigenvalue `β² + β + 1 = 0` (itself the field lift of
`Secp256k1.beta_field_eigenvalue_kernel`, the kernel-checked twin of
`Secp256k1.beta_field_eigenvalue`) via `Ecdlp.Proved.cube_root_of_eigenvalue`. -/
private theorem secp256k1_beta_cube :
    (Secp256k1.beta : ZMod Secp256k1.p) ^ 3 = 1 := by
  have hβeig : (Secp256k1.beta : ZMod Secp256k1.p) ^ 2
      + (Secp256k1.beta : ZMod Secp256k1.p) + 1 = 0 := by
    have h0 : ((Secp256k1.beta ^ 2 + Secp256k1.beta + 1 : ℕ) : ZMod Secp256k1.p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero Secp256k1.beta_field_eigenvalue_kernel
    push_cast at h0
    linear_combination h0
  exact Ecdlp.Proved.cube_root_of_eigenvalue _ hβeig

/-- **GLV covariance for `Ψ₃`.** `Ψ₃(β·x) = β · Ψ₃(x)`: the scalar is
`β^((3²−1)/2) = β⁴ = β` (since `4 ≡ 1 (mod 3)`). Residual `3·β·x⁴·(β³ − 1) = 0`. -/
theorem secp256k1_Ψ₃_eval_glv (x : ZMod Secp256k1.p) :
    secp256k1.Ψ₃.eval ((Secp256k1.beta : ZMod Secp256k1.p) * x)
      = (Secp256k1.beta : ZMod Secp256k1.p) * secp256k1.Ψ₃.eval x := by
  have hβ3 := secp256k1_beta_cube
  rw [secp256k1_Ψ₃_eval, secp256k1_Ψ₃_eval]
  set b : ZMod Secp256k1.p := (Secp256k1.beta : ZMod Secp256k1.p)
  linear_combination (3 * b * x ^ 4) * hβ3

/-- **GLV covariance for `Ψ₂Sq`.** `Ψ₂Sq(β·x) = Ψ₂Sq(x)`: `Ψ₂Sq` is `β`-invariant
(all exponents `≡ 0 (mod 3)`). Residual `4·x³·(β³ − 1) = 0`. -/
theorem secp256k1_Ψ₂Sq_eval_glv_invariant (x : ZMod Secp256k1.p) :
    secp256k1.Ψ₂Sq.eval ((Secp256k1.beta : ZMod Secp256k1.p) * x)
      = secp256k1.Ψ₂Sq.eval x := by
  have hβ3 := secp256k1_beta_cube
  rw [secp256k1_Ψ₂Sq_eval, secp256k1_Ψ₂Sq_eval]
  set b : ZMod Secp256k1.p := (Secp256k1.beta : ZMod Secp256k1.p)
  linear_combination (4 * x ^ 3) * hβ3

/-- **GLV covariance for `preΨ' 5`.** `preΨ' 5(β·x) = preΨ' 5(x)`: it is `β`-invariant
(`(5²−1)/2 = 12 ≡ 0 (mod 3)`, all exponents `≡ 0 (mod 3)`). This is the algebraic reason
the resultant test of experiment #100 was ill-posed for `l = 5`. -/
theorem secp256k1_preΨ₅_eval_glv_invariant (x : ZMod Secp256k1.p) :
    (secp256k1.preΨ' 5).eval ((Secp256k1.beta : ZMod Secp256k1.p) * x)
      = (secp256k1.preΨ' 5).eval x := by
  have hβ3 := secp256k1_beta_cube
  rw [secp256k1_preΨ₅]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat]
  set b : ZMod Secp256k1.p := (Secp256k1.beta : ZMod Secp256k1.p)
  linear_combination
    (5 * x ^ 12 * (b ^ 9 + b ^ 6 + b ^ 3 + 1)
      + 2660 * x ^ 9 * (b ^ 6 + b ^ 3 + 1)
      - 11760 * x ^ 6 * (b ^ 3 + 1)
      - 548800 * x ^ 3) * hβ3

/-- **GLV covariance for `preΨ' 7`.** `preΨ' 7(β·x) = preΨ' 7(x)`: it is `β`-invariant
(`(7²−1)/2 = 24 ≡ 0 (mod 3)`, all exponents `≡ 0 (mod 3)`). The degree-24 analogue of the
`l = 5` case. -/
theorem secp256k1_preΨ₇_eval_glv_invariant (x : ZMod Secp256k1.p) :
    (secp256k1.preΨ' 7).eval ((Secp256k1.beta : ZMod Secp256k1.p) * x)
      = (secp256k1.preΨ' 7).eval x := by
  have hβ3 := secp256k1_beta_cube
  rw [secp256k1_preΨ₇]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat]
  set b : ZMod Secp256k1.p := (Secp256k1.beta : ZMod Secp256k1.p)
  linear_combination
    (7 * x ^ 24 * (b ^ 21 + b ^ 18 + b ^ 15 + b ^ 12 + b ^ 9 + b ^ 6 + b ^ 3 + 1)
      + 27608 * x ^ 21 * (b ^ 18 + b ^ 15 + b ^ 12 + b ^ 9 + b ^ 6 + b ^ 3 + 1)
      - 2101904 * x ^ 18 * (b ^ 15 + b ^ 12 + b ^ 9 + b ^ 6 + b ^ 3 + 1)
      - 284585728 * x ^ 15 * (b ^ 12 + b ^ 9 + b ^ 6 + b ^ 3 + 1)
      - 2228742656 * x ^ 12 * (b ^ 9 + b ^ 6 + b ^ 3 + 1)
      - 26142548992 * x ^ 9 * (b ^ 6 + b ^ 3 + 1)
      - 330576748544 * x ^ 6 * (b ^ 3 + 1)
      - 661153497088 * x ^ 3) * hβ3

end Ecdlp.Curve