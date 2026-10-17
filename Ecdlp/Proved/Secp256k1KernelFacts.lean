import Ecdlp.Secp256k1Verified

/-!
# Kernel-checked twins of the secp256k1 literal facts

`Ecdlp/Secp256k1Verified.lean` proves nine closed 256-bit facts about the secp256k1
constants (`p`, `n`, `λ`, `β`, `G`) with `native_decide`, so each of them depends on
`Lean.ofReduceBool`. That file is kept byte-for-byte unchanged: its SHA-256 is pinned as an
upstream binding of a committed research artifact
(`experiments/engine/pkc_smooth_m16_regime_assurance_desk`).

This file re-proves exactly the same nine statements under new names (suffix `_kernel`)
with `decide +kernel`: the kernel evaluates the closed `Nat` arithmetic itself, using its
built-in arbitrary-precision natural-number operations. No axiom and no compiler trust is
added; `#print axioms` on each twin shows only `propext`, `Classical.choice`, `Quot.sound`
(or nothing).

The twins are infrastructure, not new results: they carry no ledger rows of their own.
Downstream proofs that must stay kernel-only (the primality certificates, `#E(𝔽_p) = n`,
`E(𝔽_p) ≃+ ℤ/n`, the GLV `[λ]` corollaries) use these twins instead of the
`native_decide` originals.
-/

namespace Secp256k1

/-- Kernel-checked twin of `Secp256k1.p_special_form`. -/
theorem p_special_form_kernel : p = 2^256 - 2^32 - 977 := by decide +kernel

/-- Kernel-checked twin of `Secp256k1.glv_lambda_eigenvalue`. -/
theorem glv_lambda_eigenvalue_kernel : (lam^2 + lam + 1) % n = 0 := by decide +kernel

/-- Kernel-checked twin of `Secp256k1.lambda_is_cube_root`. -/
theorem lambda_is_cube_root_kernel : lam^3 % n = 1 := by decide +kernel

/-- Kernel-checked twin of `Secp256k1.lambda_ne_one`. -/
theorem lambda_ne_one_kernel : lam ≠ 1 := by decide +kernel

/-- Kernel-checked twin of `Secp256k1.beta_field_eigenvalue`. -/
theorem beta_field_eigenvalue_kernel : (beta^2 + beta + 1) % p = 0 := by decide +kernel

/-- Kernel-checked twin of `Secp256k1.beta_is_cube_root`. -/
theorem beta_is_cube_root_kernel : beta^3 % p = 1 := by decide +kernel

/-- Kernel-checked twin of `Secp256k1.lam_lt_n`. -/
theorem lam_lt_n_kernel : lam < n := by decide +kernel

/-- Kernel-checked twin of `Secp256k1.beta_lt_p`. -/
theorem beta_lt_p_kernel : beta < p := by decide +kernel

/-- Kernel-checked twin of `Secp256k1.generator_on_curve`: the secp256k1 base point
`G = (Gx, Gy)` satisfies `y² = x³ + 7` (mod `p`). -/
theorem generator_on_curve_kernel : (Gy ^ 2) % p = (Gx ^ 3 + 7) % p := by decide +kernel

end Secp256k1
