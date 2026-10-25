import Mathlib
import Ecdlp.Proved.DivisionPolynomial
import Ecdlp.Proved.DivisionPolynomialDegree
import Ecdlp.Proved.ThreeTorsion
import Ecdlp.Proved.FiveTorsion
import Ecdlp.Proved.SevenTorsion
import Ecdlp.Proved.ElevenTorsion
import Ecdlp.Proved.ThirteenTorsion
import Ecdlp.Proved.OddTorsionBound
import Ecdlp.Proved.CoprimePsi3Psi5
import Ecdlp.Proved.CoprimePsi3Psi7

/-!
# FBL-PURE-008 — compressed division polynomials (structural core)

> **STATUS: kernel-verified.** Drafted with the Kimi K3 proof-drafter (PR #218), then
> accepted by the Lean kernel in CI (`build` green) and imported into `Ecdlp.lean` — it is
> part of the built, completeness-gated base (Lean v4.31.0, `mathlib4 @
> fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`). No axioms beyond the trusted base; the concrete
> `m ∈ {5,7,9,11,13}` results inherit `Lean.ofReduceBool` from the `native_decide` degree facts.
> The `m = 3` form `secp256k1_Ψ₃_compressed` does not: its degree fact
> `secp256k1_Ψ₃_natDegree` is checked by `decide +kernel`.

## The claim (FBL-PURE-008)

For odd `m`, the `m`-division polynomial `ψ_m` is supported on a single residue class of
exponents mod 3, so there is a "compressed" polynomial `R_m` with

* `ψ_m(X) = R_m(X³)`      when `3 ∤ m`   (support ≡ 0 mod 3), and
* `ψ_m(X) = X · R_m(X³)`  when `3 ∣ m`   (support ≡ 1 mod 3),

with `deg R_m = (m²−1)/6` (`3 ∤ m`) resp. `(m²−3)/6` (`3 ∣ m`).

## What is genuinely provable here (honest scoping)

The **compressed form is a structural consequence of cube-covariance**, and that structural
implication is proved here in full generality over any field carrying a primitive cube root
`β` (`β³ = 1`, `β ≠ 1`):

  if `p(βX) = c·p(X)` as *polynomials*, every exponent `k ∈ support p` has `β^k = c`,
  hence (c = 1)  `p ∈ F[X³]`  and (c = β)  `p ∈ X·F[X³]`, with `3·deg R = deg p`
  resp. `3·deg R + 1 = deg p`.

This is `exists_comp_X_pow_of_invariant` / `exists_X_mul_comp_of_covariant` below — the
reusable, foundation-free heart of the task.

Applying it to a *specific* `ψ_m` needs the **polynomial** cube-covariance identity for that
`ψ_m`. For `m ∈ {3,5,7}` we bypass it: the concrete forms `secp256k1_Ψ₃` / `secp256k1_preΨ₅`
/ `secp256k1_preΨ₇` are in the repo, so `R_m` is exhibited and `deg R_m` read off the proved
`deg ψ_m`. For `m ∈ {9,11,13}` no concrete form exists and the general polynomial covariance
is **not** in the repo/Mathlib; the compressed form for those is therefore stated *conditional
on* the covariance hypothesis (`…_compressed_of_invariant` / `…_of_covariant`), which is the
smallest missing lemma. Their bare degrees `deg ψ_9 = 40`, `deg ψ_11 = 60`, `deg ψ_13 = 84`
are unconditional.

### Verdict table
| item | status | reason |
|---|---|---|
| general compressed form from covariance | PROVABLE-NOW | pure algebra (this file) |
| general `deg R_m` closed form | REDUCES to covariance | `deg ψ_m` proved; covariance missing |
| `m = 3,5,7` compressed + `deg R_m` | PROVABLE-NOW | concrete forms in repo |
| `m = 9,11,13` `deg ψ_m` | PROVABLE-NOW | `natDegree_preΨ'` |
| `m = 9,11,13` compressed + `deg R_m` | conditional on covariance | no concrete form |

**Missing foundation (isolated):** a *polynomial-level* covariance
`(secp256k1.preΨ' m).comp (C β * X) = C (β^((m²−1)/2)) * secp256k1.preΨ' m` for all odd `m`
(with `β` the secp256k1 primitive cube root). The repo only has the `eval`-level version, and
only for `m ∈ {3,5,7}` (`GlvDivPoly.lean`). No axioms; no incomplete proofs (nothing stubbed).
-/

namespace Ecdlp.Curve

open Polynomial

/-! ## §1  Structural core: cube-covariance ⇒ compressed form (any field with a cube root) -/

section CubeCovariance

variable {F : Type*} [Field F] {β : F}

/-- Composition with the dilation `X ↦ β·X` multiplies the `k`-th coefficient by `β^k`. -/
private lemma coeff_comp_C_mul_X (p : F[X]) (k : ℕ) :
    (p.comp (C β * X)).coeff k = β ^ k * p.coeff k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [add_comp, coeff_add, hp, hq, mul_add]
  | monomial n a =>
    rw [monomial_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, C_mul_X_pow_eq_monomial]
    simp only [coeff_monomial]
    split_ifs with h
    · rw [h]; ring
    · ring

/-- `β^k` depends only on `k mod 3` (as `β³ = 1`). -/
private lemma beta_pow_mod (hβ3 : β ^ 3 = 1) (k : ℕ) : β ^ k = β ^ (k % 3) := by
  have h : β ^ (k % 3 + 3 * (k / 3)) = β ^ (k % 3) := by
    rw [pow_add, pow_mul, hβ3, one_pow, mul_one]
  rw [← h, Nat.mod_add_div]

/-- A primitive cube root is nonzero. -/
private lemma beta_ne_zero (hβ3 : β ^ 3 = 1) : β ≠ 0 := by
  intro h
  have h1 : (1 : F) = 0 := by rw [← hβ3, h]; ring
  exact one_ne_zero h1

/-- `β² ≠ 1` for a primitive cube root (else `β = β³ = 1`). -/
private lemma beta_sq_ne_one (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) : β ^ 2 ≠ 1 := by
  intro h
  apply hβ1
  have h1 : β ^ 3 = β := by
    calc β ^ 3 = β ^ 2 * β := by ring
      _ = 1 * β := by rw [h]
      _ = β := by ring
  rw [hβ3] at h1
  exact h1.symm

/-- `β² ≠ β` for a primitive cube root (else `β = 1`). -/
private lemma beta_sq_ne_beta (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) : β ^ 2 ≠ β := by
  intro h
  rw [pow_two] at h
  apply hβ1
  have h' : β * β = β * 1 := by rw [mul_one]; exact h
  exact mul_left_cancel₀ (beta_ne_zero hβ3) h'

/-- For a primitive cube root, `β^k = 1 ↔ 3 ∣ k`. -/
private lemma pow_eq_one_iff_three_dvd (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) (k : ℕ) :
    β ^ k = 1 ↔ 3 ∣ k := by
  constructor
  · intro h
    rw [beta_pow_mod hβ3 k] at h
    rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with hm | hm | hm
    · omega
    · rw [hm, pow_one] at h; exact absurd h hβ1
    · rw [hm] at h; exact absurd h (beta_sq_ne_one hβ3 hβ1)
  · rintro ⟨j, rfl⟩
    rw [beta_pow_mod hβ3, Nat.mul_mod_right, pow_zero]

/-- For a primitive cube root, `β^k = β ↔ k ≡ 1 (mod 3)`. -/
private lemma pow_eq_beta_iff_mod (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) (k : ℕ) :
    β ^ k = β ↔ k % 3 = 1 := by
  rw [beta_pow_mod hβ3 k]
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with hm | hm | hm <;> rw [hm]
  · refine iff_of_false ?_ (by omega)
    rw [pow_zero]; exact fun hh => hβ1 hh.symm
  · exact iff_of_true (by rw [pow_one]) rfl
  · exact iff_of_false (beta_sq_ne_beta hβ3 hβ1) (by omega)

/-- **Support law.** If `p(βX) = c·p(X)` as polynomials, every support exponent obeys
`β^k = c`. Pure coefficient comparison; needs only that `F` has no zero divisors. -/
theorem cube_covariant_support {p : F[X]} {c : F}
    (hcov : p.comp (C β * X) = C c * p) (k : ℕ) (hk : k ∈ p.support) : β ^ k = c := by
  have hco : (p.comp (C β * X)).coeff k = (C c * p).coeff k := by rw [hcov]
  rw [coeff_comp_C_mul_X, coeff_C_mul] at hco
  exact mul_right_cancel₀ (mem_support_iff.mp hk) hco

/-- If `p` is supported on multiples of 3, then `p = expand F 3 (contract 3 p)`. -/
private lemma eq_expand_contract_of_support {p : F[X]}
    (h : ∀ n, ¬ (3 ∣ n) → p.coeff n = 0) : p = expand F 3 (contract 3 p) := by
  ext n
  rw [coeff_expand (by norm_num : 0 < 3), coeff_contract (by norm_num : (3 : ℕ) ≠ 0)]
  split_ifs with hn
  · rw [Nat.div_mul_cancel hn]
  · exact h n hn

/-- Support on multiples of 3 ⇒ `p = R(X³)` with `deg p = 3·deg R`. -/
private lemma compressed_of_support {p : F[X]} (h : ∀ n, ¬ (3 ∣ n) → p.coeff n = 0) :
    ∃ R : F[X], p = R.comp (X ^ 3) ∧ p.natDegree = 3 * R.natDegree := by
  refine ⟨contract 3 p, ?_, ?_⟩
  · rw [← expand_eq_comp_X_pow]; exact eq_expand_contract_of_support h
  · have hd := natDegree_expand 3 (contract 3 p)
    rw [← eq_expand_contract_of_support h] at hd
    omega

/-- Support on `{n ≡ 1 mod 3}` ⇒ `p = X·R(X³)`, with `deg p = 3·deg R + 1` when `p ≠ 0`. -/
private lemma X_mul_compressed_of_support {p : F[X]} (h0 : p.coeff 0 = 0)
    (h : ∀ n, ¬ (3 ∣ n) → (divX p).coeff n = 0) :
    ∃ R : F[X], p = X * R.comp (X ^ 3) ∧ (p ≠ 0 → p.natDegree = 3 * R.natDegree + 1) := by
  have hpX : X * divX p = p := by
    have hx := X_mul_divX_add p
    rwa [h0, C_0, add_zero] at hx
  obtain ⟨R, hR, hdeg⟩ := compressed_of_support h
  refine ⟨R, ?_, ?_⟩
  · rw [← hpX, hR]
  · intro hpne
    have hdivne : divX p ≠ 0 := by
      intro hd; apply hpne; rw [← hpX, hd, mul_zero]
    rw [← hpX, natDegree_X_mul hdivne, hdeg]

/-- **Compressed form, invariant case (`c = 1`).** If `p(βX) = p(X)`, then `p ∈ F[X³]`. -/
theorem exists_comp_X_pow_of_invariant (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) {p : F[X]}
    (hcov : p.comp (C β * X) = p) :
    ∃ R : F[X], p = R.comp (X ^ 3) ∧ p.natDegree = 3 * R.natDegree := by
  have hcov' : p.comp (C β * X) = C 1 * p := by rw [C_1, one_mul]; exact hcov
  have hsupp : ∀ n, ¬ (3 ∣ n) → p.coeff n = 0 := by
    intro n hn
    by_contra hne
    exact hn ((pow_eq_one_iff_three_dvd hβ3 hβ1 n).mp
      (cube_covariant_support hcov' n (mem_support_iff.mpr hne)))
  exact compressed_of_support hsupp

/-- **Compressed form, covariant case (`c = β`).** If `p(βX) = β·p(X)`, then `p ∈ X·F[X³]`. -/
theorem exists_X_mul_comp_of_covariant (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) {p : F[X]}
    (hcov : p.comp (C β * X) = C β * p) :
    ∃ R : F[X], p = X * R.comp (X ^ 3) ∧ (p ≠ 0 → p.natDegree = 3 * R.natDegree + 1) := by
  have hsupp1 : ∀ k ∈ p.support, k % 3 = 1 := fun k hk =>
    (pow_eq_beta_iff_mod hβ3 hβ1 k).mp (cube_covariant_support hcov k hk)
  have h0 : p.coeff 0 = 0 := by
    by_contra hne
    have := hsupp1 0 (mem_support_iff.mpr hne)
    omega
  have hdiv : ∀ n, ¬ (3 ∣ n) → (divX p).coeff n = 0 := by
    intro n hn
    by_contra hne
    rw [coeff_divX] at hne
    have h1 := hsupp1 (n + 1) (mem_support_iff.mpr hne)
    exact hn (by omega)
  exact X_mul_compressed_of_support h0 hdiv

end CubeCovariance

/-! ## §2  Specific `m ∈ {3,5,7}`: unconditional compressed form + `deg R_m` (concrete forms) -/

/-- **`m = 3` (`3 ∣ 3`).** `Ψ₃ = X · R₃(X³)` with `R₃ = 3X + 84`, `deg R₃ = 1 = (3²−3)/6`. -/
theorem secp256k1_Ψ₃_compressed :
    ∃ R : (ZMod Secp256k1.p)[X],
      secp256k1.Ψ₃ = X * R.comp (X ^ 3) ∧ R.natDegree = 1 := by
  set R : (ZMod Secp256k1.p)[X] := 3 * X + 84 with hRdef
  have heq : secp256k1.Ψ₃ = X * R.comp (X ^ 3) := by
    rw [secp256k1_Ψ₃, hRdef, ← expand_eq_comp_X_pow]
    simp only [map_add, map_mul, map_ofNat, expand_X]
    ring
  refine ⟨R, heq, ?_⟩
  have hcompne : R.comp (X ^ 3) ≠ 0 := fun hz => secp256k1_Ψ₃_ne_zero (by rw [heq, hz, mul_zero])
  have hdeg : secp256k1.Ψ₃.natDegree = R.natDegree * 3 + 1 := by
    rw [heq, natDegree_X_mul hcompne, ← expand_eq_comp_X_pow, natDegree_expand]
  rw [secp256k1_Ψ₃_natDegree] at hdeg
  omega

/-- **`m = 5` (`3 ∤ 5`).** `ψ₅ = R₅(X³)` with `deg R₅ = 4 = (5²−1)/6`. -/
theorem secp256k1_preΨ₅_compressed :
    ∃ R : (ZMod Secp256k1.p)[X],
      secp256k1.preΨ' 5 = R.comp (X ^ 3) ∧ R.natDegree = 4 := by
  set R : (ZMod Secp256k1.p)[X] :=
    5 * X ^ 4 + 2660 * X ^ 3 - 11760 * X ^ 2 - 548800 * X - 614656 with hRdef
  have heq : secp256k1.preΨ' 5 = R.comp (X ^ 3) := by
    rw [secp256k1_preΨ₅, hRdef, ← expand_eq_comp_X_pow]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, expand_X]
    ring
  refine ⟨R, heq, ?_⟩
  have hdeg : (secp256k1.preΨ' 5).natDegree = R.natDegree * 3 := by
    rw [heq, ← expand_eq_comp_X_pow, natDegree_expand]
  rw [secp256k1_preΨ₅_natDegree] at hdeg
  omega

/-- **`m = 7` (`3 ∤ 7`).** `ψ₇ = R₇(X³)` with `deg R₇ = 8 = (7²−1)/6`. -/
theorem secp256k1_preΨ₇_compressed :
    ∃ R : (ZMod Secp256k1.p)[X],
      secp256k1.preΨ' 7 = R.comp (X ^ 3) ∧ R.natDegree = 8 := by
  set R : (ZMod Secp256k1.p)[X] :=
    7 * X ^ 8 + 27608 * X ^ 7 - 2101904 * X ^ 6 - 284585728 * X ^ 5 - 2228742656 * X ^ 4
      - 26142548992 * X ^ 3 - 330576748544 * X ^ 2 - 661153497088 * X + 377801998336 with hRdef
  have heq : secp256k1.preΨ' 7 = R.comp (X ^ 3) := by
    rw [secp256k1_preΨ₇, hRdef, ← expand_eq_comp_X_pow]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, expand_X]
    ring
  refine ⟨R, heq, ?_⟩
  have hdeg : (secp256k1.preΨ' 7).natDegree = R.natDegree * 3 := by
    rw [heq, ← expand_eq_comp_X_pow, natDegree_expand]
  rw [secp256k1_preΨ₇_natDegree] at hdeg
  omega

/-! ## §3  Specific `m ∈ {9,11,13}`: unconditional degrees + covariance-conditional compression -/

/-- **`deg (preΨ' 9) = 40`** (unconditional), mirroring `Eleven/ThirteenTorsion.lean`. -/
theorem secp256k1_preΨ₉_natDegree : (secp256k1.preΨ' 9).natDegree = 40 := by
  have h9 : ((9 : ℕ) : ZMod Secp256k1.p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; native_decide
  rw [secp256k1.natDegree_preΨ' h9]
  decide

/-- `preΨ' 9 ≠ 0` (it has degree 40). -/
theorem secp256k1_preΨ₉_ne_zero : secp256k1.preΨ' 9 ≠ 0 := by
  intro h
  have h40 : (secp256k1.preΨ' 9).natDegree = 40 := secp256k1_preΨ₉_natDegree
  rw [h, natDegree_zero] at h40
  exact absurd h40 (by norm_num)

/-- **General reduction, `3 ∤ m` branch.** Given a primitive cube root `β` and the (missing)
`β`-invariance of `ψ_m`, the compressed form holds with `3·deg R_m = (m²−1)/2 = deg ψ_m`.
This isolates exactly the covariance foundation; everything else is discharged. -/
theorem preΨ'_compressed_of_invariant {m : ℕ} (hodd : ¬ Even m)
    (hmp : ((m : ℕ) : ZMod Secp256k1.p) ≠ 0)
    {β : ZMod Secp256k1.p} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1)
    (hcov : (secp256k1.preΨ' m).comp (C β * X) = secp256k1.preΨ' m) :
    ∃ R : (ZMod Secp256k1.p)[X],
      secp256k1.preΨ' m = R.comp (X ^ 3) ∧ 3 * R.natDegree = (m ^ 2 - 1) / 2 := by
  obtain ⟨R, hR, hdeg⟩ := exists_comp_X_pow_of_invariant hβ3 hβ1 hcov
  refine ⟨R, hR, ?_⟩
  rw [← hdeg]; exact secp256k1_odd_preΨ_natDegree hodd hmp

/-- **General reduction, `3 ∣ m` branch.** Given a primitive cube root `β` and the (missing)
`β`-covariance `ψ_m(βX) = β·ψ_m(X)`, the compressed form holds with
`3·deg R_m + 1 = (m²−1)/2 = deg ψ_m`. -/
theorem preΨ'_compressed_of_covariant {m : ℕ} (hodd : ¬ Even m)
    (hmp : ((m : ℕ) : ZMod Secp256k1.p) ≠ 0)
    {β : ZMod Secp256k1.p} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1)
    (hcov : (secp256k1.preΨ' m).comp (C β * X) = C β * secp256k1.preΨ' m) :
    ∃ R : (ZMod Secp256k1.p)[X],
      secp256k1.preΨ' m = X * R.comp (X ^ 3) ∧ 3 * R.natDegree + 1 = (m ^ 2 - 1) / 2 := by
  obtain ⟨R, hR, hdeg⟩ := exists_X_mul_comp_of_covariant hβ3 hβ1 hcov
  refine ⟨R, hR, ?_⟩
  have hne : secp256k1.preΨ' m ≠ 0 := secp256k1.preΨ'_ne_zero hmp
  have hd := hdeg hne
  rw [secp256k1_odd_preΨ_natDegree hodd hmp] at hd
  omega

/-- **`m = 11` (`3 ∤ 11`), conditional on `β`-invariance.** `deg R₁₁ = 20 = (11²−1)/6`. -/
theorem secp256k1_preΨ₁₁_compressed_of_invariant
    {β : ZMod Secp256k1.p} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1)
    (hcov : (secp256k1.preΨ' 11).comp (C β * X) = secp256k1.preΨ' 11) :
    ∃ R : (ZMod Secp256k1.p)[X],
      secp256k1.preΨ' 11 = R.comp (X ^ 3) ∧ R.natDegree = 20 := by
  obtain ⟨R, hR, hdeg⟩ := exists_comp_X_pow_of_invariant hβ3 hβ1 hcov
  refine ⟨R, hR, ?_⟩
  rw [secp256k1_preΨ₁₁_natDegree] at hdeg
  omega

/-- **`m = 13` (`3 ∤ 13`), conditional on `β`-invariance.** `deg R₁₃ = 28 = (13²−1)/6`. -/
theorem secp256k1_preΨ₁₃_compressed_of_invariant
    {β : ZMod Secp256k1.p} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1)
    (hcov : (secp256k1.preΨ' 13).comp (C β * X) = secp256k1.preΨ' 13) :
    ∃ R : (ZMod Secp256k1.p)[X],
      secp256k1.preΨ' 13 = R.comp (X ^ 3) ∧ R.natDegree = 28 := by
  obtain ⟨R, hR, hdeg⟩ := exists_comp_X_pow_of_invariant hβ3 hβ1 hcov
  refine ⟨R, hR, ?_⟩
  rw [secp256k1_preΨ₁₃_natDegree] at hdeg
  omega

/-- **`m = 9` (`3 ∣ 9`), conditional on `β`-covariance.** `deg R₉ = 13 = (9²−3)/6`. -/
theorem secp256k1_preΨ₉_compressed_of_covariant
    {β : ZMod Secp256k1.p} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1)
    (hcov : (secp256k1.preΨ' 9).comp (C β * X) = C β * secp256k1.preΨ' 9) :
    ∃ R : (ZMod Secp256k1.p)[X],
      secp256k1.preΨ' 9 = X * R.comp (X ^ 3) ∧ R.natDegree = 13 := by
  obtain ⟨R, hR, hdeg⟩ := exists_X_mul_comp_of_covariant hβ3 hβ1 hcov
  refine ⟨R, hR, ?_⟩
  have hd := hdeg secp256k1_preΨ₉_ne_zero
  rw [secp256k1_preΨ₉_natDegree] at hd
  omega

end Ecdlp.Curve
