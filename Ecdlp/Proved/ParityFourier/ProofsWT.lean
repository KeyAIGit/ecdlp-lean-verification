import Mathlib
import Ecdlp.Proved.ParityFourier.StatementsWT
import Ecdlp.Proved.ParityFourier.ProofsC44
import Ecdlp.Proved.ParityFourier.ProofsC44L

/-!
# Proofs of WT and WT-lsb (the Weil-transfer layer)

Proves the frozen statements `Ecdlp.ParityFourier.WeilTransfer` and
`Ecdlp.ParityFourier.WeilTransferLsb` from `Ecdlp.ParityFourier.StatementsWT`.

Outline (with `e = ZMod.stdAddChar`):
1. `eChar = e` (periodicity of the exponential);
2. Fourier inversion (`ProofsC44.inversion`) for `b` and `T` turns the
   correlation into `b̂(0) ∑_{k ≠ 0} T k + ∑_{a ≠ 0} b̂(a) ∑_α T̂(α) twistedSum V a α`,
   and the triangle inequality with the hypothesis gives WT;
3. for WT-lsb: `∑_{k ≠ 0} sigma k = 0` for odd `n`, and
   `∑_a |sigma_hat a| ≤ L1low m ((m - 1)/2) ≤ 2 + log m` (`ProofsC44L.l1lowBound`).
-/

namespace Ecdlp.ParityFourier.ProofsWT

open Ecdlp.ParityFourier Finset

local notation "𝐞" => ZMod.stdAddChar

section Basic

variable {m : ℕ} [NeZero m]

lemma eChar_eq (x : ZMod m) : eChar x = 𝐞 x := by
  unfold eChar
  conv_rhs => rw [← ZMod.natCast_zmod_val x, ← Int.cast_natCast (R := ZMod m)]
  rw [ZMod.stdAddChar_coe]
  congr 1

end Basic

theorem weilTransfer : Ecdlp.ParityFourier.WeilTransfer := by
  intro n p _ _ V b T C hC
  set E := (univ.erase (0 : ZMod n)) with hE
  -- expansion of each frequency `a`
  have key : ∀ a : ZMod p, ∑ k ∈ E, ft b a * 𝐞 (a * V k) * T k
      = ft b a * ∑ α : ZMod n, ft T α * twistedSum V a α := by
    intro a
    unfold twistedSum
    simp_rw [eChar_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_lhs => rw [ProofsC44.inversion T k]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  have hS : ∑ k ∈ E, b (V k) * T k
      = ft b 0 * ∑ k ∈ E, T k +
          ∑ a ∈ (univ.erase (0 : ZMod p)), ft b a * ∑ α : ZMod n, ft T α * twistedSum V a α := by
    have h1 : ∑ k ∈ E, b (V k) * T k = ∑ a : ZMod p, ∑ k ∈ E, ft b a * 𝐞 (a * V k) * T k := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [ProofsC44.inversion b (V k)]
      rw [Finset.sum_mul]
    rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp
    · exact Finset.sum_congr rfl fun a _ => key a
  rw [hS]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul]
  gcongr
  have hT : ∀ a ∈ (univ.erase (0 : ZMod p)),
      ‖ft b a * ∑ α : ZMod n, ft T α * twistedSum V a α‖
        ≤ ‖ft b a‖ * ((∑ α : ZMod n, ‖ft T α‖) * C) := by
    intro a ha
    have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
    rw [norm_mul]
    gcongr
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_mul]
    gcongr with α _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC a ha0 α) (norm_nonneg _)
  refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hT) (le_of_eq ?_))
  rw [← Finset.sum_mul]
  ring

section Lsb

variable {m : ℕ} [NeZero m]

/-- For odd `m`, the parity sign sums to zero over the nonzero residues. -/
lemma sum_sigma_erase (hodd : Odd m) : ∑ k ∈ (univ.erase (0 : ZMod m)), sigmaC k = 0 := by
  have hall : ∑ k : ZMod m, sigmaC k = 1 := by
    have h1 : ∑ k : ZMod m, sigmaC k = ∑ i ∈ range m, (-1 : ℂ) ^ i := by
      unfold sigmaC
      refine Finset.sum_nbij (fun k : ZMod m => k.val) ?_ ?_ ?_ ?_
      · intro k _
        exact Finset.mem_range.2 (ZMod.val_lt k)
      · intro a _ b _ hab
        exact ZMod.val_injective m hab
      · intro i hi
        exact ⟨(i : ZMod m), by simp, ZMod.val_cast_of_lt (by simpa using hi)⟩
      · intro k _
        rfl
    rw [h1, geom_sum_eq (by norm_num : (-1 : ℂ) ≠ 1), hodd.neg_one_pow]
    norm_num
  have h0 := Finset.add_sum_erase (univ : Finset (ZMod m)) (sigmaC (n := m)) (mem_univ 0)
  rw [hall] at h0
  have hs0 : sigmaC (0 : ZMod m) = 1 := by simp [sigmaC]
  rw [hs0] at h0
  linear_combination h0

/-- For odd `m`, the full L1 norm of `ft sigma` is at most `2 + log m`. -/
lemma sum_ft_sigma_le (hodd : Odd m) :
    ∑ a : ZMod m, ‖ft (sigmaC (n := m)) a‖ ≤ 2 + Real.log m := by
  set B := (m - 1) / 2 with hB
  have hBm : 2 * B + 1 = m := by
    obtain ⟨j, hj⟩ := hodd
    omega
  have hcov : (univ : Finset (ZMod m)) = (window B).image (fun t : ℤ => hC m + (t : ZMod m)) := by
    ext a
    simp only [mem_univ, true_iff]
    obtain ⟨t, ht, rfl⟩ := ProofsC44.cover hodd a
    refine Finset.mem_image.2 ⟨t, ?_, rfl⟩
    rw [abs_le] at ht
    simp only [window, mem_Icc]
    exact ht
  have h1 : ∑ a : ZMod m, ‖ft (sigmaC (n := m)) a‖ ≤ L1low m B := by
    rw [hcov]
    unfold L1low
    exact sum_image_le_of_nonneg fun _ _ => norm_nonneg _
  have h2 := ProofsC44L.l1lowBound m hodd B (le_of_eq hBm)
  have h3 : (2 * (B : ℝ) + 1) = (m : ℝ) := by exact_mod_cast hBm
  rw [h3] at h2
  linarith

end Lsb

theorem weilTransferLsb : Ecdlp.ParityFourier.WeilTransferLsb := by
  intro n p _ _ _ _ hn2 hp2 V hV
  have hnodd : Odd n := (Fact.out : n.Prime).odd_of_ne_two hn2
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h := weilTransfer n p V (sigmaC (n := p)) (sigmaC (n := n)) (2 * Real.sqrt p) hV
  rw [sum_sigma_erase hnodd, norm_zero, mul_zero, zero_add] at h
  refine le_trans h ?_
  have hLp : ∑ a ∈ (univ.erase (0 : ZMod p)), ‖ft (sigmaC (n := p)) a‖ ≤ 2 + Real.log p :=
    le_trans (Finset.sum_le_univ_sum_of_nonneg fun _ => norm_nonneg _) (sum_ft_sigma_le hpodd)
  have hLn := sum_ft_sigma_le (m := n) hnodd
  have h0p : 0 ≤ ∑ a ∈ (univ.erase (0 : ZMod p)), ‖ft (sigmaC (n := p)) a‖ :=
    sum_nonneg fun _ _ => norm_nonneg _
  have h0n : 0 ≤ ∑ α : ZMod n, ‖ft (sigmaC (n := n)) α‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hs : 0 ≤ 2 * Real.sqrt p := by positivity
  have hlogp : 0 ≤ 2 + Real.log p := le_trans h0p hLp
  calc 2 * Real.sqrt p * (∑ a ∈ (univ.erase (0 : ZMod p)), ‖ft (sigmaC (n := p)) a‖) *
        (∑ α : ZMod n, ‖ft (sigmaC (n := n)) α‖)
      ≤ 2 * Real.sqrt p * (2 + Real.log p) * (∑ α : ZMod n, ‖ft (sigmaC (n := n)) α‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLp hs) h0n
    _ ≤ 2 * Real.sqrt p * (2 + Real.log p) * (2 + Real.log n) :=
        mul_le_mul_of_nonneg_left hLn (mul_nonneg hs hlogp)

end Ecdlp.ParityFourier.ProofsWT
