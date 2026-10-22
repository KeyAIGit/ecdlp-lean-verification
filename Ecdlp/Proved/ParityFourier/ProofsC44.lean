import Mathlib
import Ecdlp.Proved.ParityFourier.StatementsC44
import Ecdlp.Proved.ParityFourier.StatementsF5
import Ecdlp.Proved.ParityFourier.ProofsF5b

/-!
# Proof of C44-6' (concentration of the ordered-sector sign J)

Proves the frozen statement `Ecdlp.ParityFourier.JConcentration` from
`Ecdlp.ParityFourier.StatementsC44`.

Outline (with `e = ZMod.stdAddChar`, `e a = exp(2 pi i a.val / n)`):
1. the kernel of `ft` is `e (-(β * k))`; orthogonality of `e`, Fourier inversion and
   Parseval on `ZMod n`;
2. `Low = sum_{a ∈ W} ft sigma a * e(a k)` with `W = {h + t : |t| ≤ B}`, `High = sigma - Low`;
   `|Low| ≤ L1low` and the Fourier mass of `High` is the tail of sigma, at most `1/B`
   (bridged to `ProofsF5b.sigmaTail`);
3. `P k = Low(lam k) Low(lam^2 k)` has Fourier support inside `GammaJ`;
4. `J - P = High(lam k) sigma(lam^2 k) + Low(lam k) High(lam^2 k)`, pointwise
   `|J - P|^2 ≤ (1 + L)(x^2 + L y^2)`, and Parseval finishes.
-/

namespace Ecdlp.ParityFourier.ProofsC44

open Ecdlp.ParityFourier Finset

local notation "𝐞" => ZMod.stdAddChar

section Fourier

variable {n : ℕ} [NeZero n]

lemma kernel_eq (β k : ZMod n) :
    Complex.exp (-2 * Real.pi * Complex.I * ((β.val * k.val : ℕ) : ℂ) / (n : ℂ))
      = 𝐞 (-(β * k)) := by
  have h : (-(β * k) : ZMod n) = (((-((β.val * k.val : ℕ) : ℤ)) : ℤ) : ZMod n) := by
    push_cast
    simp
  rw [h, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

lemma ft_eq (f : ZMod n → ℂ) (β : ZMod n) :
    ft f β = (1 / (n : ℂ)) * ∑ k : ZMod n, f k * 𝐞 (-(β * k)) := by
  unfold ft
  simp_rw [kernel_eq]

lemma sum_e (c : ZMod n) :
    ∑ x : ZMod n, 𝐞 (x * c) = if c = 0 then (n : ℂ) else 0 := by
  rw [AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar n), ZMod.card]
  split_ifs <;> simp

lemma norm_e (a : ZMod n) : ‖𝐞 a‖ = 1 := AddChar.norm_apply _ _

lemma conj_e (a : ZMod n) : (starRingEnd ℂ) (𝐞 a) = 𝐞 (-a) :=
  (AddChar.map_neg_eq_conj _ _).symm

lemma ft_sub (f g : ZMod n → ℂ) (γ : ZMod n) :
    ft (fun k => f k - g k) γ = ft f γ - ft g γ := by
  simp only [ft_eq, sub_mul, Finset.sum_sub_distrib, mul_sub]

/-- Fourier coefficients of a trigonometric polynomial. -/
lemma ft_trig {ι : Type*} (s : Finset ι) (c : ι → ℂ) (m : ι → ZMod n) (γ : ZMod n) :
    ft (fun k => ∑ i ∈ s, c i * 𝐞 (m i * k)) γ
      = ∑ i ∈ s, c i * (if m i = γ then 1 else 0) := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [ft_eq]
  have h1 : ∀ k : ZMod n, (∑ i ∈ s, c i * 𝐞 (m i * k)) * 𝐞 (-(γ * k))
      = ∑ i ∈ s, c i * 𝐞 (k * (m i - γ)) := by
    intro k
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, sum_e]
  simp only [sub_eq_zero]
  split_ifs
  · field_simp
  · simp

/-- Fourier inversion on `ZMod n`. -/
lemma inversion (f : ZMod n → ℂ) (k : ZMod n) : f k = ∑ β, ft f β * 𝐞 (β * k) := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have h : ∀ β, ft f β * 𝐞 (β * k) = (1 / (n : ℂ)) * ∑ j, f j * 𝐞 (β * (k - j)) := by
    intro β
    rw [ft_eq, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [h, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_e, sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  field_simp

/-- Parseval on `ZMod n`. -/
lemma parseval (f : ZMod n → ℂ) :
    ∑ β, ‖ft f β‖ ^ 2 = (1 / (n : ℝ)) * ∑ k, ‖f k‖ ^ 2 := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have h1 : ∀ k, (starRingEnd ℂ) (f k) = ∑ β, (starRingEnd ℂ) (ft f β) * 𝐞 (-(β * k)) := by
    intro k
    conv_lhs => rw [inversion f k]
    rw [map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [map_mul, conj_e]
  have hS : ∀ β, ∑ k, f k * 𝐞 (-(β * k)) = (n : ℂ) * ft f β := by
    intro β
    rw [ft_eq]
    field_simp
  have key : ∑ k, f k * (starRingEnd ℂ) (f k)
      = (n : ℂ) * ∑ β, ft f β * (starRingEnd ℂ) (ft f β) := by
    calc ∑ k, f k * (starRingEnd ℂ) (f k)
        = ∑ k, ∑ β, (starRingEnd ℂ) (ft f β) * (f k * 𝐞 (-(β * k))) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [h1 k, Finset.mul_sum]
          refine Finset.sum_congr rfl fun β _ => ?_
          ring
      _ = ∑ β, (starRingEnd ℂ) (ft f β) * ∑ k, f k * 𝐞 (-(β * k)) := by
          rw [Finset.sum_comm]
          simp_rw [Finset.mul_sum]
      _ = ∑ β, (starRingEnd ℂ) (ft f β) * ((n : ℂ) * ft f β) := by
          simp_rw [hS]
      _ = (n : ℂ) * ∑ β, ft f β * (starRingEnd ℂ) (ft f β) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun β _ => ?_
          ring
  simp_rw [Complex.mul_conj'] at key
  have key' : ∑ k, ‖f k‖ ^ 2 = (n : ℝ) * ∑ β, ‖ft f β‖ ^ 2 := by exact_mod_cast key
  rw [key']
  field_simp

lemma ft_sub' (f g : ZMod n → ℂ) (γ : ZMod n) : ft (f - g) γ = ft f γ - ft g γ := by
  simp only [ft_eq, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

end Fourier

section Specific

variable {n : ℕ} [NeZero n]

/-- The low-pass window `W = {h + t : |t| ≤ B}`. -/
noncomputable def Wset (n : ℕ) (B : ℕ) : Finset (ZMod n) :=
  (window B).image (fun t : ℤ => hC n + (t : ZMod n))

/-- Low-pass part of sigma. -/
noncomputable def Low (n : ℕ) [NeZero n] (B : ℕ) (k : ZMod n) : ℂ :=
  ∑ a ∈ Wset n B, ft (sigmaC (n := n)) a * 𝐞 (a * k)

/-- High-pass part of sigma. -/
noncomputable def High (n : ℕ) [NeZero n] (B : ℕ) (k : ZMod n) : ℂ :=
  sigmaC k - Low n B k

omit [NeZero n] in
lemma norm_sigmaC (k : ZMod n) : ‖sigmaC k‖ = 1 := by simp [sigmaC]

lemma L1low_nonneg (B : ℕ) : 0 ≤ L1low n B := sum_nonneg fun _ _ => norm_nonneg _

lemma norm_Low_le (B : ℕ) (k : ZMod n) : ‖Low n B k‖ ≤ L1low n B := by
  unfold Low L1low Wset
  calc ‖∑ a ∈ (window B).image (fun t : ℤ => hC n + (t : ZMod n)),
          ft (sigmaC (n := n)) a * 𝐞 (a * k)‖
      ≤ ∑ a ∈ (window B).image (fun t : ℤ => hC n + (t : ZMod n)),
          ‖ft (sigmaC (n := n)) a * 𝐞 (a * k)‖ := norm_sum_le _ _
    _ = ∑ a ∈ (window B).image (fun t : ℤ => hC n + (t : ZMod n)),
          ‖ft (sigmaC (n := n)) a‖ := by
        refine sum_congr rfl fun a _ => ?_
        rw [norm_mul, norm_e, mul_one]
    _ ≤ ∑ t ∈ window B, ‖ft (sigmaC (n := n)) (hC n + (t : ZMod n))‖ :=
        sum_image_le_of_nonneg fun _ _ => norm_nonneg _

lemma ft_Low (B : ℕ) (γ : ZMod n) :
    ft (Low n B) γ = if γ ∈ Wset n B then ft (sigmaC (n := n)) γ else 0 := by
  have h := ft_trig (Wset n B) (ft (sigmaC (n := n))) (fun a => a) γ
  have e : (fun k => ∑ i ∈ Wset n B, ft (sigmaC (n := n)) i * 𝐞 ((fun a => a) i * k))
      = Low n B := rfl
  rw [e] at h
  rw [h]
  simp [mul_ite]

lemma ft_High (B : ℕ) (γ : ZMod n) :
    ft (High n B) γ = if γ ∈ Wset n B then 0 else ft (sigmaC (n := n)) γ := by
  have e : High n B = fun k => sigmaC k - Low n B k := rfl
  rw [e, ft_sub, ft_Low]
  split_ifs <;> simp

/-- Bridge between `ft sigmaC` and `sigmaHat`. -/
lemma ft_sigma_intCast (z : ℤ) : ft (sigmaC (n := n)) (z : ZMod n) = sigmaHat n z := by
  rw [ft_eq]
  unfold sigmaHat sigmaC
  congr 1
  have hk : ∀ k : ℕ, Complex.exp (-2 * Real.pi * Complex.I * (z : ℂ) * (k : ℂ) / (n : ℂ))
      = 𝐞 (-((z : ZMod n) * (k : ZMod n))) := by
    intro k
    have : (-((z : ZMod n) * (k : ZMod n))) = (((-(z * k)) : ℤ) : ZMod n) := by
      push_cast
      ring
    rw [this, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  simp_rw [hk]
  refine Finset.sum_nbij (fun k : ZMod n => k.val) ?_ ?_ ?_ ?_
  · intro k _
    exact Finset.mem_range.2 (ZMod.val_lt k)
  · intro a _ b _ hab
    exact ZMod.val_injective n hab
  · intro m hm
    exact ⟨(m : ZMod n), by simp, ZMod.val_cast_of_lt (by simpa using hm)⟩
  · intro k _
    simp

/-- Every residue is `h + t` with `|t| ≤ (n - 1) / 2`. -/
lemma cover (hodd : Odd n) (a : ZMod n) :
    ∃ t : ℤ, |t| ≤ (((n - 1) / 2 : ℕ) : ℤ) ∧ a = hC n + (t : ZMod n) := by
  obtain ⟨m, hm⟩ := hodd
  have h1 : (n + 1) / 2 = m + 1 := by omega
  have h2 : (n - 1) / 2 = m := by omega
  unfold hC
  rw [h1, h2]
  by_cases hv : a.val = 0
  · refine ⟨m, by simp, ?_⟩
    rw [(ZMod.val_eq_zero a).1 hv]
    have e : ((m + 1 : ℕ) : ZMod n) + ((m : ℤ) : ZMod n) = (((m + 1 + m : ℕ)) : ZMod n) := by
      push_cast
      ring
    rw [e, show m + 1 + m = n by omega, ZMod.natCast_self]
  · refine ⟨(a.val : ℤ) - (m + 1), ?_, ?_⟩
    · have := ZMod.val_lt a
      rw [abs_le]
      constructor <;> omega
    · conv_lhs => rw [← ZMod.natCast_zmod_val a]
      push_cast
      ring

omit [NeZero n] in
lemma hplus (t : ℤ) : hC n + (t : ZMod n) = (((((n + 1) / 2 : ℕ) : ℤ) + t : ℤ) : ZMod n) := by
  unfold hC
  rw [Int.cast_add, Int.cast_natCast]

omit [NeZero n] in
lemma hminus (t : ℤ) : hC n - (t : ZMod n) = (((((n + 1) / 2 : ℕ) : ℤ) - t : ℤ) : ZMod n) := by
  unfold hC
  rw [Int.cast_sub, Int.cast_natCast]

/-- The Fourier mass of sigma outside the window is at most `1/B`. -/
lemma tail_le (hodd : Odd n) (B : ℕ) (hB : 1 ≤ B) :
    ∑ β ∈ univ \ Wset n B, ‖ft (sigmaC (n := n)) β‖ ^ 2 ≤ 1 / (B : ℝ) := by
  set g : ZMod n → ℝ := fun β => ‖ft (sigmaC (n := n)) β‖ ^ 2 with hg
  have hg0 : ∀ β, 0 ≤ g β := fun β => sq_nonneg _
  set U1 := (Icc (B + 1) ((n - 1) / 2)).image (fun t : ℕ => hC n + ((t : ℤ) : ZMod n)) with hU1
  set U2 := (Icc (B + 1) ((n - 1) / 2)).image (fun t : ℕ => hC n - ((t : ℤ) : ZMod n)) with hU2
  have hsub : univ \ Wset n B ⊆ U1 ∪ U2 := by
    intro a ha
    have haW : a ∉ Wset n B := (Finset.mem_sdiff.1 ha).2
    obtain ⟨t, htM, rfl⟩ := cover hodd a
    by_cases htB : |t| ≤ B
    · exfalso
      apply haW
      exact Finset.mem_image.2 ⟨t, by simpa [window, abs_le] using htB, rfl⟩
    · replace htB := not_le.1 htB
      rcases le_or_gt 0 t with h0 | h0
      · apply Finset.mem_union_left
        refine Finset.mem_image.2 ⟨t.toNat, ?_, ?_⟩
        · rw [abs_of_nonneg h0] at htB htM
          rw [Finset.mem_Icc]
          omega
        · show hC n + (((t.toNat : ℕ) : ℤ) : ZMod n) = hC n + (t : ZMod n)
          rw [Int.toNat_of_nonneg h0]
      · apply Finset.mem_union_right
        refine Finset.mem_image.2 ⟨(-t).toNat, ?_, ?_⟩
        · rw [abs_of_neg h0] at htB htM
          rw [Finset.mem_Icc]
          omega
        · show hC n - ((((-t).toNat : ℕ) : ℤ) : ZMod n) = hC n + (t : ZMod n)
          rw [Int.toNat_of_nonneg (by omega), Int.cast_neg, sub_neg_eq_add]
  calc ∑ β ∈ univ \ Wset n B, g β
      ≤ ∑ β ∈ U1 ∪ U2, g β := sum_le_sum_of_subset_of_nonneg hsub (fun β _ _ => hg0 β)
    _ ≤ ∑ β ∈ U1, g β + ∑ β ∈ U2, g β := by
        have h := sum_union_inter (s₁ := U1) (s₂ := U2) (f := g)
        have h' : 0 ≤ ∑ β ∈ U1 ∩ U2, g β := sum_nonneg fun β _ => hg0 β
        linarith
    _ ≤ ∑ t ∈ Icc (B + 1) ((n - 1) / 2), g (hC n + ((t : ℤ) : ZMod n))
          + ∑ t ∈ Icc (B + 1) ((n - 1) / 2), g (hC n - ((t : ℤ) : ZMod n)) :=
        add_le_add (sum_image_le_of_nonneg fun _ _ => hg0 _)
          (sum_image_le_of_nonneg fun _ _ => hg0 _)
    _ = ∑ t ∈ Icc (B + 1) ((n - 1) / 2),
          (‖sigmaHat n (((n + 1) / 2 : ℕ) + (t : ℤ))‖ ^ 2 +
           ‖sigmaHat n (((n + 1) / 2 : ℕ) - (t : ℤ))‖ ^ 2) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun t _ => ?_
        simp only [hg]
        rw [hplus, hminus, ft_sigma_intCast, ft_sigma_intCast]
    _ ≤ 1 / (B : ℝ) := ProofsF5b.sigmaTail n hodd B hB

lemma high_mass (hodd : Odd n) (B : ℕ) (hB : 1 ≤ B) :
    (1 / (n : ℝ)) * ∑ k, ‖High n B k‖ ^ 2 ≤ 1 / (B : ℝ) := by
  rw [← parseval]
  simp_rw [ft_High]
  have e : ∀ β, ‖(if β ∈ Wset n B then (0 : ℂ) else ft (sigmaC (n := n)) β)‖ ^ 2
      = if β ∈ Wset n B then 0 else ‖ft (sigmaC (n := n)) β‖ ^ 2 := by
    intro β
    split_ifs <;> simp
  simp_rw [e]
  rw [Finset.sum_ite, sum_const_zero, zero_add, ← sdiff_eq_filter]
  exact tail_le hodd B hB

/-- The product of the low-pass parts as a trigonometric polynomial. -/
lemma P_eq (lam : ZMod n) (B : ℕ) :
    (fun k => Low n B (lam * k) * Low n B (lam ^ 2 * k))
      = fun k => ∑ p ∈ Wset n B ×ˢ Wset n B,
          (ft (sigmaC (n := n)) p.1 * ft (sigmaC (n := n)) p.2) *
            𝐞 ((lam * p.1 + lam ^ 2 * p.2) * k) := by
  funext k
  unfold Low
  rw [sum_mul_sum, sum_product]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  dsimp only
  have e : 𝐞 ((lam * a + lam ^ 2 * b) * k) = 𝐞 (a * (lam * k)) * 𝐞 (b * (lam ^ 2 * k)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [e]
  ring

lemma ft_P_zero (lam : ZMod n) (B : ℕ) (γ : ZMod n) (hγ : γ ∉ GammaJ lam B) :
    ft (fun k => Low n B (lam * k) * Low n B (lam ^ 2 * k)) γ = 0 := by
  rw [P_eq, ft_trig]
  refine sum_eq_zero fun p hp => ?_
  rw [if_neg, mul_zero]
  intro heq
  apply hγ
  obtain ⟨hp1, hp2⟩ := mem_product.1 hp
  obtain ⟨t1, ht1, e1⟩ := mem_image.1 hp1
  obtain ⟨t2, ht2, e2⟩ := mem_image.1 hp2
  unfold GammaJ
  refine mem_image.2 ⟨(t1, t2), mem_product.2 ⟨ht1, ht2⟩, ?_⟩
  show lam * (hC n + (t1 : ZMod n)) + lam ^ 2 * (hC n + (t2 : ZMod n)) = γ
  rw [e1, e2]
  exact heq

end Specific

theorem jConcentration : Ecdlp.ParityFourier.JConcentration := by
  intro n _ _ hn2 lam hlam B hB
  have hodd : Odd n := (Fact.out : n.Prime).odd_of_ne_two hn2
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    simp at hlam
  have hlam20 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam0
  have hL0 : 0 ≤ L1low n B := L1low_nonneg B
  set L := L1low n B with hL
  have hTB : (1 / (n : ℝ)) * ∑ k, ‖High n B k‖ ^ 2 ≤ 1 / (B : ℝ) := high_mass hodd B hB
  set T := ∑ k, ‖High n B k‖ ^ 2 with hT
  set Pf : ZMod n → ℂ := fun k => Low n B (lam * k) * Low n B (lam ^ 2 * k) with hPf
  set D : ZMod n → ℂ := JC lam - Pf with hD
  have hfD : ∀ γ ∉ GammaJ lam B, ft (JC lam) γ = ft D γ := by
    intro γ hγ
    rw [hD, ft_sub', hPf, ft_P_zero lam B γ hγ, sub_zero]
  have hsum1 : ∑ γ ∈ univ \ GammaJ lam B, ‖ft (JC lam) γ‖ ^ 2
      ≤ (1 / (n : ℝ)) * ∑ k, ‖D k‖ ^ 2 := by
    rw [← parseval]
    calc ∑ γ ∈ univ \ GammaJ lam B, ‖ft (JC lam) γ‖ ^ 2
        = ∑ γ ∈ univ \ GammaJ lam B, ‖ft D γ‖ ^ 2 :=
          sum_congr rfl fun γ hγ => by rw [hfD γ (mem_sdiff.1 hγ).2]
      _ ≤ ∑ γ, ‖ft D γ‖ ^ 2 := sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
  have hpt : ∀ k, ‖D k‖ ^ 2
      ≤ (1 + L) * (‖High n B (lam * k)‖ ^ 2 + L * ‖High n B (lam ^ 2 * k)‖ ^ 2) := by
    intro k
    have hDk : D k = High n B (lam * k) * sigmaC (lam ^ 2 * k)
        + Low n B (lam * k) * High n B (lam ^ 2 * k) := by
      simp only [hD, hPf, Pi.sub_apply, High, JC]
      ring
    have hle : ‖D k‖ ≤ ‖High n B (lam * k)‖ + L * ‖High n B (lam ^ 2 * k)‖ := by
      rw [hDk]
      calc _ ≤ ‖High n B (lam * k) * sigmaC (lam ^ 2 * k)‖
            + ‖Low n B (lam * k) * High n B (lam ^ 2 * k)‖ := norm_add_le _ _
        _ ≤ _ := by
          rw [norm_mul, norm_mul, norm_sigmaC, mul_one]
          gcongr
          exact norm_Low_le B _
    have h0 : 0 ≤ ‖D k‖ := norm_nonneg _
    have hx : 0 ≤ ‖High n B (lam * k)‖ := norm_nonneg _
    have hy : 0 ≤ ‖High n B (lam ^ 2 * k)‖ := norm_nonneg _
    have hsq := mul_le_mul hle hle h0 (by positivity)
    nlinarith [mul_nonneg hL0 (sq_nonneg (‖High n B (lam * k)‖ - ‖High n B (lam ^ 2 * k)‖))]
  have hsumD : ∑ k, ‖D k‖ ^ 2 ≤ (1 + L) * (T + L * T) := by
    calc ∑ k, ‖D k‖ ^ 2
        ≤ ∑ k, (1 + L) * (‖High n B (lam * k)‖ ^ 2 + L * ‖High n B (lam ^ 2 * k)‖ ^ 2) :=
          sum_le_sum fun k _ => hpt k
      _ = (1 + L) * (∑ k, ‖High n B (lam * k)‖ ^ 2
            + L * ∑ k, ‖High n B (lam ^ 2 * k)‖ ^ 2) := by
          rw [← mul_sum, sum_add_distrib, ← mul_sum]
      _ = (1 + L) * (T + L * T) := by
          have e1 : ∑ k, ‖High n B (lam * k)‖ ^ 2 = T :=
            Equiv.sum_comp (Equiv.mulLeft₀ lam hlam0) (fun k => ‖High n B k‖ ^ 2)
          have e2 : ∑ k, ‖High n B (lam ^ 2 * k)‖ ^ 2 = T :=
            Equiv.sum_comp (Equiv.mulLeft₀ (lam ^ 2) hlam20) (fun k => ‖High n B k‖ ^ 2)
          rw [e1, e2]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  calc ∑ γ ∈ univ \ GammaJ lam B, ‖ft (JC lam) γ‖ ^ 2
      ≤ (1 / (n : ℝ)) * ∑ k, ‖D k‖ ^ 2 := hsum1
    _ ≤ (1 / (n : ℝ)) * ((1 + L) * (T + L * T)) := by gcongr
    _ = (1 + L) ^ 2 * ((1 / (n : ℝ)) * T) := by ring
    _ ≤ (1 + L) ^ 2 * (1 / (B : ℝ)) := by gcongr
    _ = (1 + L) ^ 2 / (B : ℝ) := by ring

end Ecdlp.ParityFourier.ProofsC44
