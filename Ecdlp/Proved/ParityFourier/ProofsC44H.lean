import Mathlib
import Ecdlp.Proved.ParityFourier.StatementsC44H
import Ecdlp.Proved.ParityFourier.ProofsC44

/-!
# Proofs of C44-H and C44-9J (heavy Fourier coefficient; C44 Lemma 9 for J)

Proves the frozen statements `Ecdlp.ParityFourier.HeavyCore` and `Ecdlp.ParityFourier.JHeavy` from
`Ecdlp.Proved.ParityFourier.StatementsC44H`.

Outline (with `e = ZMod.stdAddChar`):
1. C44-H. `(1/n) ∑ w F = ∑_i c_i ŵ(-m_i)`, so the correlation splits into
   `(1/n) ∑ w (f - F)`, at most `η` by Cauchy–Schwarz and `|w| ≤ 1`, plus
   `∑_i c_i ŵ(-m_i)`; hence `η ≤ ∑_i |c_i| |ŵ(-m_i)|`, and the largest `|ŵ(-m_i)|` gives the
   claim (port of the scratch proof `heavy_core`, re-indexed by `ι`).
2. The inner bound of C44-6' (copied from `ProofsC44.jConcentration`):
   `(1/n) ∑_y |J(y) - P(y)|^2 ≤ (1 + L1low B)^2 / B` with
   `P(y) = Low(lam y) Low(lam^2 y)`. `Low` sums over the finset `W = {h + t : |t| ≤ B}` of
   residues, so a residue hit by several `t` is counted once, and the C44-6' argument
   (`|Low| ≤ L1low B`, tail mass `≤ 1/B`) uses no assumption `2B + 1 ≤ n`. The bound
   therefore holds for every `B ≥ 1`, and the proof needs no case split on `2B + 1 ≤ n`.
   (Remark, not used: for `2B + 1 ≥ n`, `W` is all of `ZMod n` and `P = J`.)
3. C44-9J. Apply C44-H to `f(x) = J(x k)` and `F(x) = P(x k)`, a trigonometric polynomial
   indexed by `W × W` with frequencies `(lam a + lam^2 b) k` and coefficients
   `ŝ(a) ŝ(b)`, whose `L1` norm is `(∑_{a ∈ W} |ŝ(a)|)^2 ≤ L1low(B)^2`. The `L2` error is the
   bound of step 2 after the change of variables `y = x k` (`k ≠ 0`, `n` prime). For real
   `w`, `ŵ(-β)` is the conjugate of `ŵ(β)`, so `|ŵ(-(α k))| = |ŵ(α k)|`, and
   `α = lam a + lam^2 b ∈ GammaJ lam B`.
-/

namespace Ecdlp.ParityFourier.ProofsC44H

open Ecdlp.ParityFourier Finset Ecdlp.ParityFourier.ProofsC44

local notation "𝐞" => ZMod.stdAddChar

theorem heavyCore : Ecdlp.ParityFourier.HeavyCore := by
  intro n _ ι I w f F c m hF hw η hη hcorr happrox
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  -- split the correlation
  have hsplit : (1 / (n : ℂ)) * ∑ x, w x * f x
      = (1 / (n : ℂ)) * ∑ x, w x * (f x - F x) + ∑ i ∈ I, c i * ft w (-(m i)) := by
    have h2 : ∑ i ∈ I, c i * ft w (-(m i)) = (1 / (n : ℂ)) * ∑ x, w x * F x := by
      simp_rw [hF, ft_eq, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun x _ => sum_congr rfl fun i _ => ?_
      simp only [neg_mul, neg_neg]
      ring
    rw [h2, ← mul_add, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun x _ => ?_
    ring
  -- error term ≤ η by Cauchy–Schwarz
  have herr : ‖(1 / (n : ℂ)) * ∑ x, w x * (f x - F x)‖ ≤ η := by
    have hcs : (∑ x, ‖w x‖ * ‖f x - F x‖) ^ 2
        ≤ (∑ x : ZMod n, ‖w x‖ ^ 2) * ∑ x, ‖f x - F x‖ ^ 2 :=
      sum_mul_sq_le_sq_mul_sq _ _ _
    have hw2 : ∑ x : ZMod n, ‖w x‖ ^ 2 ≤ n := by
      calc ∑ x : ZMod n, ‖w x‖ ^ 2 ≤ ∑ _x : ZMod n, (1 : ℝ) :=
            sum_le_sum fun x _ => by
              have := hw x; have := norm_nonneg (w x); nlinarith
        _ = n := by simp [ZMod.card]
    have hd : ∑ x, ‖f x - F x‖ ^ 2 ≤ n * η ^ 2 := by
      have := happrox
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn0] at this
      linarith
    have hA : (∑ x, ‖w x‖ * ‖f x - F x‖) ^ 2 ≤ (n * η) ^ 2 := by
      calc _ ≤ (∑ x : ZMod n, ‖w x‖ ^ 2) * ∑ x, ‖f x - F x‖ ^ 2 := hcs
        _ ≤ n * (n * η ^ 2) := by
            apply mul_le_mul hw2 hd (sum_nonneg fun _ _ => sq_nonneg _) hn0.le
        _ = (n * η) ^ 2 := by ring
    have hB : ∑ x, ‖w x‖ * ‖f x - F x‖ ≤ n * η :=
      abs_le_of_sq_le_sq' hA (by positivity) |>.2
    calc ‖(1 / (n : ℂ)) * ∑ x, w x * (f x - F x)‖
        ≤ (1 / (n : ℝ)) * ∑ x, ‖w x‖ * ‖f x - F x‖ := by
          rw [norm_mul]
          gcongr
          · simp
          · calc _ ≤ ∑ x, ‖w x * (f x - F x)‖ := norm_sum_le _ _
              _ = _ := by simp_rw [norm_mul]
      _ ≤ (1 / (n : ℝ)) * (n * η) := by gcongr
      _ = η := by field_simp
  -- main term
  have hmain : η ≤ ∑ i ∈ I, ‖c i‖ * ‖ft w (-(m i))‖ := by
    have h1 : 2 * η ≤ η + ‖∑ i ∈ I, c i * ft w (-(m i))‖ := by
      calc 2 * η ≤ ((1 / (n : ℂ)) * ∑ x, w x * f x).re := hcorr
        _ ≤ ‖(1 / (n : ℂ)) * ∑ x, w x * f x‖ := Complex.re_le_norm _
        _ ≤ ‖(1 / (n : ℂ)) * ∑ x, w x * (f x - F x)‖ + ‖∑ i ∈ I, c i * ft w (-(m i))‖ := by
            rw [hsplit]; exact norm_add_le _ _
        _ ≤ η + ‖∑ i ∈ I, c i * ft w (-(m i))‖ := by gcongr
    have h2 : ‖∑ i ∈ I, c i * ft w (-(m i))‖ ≤ ∑ i ∈ I, ‖c i‖ * ‖ft w (-(m i))‖ := by
      calc _ ≤ ∑ i ∈ I, ‖c i * ft w (-(m i))‖ := norm_sum_le _ _
        _ = _ := by simp_rw [norm_mul]
    linarith
  rcases I.eq_empty_or_nonempty with hI | hI
  · simp [hI] at hmain; linarith
  obtain ⟨i, hi, hmax⟩ := I.exists_max_image (fun i => ‖ft w (-(m i))‖) hI
  refine ⟨i, hi, ?_⟩
  calc η ≤ ∑ j ∈ I, ‖c j‖ * ‖ft w (-(m j))‖ := hmain
    _ ≤ ∑ j ∈ I, ‖c j‖ * ‖ft w (-(m i))‖ :=
        sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hmax j hj) (norm_nonneg _)
    _ = (∑ j ∈ I, ‖c j‖) * ‖ft w (-(m i))‖ := by rw [sum_mul]

section JPart

variable {n : ℕ} [NeZero n]

/-- For a real function, `ŵ(-β)` is the conjugate of `ŵ(β)`. -/
lemma norm_ft_real_neg (w : ZMod n → ℝ) (β : ZMod n) :
    ‖ft (fun x => (w x : ℂ)) (-β)‖ = ‖ft (fun x => (w x : ℂ)) β‖ := by
  have h : ft (fun x => (w x : ℂ)) (-β) = (starRingEnd ℂ) (ft (fun x => (w x : ℂ)) β) := by
    rw [ft_eq, ft_eq, map_mul, map_sum]
    congr 1
    · simp
    · refine sum_congr rfl fun x _ => ?_
      rw [map_mul, Complex.conj_ofReal, conj_e]
      congr 2
      ring
  rw [h, Complex.norm_conj]

omit [NeZero n] in
/-- `J` as the cast of the integer sign. -/
lemma JC_eq_J (lam y : ZMod n) : JC lam y = ((J lam y : ℤ) : ℂ) := by
  simp [JC, J, sigmaC, sgn]

/-- The `L1` norm of the coefficients of `P(y) = Low(lam y) Low(lam^2 y)`. -/
lemma sum_norm_coeff (B : ℕ) :
    ∑ p ∈ Wset n B ×ˢ Wset n B,
        ‖ft (sigmaC (n := n)) p.1 * ft (sigmaC (n := n)) p.2‖ ≤ L1low n B ^ 2 := by
  have hW : ∑ a ∈ Wset n B, ‖ft (sigmaC (n := n)) a‖ ≤ L1low n B := by
    unfold Wset L1low
    exact sum_image_le_of_nonneg fun _ _ => norm_nonneg _
  have h0 : 0 ≤ ∑ a ∈ Wset n B, ‖ft (sigmaC (n := n)) a‖ := sum_nonneg fun _ _ => norm_nonneg _
  rw [sum_product]
  simp_rw [norm_mul]
  rw [← sum_mul_sum, ← sq]
  exact pow_le_pow_left₀ h0 hW 2

/-- Inner bound of C44-6' (copied from `ProofsC44.jConcentration`):
`(1/n) ∑_y |J(y) - Low(lam y) Low(lam^2 y)|^2 ≤ (1 + L1low B)^2 / B`. -/
lemma approx_le [Fact n.Prime] (hn2 : n ≠ 2) (lam : ZMod n) (hlam : lam ^ 2 + lam + 1 = 0)
    (B : ℕ) (hB : 1 ≤ B) :
    (1 / (n : ℝ)) * ∑ y, ‖JC lam y - Low n B (lam * y) * Low n B (lam ^ 2 * y)‖ ^ 2
      ≤ (1 + L1low n B) ^ 2 / (B : ℝ) := by
  have hodd : Odd n := (Fact.out : n.Prime).odd_of_ne_two hn2
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    simp at hlam
  have hlam20 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam0
  have hL0 : 0 ≤ L1low n B := L1low_nonneg B
  set L := L1low n B with hL
  have hTB : (1 / (n : ℝ)) * ∑ k, ‖High n B k‖ ^ 2 ≤ 1 / (B : ℝ) := high_mass hodd B hB
  set T := ∑ k, ‖High n B k‖ ^ 2 with hT
  set D : ZMod n → ℂ := fun k => JC lam k - Low n B (lam * k) * Low n B (lam ^ 2 * k) with hD
  have hpt : ∀ k, ‖D k‖ ^ 2
      ≤ (1 + L) * (‖High n B (lam * k)‖ ^ 2 + L * ‖High n B (lam ^ 2 * k)‖ ^ 2) := by
    intro k
    have hDk : D k = High n B (lam * k) * sigmaC (lam ^ 2 * k)
        + Low n B (lam * k) * High n B (lam ^ 2 * k) := by
      simp only [hD, High, JC]
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
  calc (1 / (n : ℝ)) * ∑ k, ‖D k‖ ^ 2
      ≤ (1 / (n : ℝ)) * ((1 + L) * (T + L * T)) := by gcongr
    _ = (1 + L) ^ 2 * ((1 / (n : ℝ)) * T) := by ring
    _ ≤ (1 + L) ^ 2 * (1 / (B : ℝ)) := by gcongr
    _ = (1 + L) ^ 2 / (B : ℝ) := by ring

end JPart

theorem jHeavy : Ecdlp.ParityFourier.JHeavy := by
  intro n _ _ hn2 lam hlam B hB w hw k hk η hη hthr hcorr
  set W := Wset n B with hWdef
  set wC : ZMod n → ℂ := fun x => (w x : ℂ) with hwC
  set c : ZMod n × ZMod n → ℂ :=
    fun p => ft (sigmaC (n := n)) p.1 * ft (sigmaC (n := n)) p.2 with hc
  set m : ZMod n × ZMod n → ZMod n := fun p => (lam * p.1 + lam ^ 2 * p.2) * k with hm
  set F : ZMod n → ℂ := fun x => Low n B (lam * (x * k)) * Low n B (lam ^ 2 * (x * k)) with hF
  -- `F` is a trigonometric polynomial with frequencies `m p`
  have hFtrig : ∀ x, F x = ∑ p ∈ W ×ˢ W, c p * 𝐞 (m p * x) := by
    intro x
    have h := congrFun (P_eq lam B) (x * k)
    simp only [hF, hc, hm, hWdef]
    rw [h]
    refine sum_congr rfl fun p _ => ?_
    congr 2
    ring
  have hw' : ∀ x, ‖wC x‖ ≤ 1 := by
    intro x
    simp only [hwC, Complex.norm_real, Real.norm_eq_abs]
    exact hw x
  -- the correlation hypothesis in complex form
  have hcorr' : 2 * η ≤ ((1 / (n : ℂ)) * ∑ x, wC x * JC lam (x * k)).re := by
    have e : (1 / (n : ℂ)) * ∑ x, wC x * JC lam (x * k)
        = (((1 / (n : ℝ)) * ∑ x, w x * (J lam (x * k) : ℝ) : ℝ) : ℂ) := by
      simp only [hwC, JC_eq_J]
      push_cast
      rfl
    rw [e, Complex.ofReal_re]
    exact hcorr
  -- the `L2` error, after the change of variables `y = x k`
  have happrox : (1 / (n : ℝ)) * ∑ x, ‖JC lam (x * k) - F x‖ ^ 2 ≤ η ^ 2 := by
    have e : ∑ x, ‖JC lam (x * k) - F x‖ ^ 2
        = ∑ y, ‖JC lam y - Low n B (lam * y) * Low n B (lam ^ 2 * y)‖ ^ 2 :=
      Equiv.sum_comp (Equiv.mulRight₀ k hk)
        (fun y => ‖JC lam y - Low n B (lam * y) * Low n B (lam ^ 2 * y)‖ ^ 2)
    rw [e]
    exact (approx_le hn2 lam hlam B hB).trans hthr
  obtain ⟨p, hp, hη'⟩ := heavyCore n (ZMod n × ZMod n) (W ×ˢ W) wC
    (fun x => JC lam (x * k)) F c m hFtrig hw' η hη hcorr' happrox
  refine ⟨lam * p.1 + lam ^ 2 * p.2, ?_, ?_⟩
  · obtain ⟨hp1, hp2⟩ := mem_product.1 hp
    obtain ⟨t1, ht1, e1⟩ := mem_image.1 hp1
    obtain ⟨t2, ht2, e2⟩ := mem_image.1 hp2
    unfold GammaJ
    refine mem_image.2 ⟨(t1, t2), mem_product.2 ⟨ht1, ht2⟩, ?_⟩
    show lam * (hC n + (t1 : ZMod n)) + lam ^ 2 * (hC n + (t2 : ZMod n))
      = lam * p.1 + lam ^ 2 * p.2
    rw [e1, e2]
  · have hneg : ‖ft wC (-(m p))‖ = ‖ft wC ((lam * p.1 + lam ^ 2 * p.2) * k)‖ :=
      norm_ft_real_neg w _
    rw [hneg] at hη'
    calc η ≤ (∑ q ∈ W ×ˢ W, ‖c q‖) * ‖ft wC ((lam * p.1 + lam ^ 2 * p.2) * k)‖ := hη'
      _ ≤ L1low n B ^ 2 * ‖ft wC ((lam * p.1 + lam ^ 2 * p.2) * k)‖ := by
          gcongr
          exact sum_norm_coeff B

end Ecdlp.ParityFourier.ProofsC44H
