import Mathlib
import Ecdlp.Proved.ParityFourier.StatementsC44R
import Ecdlp.Proved.ParityFourier.ProofsC44H
import Ecdlp.Proved.ParityFourier.ProofsC44d
import Ecdlp.Proved.ParityFourier.ProofsC44L

/-!
# Proofs of C44-R (C44 Theorem 10 for J, with the SFT output as a hypothesis)

Proves the frozen statements `Ecdlp.ParityFourier.AccessCorrelation`, `Ecdlp.ParityFourier.GammaJCard`,
`Ecdlp.ParityFourier.HeavySetSmall`, `Ecdlp.ParityFourier.JReductionSound`,
`Ecdlp.ParityFourier.JRecoverFromHeavyList` and `Ecdlp.ParityFourier.JRecoverExplicit` from
`Ecdlp/Proved/ParityFourier/StatementsC44R.lean`. No proof of these statements existed when that file
was frozen; nothing here is ported from a scratch file.

Outline:
1. Group facts. With `addOrderOf G = n`, `a ↦ [a.val]G` is injective on `ZMod n`
   (`nsmul_eq_nsmul_iff_modEq`) and `[x.val]([k.val]G) = [(x k).val]G`
   (`mod_addOrderOf_nsmul`).
2. C44-10s. A kept proposal `k'` passes `[k']G = [k]G`, so `k' = k`; if `[k]G = O`
   then `k = 0`, the output when `Q = O`.
3. C44-6a#. `GammaJ` is the image of `window B × window B`, which has `(2B + 1)^2`
   elements. Two pairs with the same image differ by `(d1, d2)` with `d1 + lam d2 = 0`
   and `|d1|, |d2| ≤ 2B`; by C44-N (`normLemma`) a nonzero such pair has
   `n ≤ d1^2 - d1 d2 + d2^2 ≤ 12 B^2`, so for `12 B^2 < n` the map is injective.
4. C44-HS. `τ #{heavy} ≤ ∑_β |ŵ(β)|^2 = (1/n) ∑_x |w(x)|^2 ≤ 1` (`ProofsC44.parseval`).
5. C44-8. For `k ≠ 0`, `w(x) J(x k) = φ(x k)` with `φ(0) = J(0) = 1` and
   `φ(u) = Pred([u]G) J(u) = ±1` (`+1` iff the predictor agrees) for `u ≠ 0`. After
   `u = x k`, `∑_x w(x) J(x k) = 1 + 2a - (n - 1)` with `a` the agreement count. With
   `(1/2 + ε)(n - 1) ≤ a ≤ n - 1` (hence `ε ≤ 1/2`) this is at least `2 ε n - 2`.
6. C44-10. For `k = 0`, `Q = O` and the output is `{0}`. For `k ≠ 0`, C44-8 gives the
   correlation `2η`; C44-9J (`jHeavy`) gives `α ∈ GammaJ lam B` with
   `η ≤ L1low(B)^2 |ŵ(α k)|`; then `L1low B ≠ 0` (as `η > 0`) and
   `τ ≤ (η / L1low(B)^2)^2 ≤ |ŵ(α k)|^2`, so `α k ∈ Lst`. The table hit
   `[(α k).val]G = [α.val]([k.val]G)` holds by step 1, `α ≠ 0` by C44-6d
   (`zeroNotInGammaJ`), so the proposal is `α k α⁻¹ = k`, which passes the check. With
   step 2 the output is exactly `{k}`.
7. C44-10x. C44-L4 (`l1lowBound`, `n` odd and `2B + 1 ≤ n`) gives
   `0 ≤ L1low B ≤ 2 + log(2B + 1)`, so the condition `(3 + log(2B + 1))^2 / B ≤ η^2`
   implies `(1 + L1low B)^2 / B ≤ η^2`, and `η ≤ L1low(B)^2 |ŵ(α k)|` implies
   `(η / (2 + log(2B + 1))^2)^2 ≤ |ŵ(α k)|^2`; step 6's core argument finishes.
-/

namespace Ecdlp.ParityFourier.ProofsC44R

open Ecdlp.ParityFourier Finset

section Group

variable {A : Type*} [AddCommGroup A] {G : A} {n : ℕ} [NeZero n]

/-- With `addOrderOf G = n`, `a ↦ [a.val]G` is injective on `ZMod n`. -/
lemma val_nsmul_inj (hG : addOrderOf G = n) {a b : ZMod n} (h : a.val • G = b.val • G) :
    a = b := by
  rw [nsmul_eq_nsmul_iff_modEq, hG] at h
  apply ZMod.val_injective
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h

lemma val_nsmul_eq_zero (hG : addOrderOf G = n) {a : ZMod n} (h : a.val • G = 0) : a = 0 := by
  apply val_nsmul_inj hG
  simpa using h

omit [NeZero n] in
/-- `[x.val]([k.val]G) = [(x k).val]G`. -/
lemma val_mul_nsmul (hG : addOrderOf G = n) (x k : ZMod n) :
    x.val • (k.val • G) = (x * k).val • G := by
  have h := mod_addOrderOf_nsmul G (x.val * k.val)
  rw [hG] at h
  rw [smul_smul, ZMod.val_mul, h]

end Group

/-! ### C44-10s -/

theorem jReductionSound : Ecdlp.ParityFourier.JReductionSound := by
  intro A _ _ G n _ hG lam B Lst k
  unfold jReductionOutput
  split_ifs with hQ
  · rw [singleton_subset_iff, mem_singleton]
    exact (val_nsmul_eq_zero hG hQ).symm
  · intro k' hk'
    rw [mem_filter] at hk'
    rw [mem_singleton]
    exact val_nsmul_inj hG hk'.2

/-! ### C44-6a# -/

lemma card_window (B : ℕ) : (window B).card = 2 * B + 1 := by
  unfold window
  rw [Int.card_Icc]
  omega

theorem gammaJCard : Ecdlp.ParityFourier.GammaJCard := by
  intro n _ lam hlam B
  have hprod : ((window B) ×ˢ (window B)).card = (2 * B + 1) ^ 2 := by
    rw [card_product, card_window, sq]
  refine ⟨?_, fun hB => ?_⟩
  · unfold GammaJ
    rw [← hprod]
    exact card_image_le
  · unfold GammaJ
    rw [← hprod]
    apply card_image_of_injOn
    rintro ⟨t1, t2⟩ ht ⟨s1, s2⟩ hs he
    simp only [coe_product, Set.mem_prod, mem_coe, window, mem_Icc] at ht hs
    simp only at he
    have hlam0 : lam ≠ 0 := by
      rintro rfl
      simp at hlam
    have hd : ((t1 - s1 : ℤ) : ZMod n) + lam * ((t2 - s2 : ℤ) : ZMod n) = 0 := by
      have h : lam * (((t1 - s1 : ℤ) : ZMod n) + lam * ((t2 - s2 : ℤ) : ZMod n)) = 0 := by
        push_cast
        linear_combination he
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h hlam0
      · exact h
    by_contra hne
    have hne' : ((t1 - s1 : ℤ), (t2 - s2 : ℤ)) ≠ (0, 0) := by
      intro h
      simp only [Prod.mk.injEq] at h
      apply hne
      rw [Prod.mk.injEq]
      exact ⟨by omega, by omega⟩
    have hN := ProofsC44d.normLemma n lam hlam _ _ hne' hd
    have hB' : (12 * (B : ℤ) ^ 2) < (n : ℤ) := by exact_mod_cast hB
    obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩ := ht
    obtain ⟨⟨h3a, h3b⟩, ⟨h4a, h4b⟩⟩ := hs
    set M : ℤ := 2 * (B : ℤ) with hM
    set x : ℤ := t1 - s1 with hx
    set y : ℤ := t2 - s2 with hy
    have hxl : -M ≤ x := by omega
    have hxu : x ≤ M := by omega
    have hyl : -M ≤ y := by omega
    have hyu : y ≤ M := by omega
    nlinarith [mul_nonneg (sub_nonneg.2 hxu) (sub_nonneg.2 hyu),
      mul_nonneg (neg_le_iff_add_nonneg.1 hxl) (neg_le_iff_add_nonneg.1 hyl),
      mul_nonneg (sub_nonneg.2 hxu) (neg_le_iff_add_nonneg.1 hxl),
      mul_nonneg (sub_nonneg.2 hyu) (neg_le_iff_add_nonneg.1 hyl)]

/-! ### C44-HS -/

theorem heavySetSmall : Ecdlp.ParityFourier.HeavySetSmall := by
  intro n _ w hw τ hτ
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set S := univ.filter (fun β : ZMod n => τ ≤ ‖ft w β‖ ^ 2) with hS
  calc τ * (S.card : ℝ) = ∑ _β ∈ S, τ := by rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ β ∈ S, ‖ft w β‖ ^ 2 := sum_le_sum fun β hβ => (mem_filter.1 hβ).2
    _ ≤ ∑ β, ‖ft w β‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
    _ = (1 / (n : ℝ)) * ∑ x, ‖w x‖ ^ 2 := ProofsC44.parseval w
    _ ≤ (1 / (n : ℝ)) * ∑ _x : ZMod n, (1 : ℝ) := by
        gcongr with x
        exact pow_le_one₀ (norm_nonneg _) (hw x)
    _ = 1 := by
        rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
        field_simp

/-! ### C44-8 -/

lemma sgn_cases {n : ℕ} (a : ZMod n) : sgn a = 1 ∨ sgn a = -1 := neg_one_pow_eq_or ℤ _

lemma J_cases {n : ℕ} (lam u : ZMod n) : J lam u = 1 ∨ J lam u = -1 := by
  unfold J
  rcases sgn_cases (lam * u) with h1 | h1 <;> rcases sgn_cases (lam ^ 2 * u) with h2 | h2 <;>
    simp [h1, h2]

lemma J_zero {n : ℕ} (lam : ZMod n) : J lam 0 = 1 := by
  simp [J, sgn]

section Access

variable {A : Type*} [AddCommGroup A] {G : A} {n : ℕ} [Fact n.Prime]

/-- For `k ≠ 0`, `w(x) = φ(x k)` with `φ(0) = 1`, `φ(u) = Pred([u]G)`. -/
lemma accessFn_eq (hG : addOrderOf G = n) (Pred : A → ℤ) {k : ZMod n} (hk : k ≠ 0)
    (x : ZMod n) :
    accessFn Pred (k.val • G) x = if x * k = 0 then 1 else Pred ((x * k).val • G) := by
  have h : (x * k = 0) ↔ (x = 0) := by simp [hk]
  simp only [accessFn, h, val_mul_nsmul hG]

lemma accessFn_cases (hG : addOrderOf G = n) {Pred : A → ℤ}
    (hPred : ∀ u : ZMod n, u ≠ 0 → Pred (u.val • G) = 1 ∨ Pred (u.val • G) = -1)
    {k : ZMod n} (hk : k ≠ 0) (x : ZMod n) :
    accessFn Pred (k.val • G) x = 1 ∨ accessFn Pred (k.val • G) x = -1 := by
  rw [accessFn_eq hG Pred hk x]
  split_ifs with hx
  · exact Or.inl rfl
  · exact hPred _ hx

end Access

theorem accessCorrelation : Ecdlp.ParityFourier.AccessCorrelation := by
  intro A _ G n _ _ hG lam Pred hPred ε hadv k hk
  set a : ℕ := ((univ.erase (0 : ZMod n)).filter
    (fun u => Pred (u.val • G) = J lam u)).card with ha
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (Fact.out : n.Prime).one_lt
  have hcard : (univ.erase (0 : ZMod n)).card = n - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  have hcardR : ((univ.erase (0 : ZMod n)).card : ℝ) = (n : ℝ) - 1 := by
    rw [hcard, Nat.cast_sub (Fact.out : n.Prime).one_lt.le, Nat.cast_one]
  set φ : ZMod n → ℝ := fun u =>
    ((if u = 0 then 1 else Pred (u.val • G) : ℤ) : ℝ) * (J lam u : ℝ) with hφ
  have hsum : ∑ x : ZMod n, (accessFn Pred (k.val • G) x : ℝ) * (J lam (x * k) : ℝ)
      = 1 + 2 * (a : ℝ) - ((n : ℝ) - 1) := by
    have h1 : ∑ x : ZMod n, (accessFn Pred (k.val • G) x : ℝ) * (J lam (x * k) : ℝ)
        = ∑ x, φ (x * k) := by
      refine sum_congr rfl fun x _ => ?_
      rw [accessFn_eq hG Pred hk x]
    have h2 : ∑ x, φ (x * k) = ∑ u, φ u := Equiv.sum_comp (Equiv.mulRight₀ k hk) φ
    rw [h1, h2, ← add_sum_erase _ _ (mem_univ (0 : ZMod n))]
    have h0 : φ 0 = 1 := by simp [hφ, J_zero]
    have h3 : ∀ u ∈ univ.erase (0 : ZMod n),
        φ u = if Pred (u.val • G) = J lam u then 1 else -1 := by
      intro u hu
      have hu0 : u ≠ 0 := ne_of_mem_erase hu
      simp only [hφ, if_neg hu0]
      rcases hPred u hu0 with hp | hp <;> rcases J_cases lam u with hj | hj <;> simp [hp, hj]
    rw [h0, sum_congr rfl h3, sum_ite]
    simp only [sum_const, nsmul_eq_mul, mul_one, mul_neg]
    have hc := card_filter_add_card_filter_not (s := univ.erase (0 : ZMod n))
      (fun u => Pred (u.val • G) = J lam u)
    have hc' : (a : ℝ) + (((univ.erase (0 : ZMod n)).filter
        (fun u => ¬ Pred (u.val • G) = J lam u)).card : ℝ) = (n : ℝ) - 1 := by
      rw [← hcardR, ← hc, Nat.cast_add]
    linarith
  rw [hsum]
  have hle : (a : ℝ) ≤ (n : ℝ) - 1 := by
    rw [← hcardR]
    exact_mod_cast card_filter_le _ _
  have hε : ε ≤ 1 / 2 := by
    by_contra h
    push Not at h
    nlinarith
  have hnpos : (0 : ℝ) < n := by linarith
  have e1 : 2 * (ε - 1 / (n : ℝ)) = (2 * ε * n - 2) / n := by field_simp
  have e2 : 1 / (n : ℝ) * (1 + 2 * (a : ℝ) - ((n : ℝ) - 1))
      = (1 + 2 * (a : ℝ) - ((n : ℝ) - 1)) / n := by ring
  rw [e1, e2]
  apply div_le_div_of_nonneg_right _ hnpos.le
  nlinarith

/-! ### C44-10 and C44-10x -/

/-- Core of C44-10 for `k ≠ 0`: if every `β` with `η ≤ L1low(B)^2 |ŵ(β)|` is in the list,
the output of `R` is exactly `{k}`. -/
lemma recover_core {A : Type} [AddCommGroup A] [DecidableEq A] {G : A} {n : ℕ} [NeZero n]
    [Fact n.Prime] (hn2 : n ≠ 2) (hG : addOrderOf G = n) {lam : ZMod n}
    (hlam : lam ^ 2 + lam + 1 = 0) {Pred : A → ℤ}
    (hPred : ∀ u : ZMod n, u ≠ 0 → Pred (u.val • G) = 1 ∨ Pred (u.val • G) = -1)
    {ε : ℝ} (hadv : (1 / 2 + ε) * ((n : ℝ) - 1) ≤
        (((univ.erase (0 : ZMod n)).filter (fun u => Pred (u.val • G) = J lam u)).card : ℝ))
    (hη : 0 < ε - 1 / (n : ℝ)) {B : ℕ} (hB1 : 1 ≤ B) (hBn : 3 * (2 * B + 1) ^ 2 < n)
    (hthr : (1 + L1low n B) ^ 2 / (B : ℝ) ≤ (ε - 1 / (n : ℝ)) ^ 2)
    {k : ZMod n} (hk : k ≠ 0) {Lst : Finset (ZMod n)}
    (hLst : ∀ β : ZMod n, ε - 1 / (n : ℝ) ≤
        L1low n B ^ 2 * ‖ft (fun x => ((accessFn Pred (k.val • G) x : ℤ) : ℂ)) β‖ →
          β ∈ Lst) :
    jReductionOutput lam B G (k.val • G) Lst = {k} := by
  have hwb : ∀ x : ZMod n, |(accessFn Pred (k.val • G) x : ℝ)| ≤ 1 := by
    intro x
    rcases accessFn_cases hG hPred hk x with h | h <;> simp [h]
  have hcorr := accessCorrelation A G n hG lam Pred hPred ε hadv k hk
  obtain ⟨α, hα, hheavy⟩ := ProofsC44H.jHeavy n hn2 lam hlam B hB1
    (fun x : ZMod n => (accessFn Pred (k.val • G) x : ℝ)) hwb k hk (ε - 1 / (n : ℝ)) hη hthr hcorr
  have hfun : (fun x : ZMod n => (((accessFn Pred (k.val • G) x : ℤ) : ℝ) : ℂ))
      = (fun x : ZMod n => ((accessFn Pred (k.val • G) x : ℤ) : ℂ)) := by
    funext x
    exact Complex.ofReal_intCast _
  rw [hfun] at hheavy
  have hβ : α * k ∈ Lst := hLst _ hheavy
  have hα0 : α ≠ 0 := by
    intro h
    exact ProofsC44d.zeroNotInGammaJ n hn2 lam hlam B hBn (h ▸ hα)
  have hQ : k.val • G ≠ 0 := fun h => hk (val_nsmul_eq_zero hG h)
  apply Finset.Subset.antisymm (jReductionSound A G n hG lam B Lst k)
  rw [singleton_subset_iff]
  unfold jReductionOutput
  rw [if_neg hQ, mem_filter]
  refine ⟨mem_image.2 ⟨(α * k, α), mem_filter.2 ⟨mem_product.2 ⟨hβ, hα⟩, ?_⟩, ?_⟩, rfl⟩
  · show (α * k).val • G = α.val • (k.val • G)
    rw [val_mul_nsmul hG]
  · show α * k * α⁻¹ = k
    rw [mul_comm α k, mul_assoc, mul_inv_cancel₀ hα0, mul_one]

theorem jRecoverFromHeavyList : Ecdlp.ParityFourier.JRecoverFromHeavyList := by
  intro A _ _ G n _ _ hn2 hG lam hlam Pred hPred ε hadv hη B hB1 hBn hthr τ hτ k Lst hLst
  by_cases hk : k = 0
  · subst hk
    unfold jReductionOutput
    rw [if_pos (by simp)]
  · refine recover_core hn2 hG hlam hPred hadv hη hB1 hBn hthr hk fun β hβ => hLst β ?_
    have hL : 0 < L1low n B ^ 2 := by
      rcases (sq_nonneg (L1low n B)).lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hβ
        linarith
    refine le_trans hτ (pow_le_pow_left₀ (div_nonneg hη.le hL.le) ?_ 2)
    rw [div_le_iff₀ hL, mul_comm]
    exact hβ

theorem jRecoverExplicit : Ecdlp.ParityFourier.JRecoverExplicit := by
  intro A _ _ G n _ _ hn2 hG lam hlam Pred hPred ε hadv hη B hB1 hBn hthr k Lst hLst
  by_cases hk : k = 0
  · subst hk
    unfold jReductionOutput
    rw [if_pos (by simp)]
  · have hodd : Odd n := (Fact.out : n.Prime).odd_of_ne_two hn2
    have h2B : 2 * B + 1 ≤ n := by nlinarith
    have hL := ProofsC44L.l1lowBound n hodd B h2B
    have hL0 : 0 ≤ L1low n B := ProofsC44.L1low_nonneg B
    have hlog : 0 ≤ Real.log (2 * (B : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)])
    have hBpos : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    have hthr' : (1 + L1low n B) ^ 2 / (B : ℝ) ≤ (ε - 1 / (n : ℝ)) ^ 2 := by
      refine le_trans (div_le_div_of_nonneg_right ?_ hBpos) hthr
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    refine recover_core hn2 hG hlam hPred hadv hη hB1 hBn hthr' hk fun β hβ => hLst β ?_
    have hM : 0 < (2 + Real.log (2 * (B : ℝ) + 1)) ^ 2 := by positivity
    have hLM : L1low n B ^ 2 ≤ (2 + Real.log (2 * (B : ℝ) + 1)) ^ 2 :=
      pow_le_pow_left₀ hL0 hL 2
    have hβ' : ε - 1 / (n : ℝ) ≤ (2 + Real.log (2 * (B : ℝ) + 1)) ^ 2 *
        ‖ft (fun x => ((accessFn Pred (k.val • G) x : ℤ) : ℂ)) β‖ :=
      le_trans hβ (mul_le_mul_of_nonneg_right hLM (norm_nonneg _))
    refine pow_le_pow_left₀ (div_nonneg hη.le hM.le) ?_ 2
    rw [div_le_iff₀ hM, mul_comm]
    exact hβ'

end Ecdlp.ParityFourier.ProofsC44R
