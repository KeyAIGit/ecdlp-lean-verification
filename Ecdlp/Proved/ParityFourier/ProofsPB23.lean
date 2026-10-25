import Ecdlp.Proved.ParityFourier.StatementsPB
import Ecdlp.Proved.ParityFourier.ProofsF3F4a

/-!
# Proofs of PB-2 (`VoteIdentity`) and PB-3 (`VoteAdvantage`)

Proves the frozen statements `Ecdlp.ParityFourier.VoteIdentity` and `Ecdlp.ParityFourier.VoteAdvantage` from
`Ecdlp.Proved.ParityFourier.StatementsPB`, and exposes the per-step facts that a proof of PB-4 uses.

Outline:
1. PB-2. `ZMod.val_add` gives `(y + r).val = (y.val + r.val) % n`. Without a wrap this is
   `y.val + r.val`; with a wrap it is `y.val + r.val - n`, and subtracting the odd `n` flips
   the parity, which the wrap term `1` restores.
2. Correct votes. If the answer is the parity of `y + r` and the guessed wrap
   `[n - c ≤ r.val]` equals the true wrap `[n ≤ y.val + r.val]`, then by PB-2 the vote is
   `(y.val + 2 r.val + 2 w) % 2 = y.val % 2` (`pbVote_eq_of_correct`).
3. Wrap window. With `k = ⌈n - c⌉₊` the guessed wrap is `[k ≤ r.val]` (`Nat.ceil_le`) and
   the true wrap is `[n - y.val ≤ r.val]`. They differ only for `r.val` in
   `[min k b, max k b)` with `b = n - y.val`, and `r ↦ r.val` is injective, so at most
   `|k - b|` shifts are in the window. From `n - c ≤ k` and (when `k > 0`) `k < n - c + 1`:
   `b - k ≤ c - y.val ≤ Δ` and `k - b < y.val - c + 1 ≤ Δ + 1` (`card_wrapWindow_le`).
4. PB-3. Translation `r ↦ y + r` is a bijection, so `#{r : P (y + r) correct} =
   #{z : P z correct}`. Every such `r` is a correct vote or in the window, so
   `#{z : P z correct} ≤ #{correct votes} + (Δ + 1)` (`card_vote_correct_ge`).
5. Helpers for PB-4 (not frozen statements):
   * `vote_half_advantage`: the hypothesis of PB-1 (`MajorityVote`) for `Ω = ZMod n` and the
     votes of one step, with `δ = ε - (Δ + 1)/n`;
   * `pbBit_eq_of_majority`, `two_mul_card_le_of_pbBit_ne`, `pbBit_answers_ne_subset`: a step
     decides the parity `p` of `y` unless at most half of its votes equal `p`, i.e. the
     failure event of a step lies in the event bounded by PB-1;
   * `two_mul_val_mul_inv_two`, `halve_error`: for an odd prime `n`,
     `2 (y · 2⁻¹).val = y.val + (y.val % 2) n`, so a correct bit halves the guess error
     `c - y.val` exactly.

Provenance: the proof of `vote_identity` (PB-2) is ported from the pre-freeze scratch file
`bv/lean-feasibility/VoteIdentity.lean` (disclosed in the docstring of `StatementsPB.lean`).
The wrap-window lemma of that scratch file (`wrap_decided`, integer guess) is not used; the
window count here (`card_wrapWindow_le`, rational guess, via `Nat.ceil`) is new. The proof
of PB-3 and the PB-4 helpers are new. `two_ne_zero_zmod` is reused from `ProofsF3F4a`.
-/

namespace Ecdlp.ParityFourier.ProofsPB23

open Finset Ecdlp.ParityFourier

/-- PB-2, pointwise: for odd `n`, the parity of `y + r` is the parity of `y.val + r.val`
plus the wrap `[n ≤ y.val + r.val]`. -/
theorem vote_identity {n : ℕ} [NeZero n] (hn : Odd n) (y r : ZMod n) :
    (y + r).val % 2 = (y.val + r.val + (if n ≤ y.val + r.val then 1 else 0)) % 2 := by
  rw [ZMod.val_add]
  have hy := ZMod.val_lt y
  have hr := ZMod.val_lt r
  obtain ⟨j, hj⟩ := hn
  split_ifs with h
  · have : (y.val + r.val) % n = y.val + r.val - n := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (show y.val + r.val - n < n by omega)]
    rw [this]
    omega
  · rw [Nat.mod_eq_of_lt (show y.val + r.val < n by omega)]
    simp

/-- PB-2. `VoteIdentity`. -/
theorem voteIdentity : Ecdlp.ParityFourier.VoteIdentity := by
  intro n _ hn y r
  exact vote_identity hn y r

/-- A vote is correct when the answer is the parity of `y + r` and the wrap decided by the
guess, `[n - c ≤ r.val]`, equals the true wrap `[n ≤ y.val + r.val]`. -/
theorem pbVote_eq_of_correct {n : ℕ} [NeZero n] (hn : Odd n) (a : ℕ) (c : ℚ) (y r : ZMod n)
    (ha : a = (y + r).val % 2)
    (hw : ((n : ℚ) - c ≤ (r.val : ℚ)) ↔ n ≤ y.val + r.val) :
    pbVote a c r = y.val % 2 := by
  unfold pbVote
  rw [ha, vote_identity hn y r]
  by_cases h : n ≤ y.val + r.val
  · rw [if_pos h, if_pos (hw.mpr h)]
    omega
  · rw [if_neg h, if_neg (fun h' => h (hw.mp h'))]
    omega

/-- Wrap window: with `|c - y.val| ≤ Δ`, the guessed wrap `[n - c ≤ r.val]` differs from the
true wrap `[n ≤ y.val + r.val]` for at most `Δ + 1` shifts `r`. -/
theorem card_wrapWindow_le {n : ℕ} [NeZero n] (y : ZMod n) (c : ℚ) (Δ : ℝ)
    (hc : |(c : ℝ) - (y.val : ℝ)| ≤ Δ) :
    ((univ.filter (fun r : ZMod n =>
        ¬ (((n : ℚ) - c ≤ (r.val : ℚ)) ↔ n ≤ y.val + r.val))).card : ℝ) ≤ Δ + 1 := by
  have hy := ZMod.val_lt y
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  set k : ℕ := ⌈(n : ℚ) - c⌉₊ with hk
  set b : ℕ := n - y.val with hb
  have hsub : (univ.filter (fun r : ZMod n =>
        ¬ (((n : ℚ) - c ≤ (r.val : ℚ)) ↔ n ≤ y.val + r.val))).image ZMod.val ⊆
      Finset.Ico (min k b) (max k b) := by
    intro v hv
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨r, hr, rfl⟩ := hv
    have hceil : ((n : ℚ) - c ≤ (r.val : ℚ)) ↔ k ≤ r.val := Nat.ceil_le.symm
    rw [hceil] at hr
    simp only [Finset.mem_Ico, min_le_iff, lt_max_iff]
    omega
  have hcard : (univ.filter (fun r : ZMod n =>
        ¬ (((n : ℚ) - c ≤ (r.val : ℚ)) ↔ n ≤ y.val + r.val))).card ≤ max k b - min k b := by
    rw [← Finset.card_image_of_injective _ (ZMod.val_injective n)]
    calc _ ≤ (Finset.Ico (min k b) (max k b)).card := Finset.card_le_card hsub
      _ = max k b - min k b := Nat.card_Ico _ _
  have hbR : (b : ℝ) = (n : ℝ) - (y.val : ℝ) := by
    rw [hb, Nat.cast_sub hy.le]
  have hkge : (n : ℝ) - (c : ℝ) ≤ (k : ℝ) := by
    have : (n : ℚ) - c ≤ (k : ℚ) := Nat.le_ceil _
    exact_mod_cast this
  have hcardR : ((univ.filter (fun r : ZMod n =>
        ¬ (((n : ℚ) - c ≤ (r.val : ℚ)) ↔ n ≤ y.val + r.val))).card : ℝ) ≤
      ((max k b - min k b : ℕ) : ℝ) := by
    exact_mod_cast hcard
  refine hcardR.trans ?_
  rcases le_total k b with hkb | hbk
  · rw [max_eq_right hkb, min_eq_left hkb, Nat.cast_sub hkb, hbR]
    linarith
  · rw [max_eq_left hbk, min_eq_right hbk, Nat.cast_sub hbk, hbR]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      omega
    · have hpos : (0 : ℚ) ≤ (n : ℚ) - c := by
        by_contra hneg
        have : k = 0 := Nat.ceil_eq_zero.mpr (not_le.mp hneg).le
        omega
      have hlt : (k : ℚ) < (n : ℚ) - c + 1 := Nat.ceil_lt_add_one hpos
      have hltR : (k : ℝ) < (n : ℝ) - (c : ℝ) + 1 := by exact_mod_cast hlt
      linarith

/-- Translation invariance: `#{r : P (y + r) correct} = #{z : P z correct}`. -/
theorem card_shift_correct {n : ℕ} [NeZero n] (P : ZMod n → ℕ) (y : ZMod n) :
    (univ.filter (fun r : ZMod n => P (y + r) = (y + r).val % 2)).card =
      (univ.filter (fun z : ZMod n => P z = z.val % 2)).card := by
  apply Finset.card_equiv (Equiv.addLeft y)
  intro r
  simp

/-- PB-3, pointwise in the parameters: with `|c - y.val| ≤ Δ`, at least
`#{z : P z correct} - (Δ + 1)` shifts give a correct vote. -/
theorem card_vote_correct_ge {n : ℕ} [NeZero n] (hn : Odd n) (P : ZMod n → ℕ) (y : ZMod n)
    (c : ℚ) (Δ : ℝ) (hc : |(c : ℝ) - (y.val : ℝ)| ≤ Δ) :
    ((univ.filter (fun z : ZMod n => P z = z.val % 2)).card : ℝ) - (Δ + 1) ≤
      ((univ.filter (fun r : ZMod n => pbVote (P (y + r)) c r = y.val % 2)).card : ℝ) := by
  set W := univ.filter (fun r : ZMod n =>
    ¬ (((n : ℚ) - c ≤ (r.val : ℚ)) ↔ n ≤ y.val + r.val)) with hW
  set V := univ.filter (fun r : ZMod n => pbVote (P (y + r)) c r = y.val % 2) with hV
  have hsub : univ.filter (fun r : ZMod n => P (y + r) = (y + r).val % 2) ⊆ V ∪ W := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rw [Finset.mem_union]
    by_cases hw : (((n : ℚ) - c ≤ (r.val : ℚ)) ↔ n ≤ y.val + r.val)
    · left
      simp only [hV, Finset.mem_filter, Finset.mem_univ, true_and]
      exact pbVote_eq_of_correct hn _ c y r hr hw
    · right
      simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hw
  have hcardN : (univ.filter (fun z : ZMod n => P z = z.val % 2)).card ≤ V.card + W.card := by
    rw [← card_shift_correct P y]
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hWle : (W.card : ℝ) ≤ Δ + 1 := card_wrapWindow_le y c Δ hc
  have hcardR : ((univ.filter (fun z : ZMod n => P z = z.val % 2)).card : ℝ) ≤
      (V.card : ℝ) + (W.card : ℝ) := by
    exact_mod_cast hcardN
  linarith

/-- PB-3. `VoteAdvantage`. -/
theorem voteAdvantage : Ecdlp.ParityFourier.VoteAdvantage := by
  intro n _ hn P y c Δ hc
  exact card_vote_correct_ge hn P y c Δ hc

/-- For PB-4: the votes of one step satisfy the hypothesis of PB-1 (`MajorityVote`) with
`Ω = ZMod n`, `good r ↔ pbVote (P (y + r)) c r = y.val % 2` and `δ = ε - (Δ + 1)/n`. -/
theorem vote_half_advantage {n : ℕ} [NeZero n] (hn : Odd n) (P : ZMod n → ℕ) (ε : ℝ)
    (hP : (1 / 2 + ε) * (n : ℝ) ≤
      ((univ.filter (fun z : ZMod n => P z = z.val % 2)).card : ℝ))
    (y : ZMod n) (c : ℚ) (Δ : ℝ) (hc : |(c : ℝ) - (y.val : ℝ)| ≤ Δ) :
    (1 / 2 + (ε - (Δ + 1) / (n : ℝ))) * (Fintype.card (ZMod n) : ℝ) ≤
      ((univ.filter (fun r : ZMod n => pbVote (P (y + r)) c r = y.val % 2)).card : ℝ) := by
  rw [ZMod.card]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have h := card_vote_correct_ge hn P y c Δ hc
  have e : (1 / 2 + (ε - (Δ + 1) / (n : ℝ))) * (n : ℝ) = (1 / 2 + ε) * (n : ℝ) - (Δ + 1) := by
    field_simp
    ring
  linarith

/-- A step decides `p ∈ {0, 1}` when strictly more than half of its `m` votes equal `p`. -/
theorem pbBit_eq_of_majority {n m : ℕ} (r : Fin m → ZMod n) (a : Fin m → ℕ) (c : ℚ) (p : ℕ)
    (hp : p < 2) (h : m < 2 * (univ.filter (fun i => pbVote (a i) c (r i) = p)).card) :
    pbBit r a c = p := by
  unfold pbBit
  interval_cases p
  · have h1 : univ.filter (fun i => pbVote (a i) c (r i) = 1) ⊆
        univ.filter (fun i => ¬ pbVote (a i) c (r i) = 0) := by
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hi
      omega
    have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
      (fun i => pbVote (a i) c (r i) = 0)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    have h3 := Finset.card_le_card h1
    rw [if_neg]
    omega
  · rw [if_pos h]

/-- Contrapositive of `pbBit_eq_of_majority`: if a step does not decide `p ∈ {0, 1}`, at most
half of its votes equal `p`. -/
theorem two_mul_card_le_of_pbBit_ne {n m : ℕ} (r : Fin m → ZMod n) (a : Fin m → ℕ) (c : ℚ)
    (p : ℕ) (hp : p < 2) (h : pbBit r a c ≠ p) :
    2 * (univ.filter (fun i => pbVote (a i) c (r i) = p)).card ≤ m := by
  by_contra h'
  exact h (pbBit_eq_of_majority r a c p hp (by omega))

/-- For PB-4: the shift rows `s` on which a step with answers `P (y + s i)` and guess `c`
does not decide the parity of `y` lie in the event of PB-1 for
`good r ↔ pbVote (P (y + r)) c r = y.val % 2`: at most half of the entries of `s` are good. -/
theorem pbBit_answers_ne_subset {n m : ℕ} [NeZero n] (P : ZMod n → ℕ) (y : ZMod n) (c : ℚ) :
    univ.filter (fun s : Fin m → ZMod n => pbBit s (fun i => P (y + s i)) c ≠ y.val % 2) ⊆
      univ.filter (fun s : Fin m → ZMod n =>
        2 * (univ.filter (fun i => pbVote (P (y + s i)) c (s i) = y.val % 2)).card ≤ m) := by
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact two_mul_card_le_of_pbBit_ne s (fun i => P (y + s i)) c (y.val % 2)
    (Nat.mod_lt _ (by norm_num)) hs

/-- Binary division in `ZMod n`, `n` an odd prime: `2 (y · 2⁻¹).val = y.val + (y.val % 2) n`. -/
theorem two_mul_val_mul_inv_two (n : ℕ) [Fact n.Prime] (h2 : n ≠ 2) (y : ZMod n) :
    2 * (y * (2 : ZMod n)⁻¹).val = y.val + (y.val % 2) * n := by
  have h2z : (2 : ZMod n) ≠ 0 := ProofsF3F4a.two_ne_zero_zmod n h2
  have hodd : n % 2 = 1 := by
    rcases (Fact.out : n.Prime).eq_two_or_odd with h | h
    · exact absurd h h2
    · exact h
  have hy := ZMod.val_lt y
  set v : ℕ := (y.val + (y.val % 2) * n) / 2 with hv
  have h2v : 2 * v = y.val + (y.val % 2) * n := by
    rcases Nat.mod_two_eq_zero_or_one y.val with h | h <;> rw [hv, h] <;> omega
  have hvlt : v < n := by
    rcases Nat.mod_two_eq_zero_or_one y.val with h | h <;> rw [h] at h2v <;> omega
  have hcast : (2 : ZMod n) * (v : ZMod n) = y := by
    have : ((2 * v : ℕ) : ZMod n) = ((y.val + (y.val % 2) * n : ℕ) : ZMod n) := by rw [h2v]
    push_cast at this
    rw [this, ZMod.natCast_self, mul_zero, add_zero, ZMod.natCast_zmod_val]
  have hyv : y * (2 : ZMod n)⁻¹ = (v : ZMod n) := by
    rw [← hcast, mul_comm (2 : ZMod n), mul_assoc, mul_inv_cancel₀ h2z, mul_one]
  rw [hyv, ZMod.val_natCast, Nat.mod_eq_of_lt hvlt, h2v]

/-- For PB-4: a correct bit halves the guess error exactly. With `c' = (c + (y.val % 2) n)/2`
and `y' = y · 2⁻¹`, `c' - y'.val = (c - y.val)/2`. -/
theorem halve_error (n : ℕ) [Fact n.Prime] (h2 : n ≠ 2) (y : ZMod n) (c : ℚ) :
    (c + ((y.val % 2 : ℕ) : ℚ) * (n : ℚ)) / 2 - ((y * (2 : ZMod n)⁻¹).val : ℚ) =
      (c - (y.val : ℚ)) / 2 := by
  have h := two_mul_val_mul_inv_two n h2 y
  have hq : (2 : ℚ) * ((y * (2 : ZMod n)⁻¹).val : ℚ) =
      (y.val : ℚ) + ((y.val % 2 : ℕ) : ℚ) * (n : ℚ) := by
    exact_mod_cast h
  linarith

end Ecdlp.ParityFourier.ProofsPB23
