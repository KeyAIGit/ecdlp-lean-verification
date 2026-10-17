import Ecdlp.Proved.ParityFourier.Statements

/-!
# Proofs of F3 (`Relabel`) and F4a (`HalvingRecovers`)

* F3: if `c x = ±1` and `sigma x = c x * b x`, then `c x * P x = sigma x ↔ P x = b x`
  (cancel the nonzero factor `c x`), so the two filters coincide.
* F4a: with an exact parity oracle, the `i`-th halving state has canonical
  representative `x.val / 2 ^ i`; the bit read there is the `i`-th binary digit of
  `x.val`, and the digits below `L` reassemble `x.val % 2 ^ L = x.val`.
-/

namespace Ecdlp.ParityFourier.ProofsF3F4a

open Finset Ecdlp.ParityFourier

/-- F3. Public relabelling transfers predictor agreement exactly. -/
theorem relabel : Ecdlp.ParityFourier.Relabel := by
  intro X _ sigma c b P hc hs
  congr 1
  apply Finset.filter_congr
  intro x _
  rw [hs x]
  have hne : c x ≠ 0 := by
    rcases hc x with h | h <;> rw [h] <;> decide
  exact ⟨fun h => mul_left_cancel₀ hne h, fun h => by rw [h]⟩

/-- `2 ≠ 0` in `ZMod n` for an odd prime `n`. -/
lemma two_ne_zero_zmod (n : ℕ) [hp : Fact n.Prime] (h2 : n ≠ 2) : (2 : ZMod n) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have hle : n ≤ 2 := Nat.le_of_dvd (by norm_num) h'
  have hge : 2 ≤ n := hp.out.two_le
  omega

/-- One exact halving step: the canonical representative is halved (rounding down). -/
lemma val_halve (n : ℕ) [Fact n.Prime] (h2 : n ≠ 2) (s : ZMod n) :
    ((s - ((s.val % 2 : ℕ) : ZMod n)) * (2 : ZMod n)⁻¹).val = s.val / 2 := by
  have h2z : (2 : ZMod n) ≠ 0 := two_ne_zero_zmod n h2
  have hs : s = ((2 * (s.val / 2) + s.val % 2 : ℕ) : ZMod n) := by
    rw [Nat.div_add_mod, ZMod.natCast_zmod_val]
  have hsub : s - ((s.val % 2 : ℕ) : ZMod n) = (2 : ZMod n) * ((s.val / 2 : ℕ) : ZMod n) := by
    have hrw : s - ((s.val % 2 : ℕ) : ZMod n) =
        ((2 * (s.val / 2) + s.val % 2 : ℕ) : ZMod n) - ((s.val % 2 : ℕ) : ZMod n) := by
      rw [← hs]
    rw [hrw]
    push_cast
    ring
  rw [hsub, mul_comm, ← mul_assoc, inv_mul_cancel₀ h2z, one_mul, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have hlt : s.val < n := ZMod.val_lt s
  omega

/-- The `i`-th halving state has canonical representative `x.val / 2 ^ i`. -/
lemma val_halvingState (n : ℕ) [Fact n.Prime] (h2 : n ≠ 2) (O : ZMod n → ℕ)
    (hO : ∀ y, O y = y.val % 2) (x : ZMod n) :
    ∀ i : ℕ, (halvingState O x i).val = x.val / 2 ^ i := by
  intro i
  induction i with
  | zero => simp [halvingState]
  | succ i ih =>
    simp only [halvingState]
    rw [hO, val_halve n h2, ih, Nat.div_div_eq_div_mul, pow_succ]

/-- Binary digits below `L` reassemble `m % 2 ^ L`. -/
lemma sum_binary_digits (m : ℕ) :
    ∀ L : ℕ, (∑ i ∈ range L, (m / 2 ^ i % 2) * 2 ^ i) = m % 2 ^ L := by
  intro L
  induction L with
  | zero => simp [Nat.mod_one]
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ, mul_comm (2 ^ L)]

/-- F4a. Halving recovery in `ZMod n` with an exact parity oracle. -/
theorem halvingRecovers : Ecdlp.ParityFourier.HalvingRecovers := by
  intro n _ h2 O hO x L hL
  have hterm : ∀ i ∈ range L, O (halvingState O x i) * 2 ^ i = (x.val / 2 ^ i % 2) * 2 ^ i := by
    intro i _
    rw [hO, val_halvingState n h2 O hO x i]
  rw [Finset.sum_congr rfl hterm, sum_binary_digits]
  apply Nat.mod_eq_of_lt
  exact lt_of_lt_of_le (ZMod.val_lt x) hL

end Ecdlp.ParityFourier.ProofsF3F4a
