import Ecdlp.Proved.ParityFourier.Statements

/-!
# F4b: halving recovery in an additive group

Proof of `Ecdlp.ParityFourier.GroupHalvingRecovers`. The halving chain started at
`x.val • G` stays at `(x.val / 2 ^ i) • G`, so the bit read at step `i` is the
`i`-th binary digit of `x.val`, and the digit sum over `L` steps is
`x.val % 2 ^ L = x.val`.
-/

namespace Ecdlp.ParityFourier.ProofsF4b

open Finset

/-- Binary digit sum: `∑_{i<L} (a / 2^i % 2) * 2^i = a % 2^L`. -/
theorem digitSum_eq_mod (a : ℕ) :
    ∀ L : ℕ, (∑ i ∈ range L, (a / 2 ^ i % 2) * 2 ^ i) = a % 2 ^ L
  | 0 => by simp [Nat.mod_one]
  | L + 1 => by
    rw [sum_range_succ, digitSum_eq_mod a L, Nat.mod_pow_succ, Nat.mul_comm (2 ^ L)]

/-- Multiplying by `2 h` with `2 h ≡ 1 (mod n)` is the identity on multiples of `G`. -/
theorem two_h_nsmul {A : Type} [AddCommGroup A] (G : A) (n : ℕ)
    (hG : addOrderOf G = n) (h : ℕ) (hh : (2 * h) % n = 1) (k : ℕ) :
    (h * (2 * k)) • G = k • G := by
  have hdiv := Nat.div_add_mod (2 * h) n
  rw [hh] at hdiv
  have e : h * (2 * k) = (k * ((2 * h) / n)) * n + k := by
    calc h * (2 * k) = k * (2 * h) := by ring
      _ = k * (n * ((2 * h) / n) + 1) := by rw [hdiv]
      _ = (k * ((2 * h) / n)) * n + k := by ring
  rw [e, add_nsmul, mul_nsmul', ← hG, addOrderOf_nsmul_eq_zero, nsmul_zero, zero_add]

/-- The halving chain stays at `(x.val / 2 ^ i) • G`. -/
theorem state_eq {A : Type} [AddCommGroup A] (G : A) (n : ℕ)
    (hG : addOrderOf G = n) (h : ℕ) (hh : (2 * h) % n = 1)
    (O : A → ℕ) (hO : ∀ y : ZMod n, O (y.val • G) = y.val % 2) (x : ZMod n) :
    ∀ i : ℕ, groupHalvingState O G h (x.val • G) i = (x.val / 2 ^ i) • G
  | 0 => by simp [groupHalvingState]
  | i + 1 => by
    have ih := state_eq G n hG h hh O hO x i
    set m := x.val / 2 ^ i with hm
    have hmlt : m < n := by
      have hx : x.val < n := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          simp at hh
        · haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hpos⟩
          exact ZMod.val_lt x
      exact lt_of_le_of_lt (Nat.div_le_self _ _) hx
    have hOm : O (m • G) = m % 2 := by
      have := hO (m : ZMod n)
      rwa [ZMod.val_cast_of_lt hmlt] at this
    have hsplit : m = 2 * (m / 2) + m % 2 := (Nat.div_add_mod m 2).symm
    show h • (groupHalvingState O G h (x.val • G) i
        - (O (groupHalvingState O G h (x.val • G) i)) • G) = (x.val / 2 ^ (i + 1)) • G
    rw [ih, hOm]
    have hsub : m • G - (m % 2) • G = (2 * (m / 2)) • G := by
      have hmG : m • G = (2 * (m / 2)) • G + (m % 2) • G := by
        rw [← add_nsmul, ← hsplit]
      rw [hmG, add_sub_cancel_right]
    rw [hsub, ← mul_nsmul', two_h_nsmul G n hG h hh, pow_succ, ← Nat.div_div_eq_div_mul]

theorem groupHalvingRecovers : Ecdlp.ParityFourier.GroupHalvingRecovers := by
  intro A _ G n _ _ hG h hh O hO x L hL
  have hstate := state_eq G n hG h hh O hO x
  have hbit : ∀ i, O (groupHalvingState O G h (x.val • G) i) = x.val / 2 ^ i % 2 := by
    intro i
    rw [hstate i]
    have hmlt : x.val / 2 ^ i < n :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (ZMod.val_lt x)
    have := hO ((x.val / 2 ^ i : ℕ) : ZMod n)
    rwa [ZMod.val_cast_of_lt hmlt] at this
  simp_rw [hbit]
  rw [digitSum_eq_mod]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt x) hL)

end Ecdlp.ParityFourier.ProofsF4b
