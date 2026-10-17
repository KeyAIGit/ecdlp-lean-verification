import Ecdlp.Proved.ParityFourier.Statements

/-!
# Proofs of F1 (carry identity and symmetries of `J` and `g`)

Proves the frozen statements `CarrySum`, `CarrySign`, `JEven`, `GOdd`,
`GInvariant` and `JOrbitProduct` from `Ecdlp.Proved.ParityFourier.Statements`.
-/

namespace Ecdlp.ParityFourier.ProofsF1

open Ecdlp.ParityFourier

/-- `sgn k` squares to `1`. -/
lemma sgn_mul_self {n : ℕ} (k : ZMod n) : sgn k * sgn k = 1 := by
  unfold sgn
  rw [← mul_pow]
  norm_num

/-- A root of `X^2 + X + 1` is a cube root of unity, in any `ZMod n`. -/
lemma lam_cube {n : ℕ} {lam : ZMod n} (h : lam ^ 2 + lam + 1 = 0) : lam ^ 3 = 1 := by
  have e : lam ^ 3 - 1 = (lam - 1) * (lam ^ 2 + lam + 1) := by ring
  rw [h, mul_zero, sub_eq_zero] at e
  exact e

/-- For odd `n` and `y ≠ 0`, negation flips the parity sign. -/
lemma sgn_neg {n : ℕ} [NeZero n] (hn : Odd n) {y : ZMod n} (hy : y ≠ 0) :
    sgn (-y) = - sgn y := by
  have hv : (-y).val = n - y.val := by
    haveI : NeZero y := ⟨hy⟩
    exact ZMod.val_neg_of_ne_zero y
  have hlt : y.val < n := ZMod.val_lt y
  have hsplit : (-1 : ℤ) ^ n = (-1) ^ (n - y.val) * (-1) ^ y.val := by
    rw [← pow_add, Nat.sub_add_cancel hlt.le]
  rw [hn.neg_one_pow] at hsplit
  have hsq : ((-1 : ℤ) ^ y.val) * ((-1) ^ y.val) = 1 := sgn_mul_self y
  unfold sgn
  rw [hv]
  calc (-1 : ℤ) ^ (n - y.val)
      = (-1) ^ (n - y.val) * ((-1) ^ y.val * (-1) ^ y.val) := by rw [hsq, mul_one]
    _ = ((-1) ^ (n - y.val) * (-1) ^ y.val) * (-1) ^ y.val := by ring
    _ = - (-1) ^ y.val := by rw [← hsplit]; ring

lemma odd_of_prime {n : ℕ} [hp : Fact n.Prime] (hn : n ≠ 2) : Odd n :=
  hp.out.odd_of_ne_two hn

lemma lam_ne_zero {n : ℕ} [Fact n.Prime] {lam : ZMod n} (h : lam ^ 2 + lam + 1 = 0) :
    lam ≠ 0 := by
  rintro rfl
  simp at h

/-- The three representatives sum to `0` in `ZMod n`. -/
lemma val_sum_cast {n : ℕ} [NeZero n] {lam : ZMod n} (hlam : lam ^ 2 + lam + 1 = 0)
    (k : ZMod n) :
    ((k.val + (lam * k).val + (lam ^ 2 * k).val : ℕ) : ZMod n) = 0 := by
  rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]
  have e : k + lam * k + lam ^ 2 * k = (lam ^ 2 + lam + 1) * k := by ring
  rw [e, hlam, zero_mul]

/-- F1a. -/
theorem carrySum : Ecdlp.ParityFourier.CarrySum := by
  intro n _ hn2 lam hlam k hk
  haveI : NeZero n := ⟨(Fact.out : n.Prime).ne_zero⟩
  have hl := lam_ne_zero hlam
  have h1 : lam * k ≠ 0 := mul_ne_zero hl hk
  have h2 : lam ^ 2 * k ≠ 0 := mul_ne_zero (pow_ne_zero 2 hl) hk
  have ha0 : k.val ≠ 0 := fun h => hk ((ZMod.val_eq_zero k).1 h)
  have hb0 : (lam * k).val ≠ 0 := fun h => h1 ((ZMod.val_eq_zero _).1 h)
  have hc0 : (lam ^ 2 * k).val ≠ 0 := fun h => h2 ((ZMod.val_eq_zero _).1 h)
  have ha := ZMod.val_lt k
  have hb := ZMod.val_lt (lam * k)
  have hc := ZMod.val_lt (lam ^ 2 * k)
  obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff _ n).1 (val_sum_cast hlam k)
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [Nat.mul_zero] at hm
      omega
    · exact h
  have hm3 : m < 3 := by
    by_contra h
    have := Nat.mul_le_mul_left n (Nat.le_of_not_lt h)
    omega
  interval_cases m
  · left
    omega
  · right
    omega

/-- F1b. -/
theorem carrySign : Ecdlp.ParityFourier.CarrySign := by
  intro n _ hn2 lam hlam k hk
  have hodd := odd_of_prime hn2
  have hg : g lam k = (-1) ^ (k.val + (lam * k).val + (lam ^ 2 * k).val) := by
    unfold g J sgn
    rw [pow_add, pow_add, mul_assoc]
  rcases carrySum n hn2 lam hlam k hk with h | h
  · rw [if_pos h, hg, h, hodd.neg_one_pow]
  · have hne : k.val + (lam * k).val + (lam ^ 2 * k).val ≠ n := by
      rw [h]
      have := (Fact.out : n.Prime).pos
      omega
    rw [if_neg hne, hg, h, pow_mul]
    norm_num

/-- F1c. -/
theorem jEven : Ecdlp.ParityFourier.JEven := by
  intro n _ hn2 lam hlam k
  haveI : NeZero n := ⟨(Fact.out : n.Prime).ne_zero⟩
  by_cases hk : k = 0
  · subst hk
    simp
  have hodd := odd_of_prime hn2
  have hl := lam_ne_zero hlam
  have h1 : lam * k ≠ 0 := mul_ne_zero hl hk
  have h2 : lam ^ 2 * k ≠ 0 := mul_ne_zero (pow_ne_zero 2 hl) hk
  unfold J
  rw [mul_neg, mul_neg, sgn_neg hodd h1, sgn_neg hodd h2]
  ring

/-- F1d. -/
theorem gOdd : Ecdlp.ParityFourier.GOdd := by
  intro n _ hn2 lam hlam k hk
  haveI : NeZero n := ⟨(Fact.out : n.Prime).ne_zero⟩
  have hJ := jEven n hn2 lam hlam k
  unfold g
  rw [hJ, sgn_neg (odd_of_prime hn2) hk]
  ring

/-- F1e. -/
theorem gInvariant : Ecdlp.ParityFourier.GInvariant := by
  intro n lam hlam k
  have h3 := lam_cube hlam
  have e1 : lam * (lam * k) = lam ^ 2 * k := by ring
  have e2 : lam ^ 2 * (lam * k) = k := by
    have e : lam ^ 2 * (lam * k) = lam ^ 3 * k := by ring
    rw [e, h3, one_mul]
  unfold g J
  rw [e1, e2]
  ring

/-- F1f. -/
theorem jOrbitProduct : Ecdlp.ParityFourier.JOrbitProduct := by
  intro n lam hlam k
  have h3 := lam_cube hlam
  have e1 : lam * (lam * k) = lam ^ 2 * k := by ring
  have e2 : lam ^ 2 * (lam * k) = k := by
    have e : lam ^ 2 * (lam * k) = lam ^ 3 * k := by ring
    rw [e, h3, one_mul]
  have e3 : lam * (lam ^ 2 * k) = k := by
    have e : lam * (lam ^ 2 * k) = lam ^ 3 * k := by ring
    rw [e, h3, one_mul]
  have e4 : lam ^ 2 * (lam ^ 2 * k) = lam * k := by
    have e : lam ^ 2 * (lam ^ 2 * k) = lam ^ 3 * (lam * k) := by ring
    rw [e, h3, one_mul]
  unfold J
  rw [e1, e2, e3, e4]
  have hre : sgn (lam * k) * sgn (lam ^ 2 * k) * (sgn (lam ^ 2 * k) * sgn k) *
      (sgn k * sgn (lam * k)) =
      (sgn (lam * k) * sgn (lam * k)) * (sgn (lam ^ 2 * k) * sgn (lam ^ 2 * k)) *
        (sgn k * sgn k) := by ring
  rw [hre, sgn_mul_self, sgn_mul_self, sgn_mul_self]
  norm_num

end Ecdlp.ParityFourier.ProofsF1
