import Ecdlp.Proved.ParityFourier.Statements

/-!
# F2: the balance identity of `J`

Proof of `Ecdlp.ParityFourier.JBalance`.

Write `s0 = sgn k`, `s1 = sgn (lam k)`, `s2 = sgn (lam^2 k)`. Since `lam ^ 3 = 1`,
`J(k) + J(lam k) + J(lam^2 k) = s1 s2 + s2 s0 + s0 s1`, which is `3` when
`s0 = s1 = s2` and `-1` otherwise. Multiplication by the unit `lam` (and by
`lam ^ 2`) permutes the nonzero residues, so the three sums over `k ≠ 0` agree,
giving `3 * sum J = 3 M - (N - M) = 4 M - N` with `N = n - 1`.
-/

namespace Ecdlp.ParityFourier.ProofsF2

open Finset

/-- The parity sign takes only the values `1` and `-1`. -/
theorem sgn_cases {n : ℕ} (k : ZMod n) : Ecdlp.ParityFourier.sgn k = 1 ∨ Ecdlp.ParityFourier.sgn k = -1 := by
  unfold Ecdlp.ParityFourier.sgn
  exact neg_one_pow_eq_or ℤ k.val

/-- A root of `X^2 + X + 1` is a cube root of unity. -/
theorem lam_cube {n : ℕ} {lam : ZMod n} (h : lam ^ 2 + lam + 1 = 0) : lam ^ 3 = 1 := by
  have e : lam ^ 3 - 1 = (lam - 1) * (lam ^ 2 + lam + 1) := by ring
  rw [h, mul_zero] at e
  exact sub_eq_zero.mp e

/-- `J(lam k) = sgn(lam^2 k) * sgn(k)`. -/
theorem J_mul_lam {n : ℕ} {lam : ZMod n} (h : lam ^ 2 + lam + 1 = 0) (k : ZMod n) :
    Ecdlp.ParityFourier.J lam (lam * k) = Ecdlp.ParityFourier.sgn (lam ^ 2 * k) * Ecdlp.ParityFourier.sgn k := by
  have h3 := lam_cube h
  unfold Ecdlp.ParityFourier.J
  have e1 : lam * (lam * k) = lam ^ 2 * k := by ring
  have e2 : lam ^ 2 * (lam * k) = k := by
    calc lam ^ 2 * (lam * k) = lam ^ 3 * k := by ring
      _ = k := by rw [h3, one_mul]
  rw [e1, e2]

/-- `J(lam^2 k) = sgn(k) * sgn(lam k)`. -/
theorem J_mul_lam_sq {n : ℕ} {lam : ZMod n} (h : lam ^ 2 + lam + 1 = 0) (k : ZMod n) :
    Ecdlp.ParityFourier.J lam (lam ^ 2 * k) = Ecdlp.ParityFourier.sgn k * Ecdlp.ParityFourier.sgn (lam * k) := by
  have h3 := lam_cube h
  unfold Ecdlp.ParityFourier.J
  have e1 : lam * (lam ^ 2 * k) = k := by
    calc lam * (lam ^ 2 * k) = lam ^ 3 * k := by ring
      _ = k := by rw [h3, one_mul]
  have e2 : lam ^ 2 * (lam ^ 2 * k) = lam * k := by
    calc lam ^ 2 * (lam ^ 2 * k) = lam ^ 3 * (lam * k) := by ring
      _ = lam * k := by rw [h3, one_mul]
  rw [e1, e2]

/-- For signs `a, b, c ∈ {±1}`: `bc + ca + ab` is `3` if all agree and `-1` otherwise. -/
theorem orbit_sum (a b c : ℤ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) :
    b * c + c * a + a * b = 4 * (if a = b ∧ b = c then 1 else 0) - 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    norm_num

/-- Multiplication by a nonzero `c` permutes the nonzero residues. -/
theorem sum_mul_left {n : ℕ} [Fact n.Prime] (c : ZMod n) (hc : c ≠ 0) (f : ZMod n → ℤ) :
    ∑ k ∈ univ.erase (0 : ZMod n), f (c * k) = ∑ k ∈ univ.erase (0 : ZMod n), f k := by
  refine Finset.sum_nbij' (fun k => c * k) (fun k => c⁻¹ * k) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_erase, mem_univ, and_true] at ha ⊢
    exact mul_ne_zero hc ha
  · intro a ha
    simp only [mem_erase, mem_univ, and_true] at ha ⊢
    exact mul_ne_zero (inv_ne_zero hc) ha
  · intro a _
    exact inv_mul_cancel_left₀ hc a
  · intro a _
    exact mul_inv_cancel_left₀ hc a
  · intro a _
    rfl

/-- F2. Balance identity of `J`. -/
theorem jBalance : Ecdlp.ParityFourier.JBalance := by
  intro n _ _ lam h
  have hlam : lam ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  have hlam2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam
  have s1 : ∑ k ∈ univ.erase (0 : ZMod n), Ecdlp.ParityFourier.J lam (lam * k)
      = ∑ k ∈ univ.erase (0 : ZMod n), Ecdlp.ParityFourier.J lam k :=
    sum_mul_left lam hlam _
  have s2 : ∑ k ∈ univ.erase (0 : ZMod n), Ecdlp.ParityFourier.J lam (lam ^ 2 * k)
      = ∑ k ∈ univ.erase (0 : ZMod n), Ecdlp.ParityFourier.J lam k :=
    sum_mul_left (lam ^ 2) hlam2 _
  have key : ∀ k : ZMod n,
      Ecdlp.ParityFourier.J lam k + Ecdlp.ParityFourier.J lam (lam * k) + Ecdlp.ParityFourier.J lam (lam ^ 2 * k)
        = 4 * (if (Ecdlp.ParityFourier.sgn k = Ecdlp.ParityFourier.sgn (lam * k) ∧
              Ecdlp.ParityFourier.sgn (lam * k) = Ecdlp.ParityFourier.sgn (lam ^ 2 * k)) then (1 : ℤ) else 0)
          - 1 := by
    intro k
    rw [J_mul_lam h, J_mul_lam_sq h]
    unfold Ecdlp.ParityFourier.J
    exact orbit_sum _ _ _ (sgn_cases k) (sgn_cases _) (sgn_cases _)
  have hn : 1 ≤ n := (Fact.out : n.Prime).one_lt.le
  calc 3 * ∑ k ∈ univ.erase (0 : ZMod n), Ecdlp.ParityFourier.J lam k
      = ∑ k ∈ univ.erase (0 : ZMod n), Ecdlp.ParityFourier.J lam k
        + ∑ k ∈ univ.erase (0 : ZMod n), Ecdlp.ParityFourier.J lam (lam * k)
        + ∑ k ∈ univ.erase (0 : ZMod n), Ecdlp.ParityFourier.J lam (lam ^ 2 * k) := by
        rw [s1, s2]; ring
    _ = ∑ k ∈ univ.erase (0 : ZMod n), (Ecdlp.ParityFourier.J lam k + Ecdlp.ParityFourier.J lam (lam * k)
          + Ecdlp.ParityFourier.J lam (lam ^ 2 * k)) := by
        rw [sum_add_distrib, sum_add_distrib]
    _ = ∑ k ∈ univ.erase (0 : ZMod n),
          (4 * (if (Ecdlp.ParityFourier.sgn k = Ecdlp.ParityFourier.sgn (lam * k) ∧
              Ecdlp.ParityFourier.sgn (lam * k) = Ecdlp.ParityFourier.sgn (lam ^ 2 * k)) then (1 : ℤ) else 0)
            - 1) :=
        sum_congr rfl (fun k _ => key k)
    _ = 4 * (((univ.erase (0 : ZMod n)).filter
              (fun k => Ecdlp.ParityFourier.sgn k = Ecdlp.ParityFourier.sgn (lam * k) ∧
                Ecdlp.ParityFourier.sgn (lam * k) = Ecdlp.ParityFourier.sgn (lam ^ 2 * k))).card : ℤ)
          - ((n : ℤ) - 1) := by
        rw [sum_sub_distrib, ← mul_sum, sum_boole, sum_const, card_erase_of_mem (mem_univ _),
          card_univ, ZMod.card]
        simp [Nat.cast_sub hn]

end Ecdlp.ParityFourier.ProofsF2
