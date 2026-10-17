import Mathlib
import Ecdlp.Proved.ParityFourier.StatementsC44L
import Ecdlp.Proved.ParityFourier.ProofsF5a
import Ecdlp.Proved.ParityFourier.ProofsC44

/-!
# Proofs of C44-L4 and C44-6x

Proves the frozen statements `Ecdlp.ParityFourier.L1lowBound` and
`Ecdlp.ParityFourier.JConcentrationExplicit` from `Ecdlp.ParityFourier.StatementsC44L`.

Outline:
1. For odd `n = 2m + 1` and `t` with `|2t + 1| ≤ n`, the frequency `h + t` is the cast of
   `z = m + 1 + t`, and `pi z / n = (pi (2t+1)/(2n)) + pi/2`, so by the closed form F5a
   `‖ft sigma (h + t)‖ = 1 / (n |sin (pi (2t+1)/(2n))|)`. Jordan's inequality
   `sin x ≥ (2/pi) x` on `[0, pi/2]` gives `n |sin(...)| ≥ |2t+1|`, hence each term is at most
   `1 / |2t + 1|`.
2. `S_B = sum_{|t| ≤ B} 1/|2t+1| ≤ 2 + log(2B+1) - 1/(2B+1)` by induction on `B`; the step
   needs `2/(u+2) ≤ log((u+2)/u)` for `u = 2B+1`, which is `1 - 1/y ≤ log y`.
3. C44-6x combines C44-6' with step 2.
-/

namespace Ecdlp.ParityFourier.ProofsC44L

open Ecdlp.ParityFourier Finset

/-- One term of the low-pass L1 norm is at most `1 / |2t + 1|`. -/
lemma term_le {n : ℕ} [NeZero n] (hodd : Odd n) (t : ℤ) (ht : |2 * t + 1| ≤ (n : ℤ)) :
    ‖ft (sigmaC (n := n)) (hC n + (t : ZMod n))‖ ≤ 1 / |2 * (t : ℝ) + 1| := by
  obtain ⟨m, hm⟩ := hodd
  have hh : (n + 1) / 2 = m + 1 := by omega
  rw [ProofsC44.hplus, ProofsC44.ft_sigma_intCast,
    ProofsF5a.sigmaHatClosedForm n ⟨m, hm⟩, hh]
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hnm : (n : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hm
  set s : ℝ := 2 * (t : ℝ) + 1 with hs
  -- the angle
  have hangle : Real.pi * ((((m + 1 : ℕ) : ℤ) + t : ℤ) : ℝ) / (n : ℝ)
      = Real.pi * s / (2 * n) + Real.pi / 2 := by
    rw [hs, hnm]
    push_cast
    field_simp
    ring
  rw [hangle, Real.cos_add_pi_div_two, abs_neg]
  -- bounds on |s|
  have hs1 : (1 : ℝ) ≤ |s| := by
    have h1 : (1 : ℤ) ≤ |2 * t + 1| := le_abs.2 (by omega)
    have h2 : ((|2 * t + 1| : ℤ) : ℝ) = |s| := by rw [hs]; push_cast; ring_nf
    rw [← h2]
    exact_mod_cast h1
  have hsn : |s| ≤ (n : ℝ) := by
    have h2 : ((|2 * t + 1| : ℤ) : ℝ) = |s| := by rw [hs]; push_cast; ring_nf
    rw [← h2]
    exact_mod_cast ht
  -- Jordan's inequality
  set y : ℝ := Real.pi * s / (2 * n) with hy
  have hay : |y| = Real.pi * |s| / (2 * n) := by
    rw [hy, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0:ℝ) < 2 * n)]
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have hyle : |y| ≤ Real.pi / 2 := by
    rw [hay, div_le_div_iff₀ (by positivity) (by norm_num)]
    have := Real.pi_pos
    nlinarith
  have hjordan := Real.mul_le_sin hy0 hyle
  have hsinabs : Real.sin |y| ≤ |Real.sin y| := by
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]; exact le_abs_self _
    · rw [abs_of_neg h, Real.sin_neg]; exact neg_le_abs _
  have hkey : |s| ≤ (n : ℝ) * |Real.sin y| := by
    have e : 2 / Real.pi * |y| = |s| / n := by
      rw [hay]
      field_simp
    rw [e] at hjordan
    have h3 : |s| / n ≤ |Real.sin y| := le_trans hjordan hsinabs
    rw [div_le_iff₀ hnR] at h3
    linarith
  exact one_div_le_one_div_of_le (by linarith) hkey

lemma window_succ (B : ℕ) :
    window (B + 1) = insert (-(B : ℤ) - 1) (insert ((B : ℤ) + 1) (window B)) := by
  ext t
  simp only [window, mem_insert, mem_Icc]
  push_cast
  omega

/-- The harmonic-type sum. -/
lemma harm_le (B : ℕ) :
    ∑ t ∈ window B, 1 / |2 * (t : ℝ) + 1|
      ≤ 2 + Real.log (2 * (B : ℝ) + 1) - 1 / (2 * (B : ℝ) + 1) := by
  induction B with
  | zero =>
    simp [window]
    norm_num
  | succ B ih =>
    rw [window_succ, sum_insert, sum_insert]
    · have hu : (0 : ℝ) < 2 * (B : ℝ) + 1 := by positivity
      have e1 : |2 * (((-(B : ℤ) - 1 : ℤ)) : ℝ) + 1| = 2 * (B : ℝ) + 1 := by
        push_cast
        rw [abs_of_neg (by linarith)]
        ring
      have e2 : |2 * ((((B : ℤ) + 1 : ℤ)) : ℝ) + 1| = 2 * (B : ℝ) + 3 := by
        push_cast
        rw [abs_of_pos (by positivity)]
        ring
      rw [e1, e2]
      push_cast
      have hlog : 2 / (2 * (B : ℝ) + 3) ≤
          Real.log (2 * ((B : ℝ) + 1) + 1) - Real.log (2 * (B : ℝ) + 1) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        have h := Real.one_sub_inv_le_log_of_pos
          (by positivity : (0 : ℝ) < (2 * ((B : ℝ) + 1) + 1) / (2 * (B : ℝ) + 1))
        have e : 1 - ((2 * ((B : ℝ) + 1) + 1) / (2 * (B : ℝ) + 1))⁻¹ = 2 / (2 * (B : ℝ) + 3) := by
          field_simp
          ring
        linarith
      have e3 : 2 * ((B : ℝ) + 1) + 1 = 2 * (B : ℝ) + 3 := by ring
      rw [e3] at hlog ⊢
      have e4 : 2 / (2 * (B : ℝ) + 3) = 2 * (1 / (2 * (B : ℝ) + 3)) := by ring
      linarith
    · simp only [window, mem_Icc]
      omega
    · simp only [window, mem_insert, mem_Icc]
      omega

theorem l1lowBound : Ecdlp.ParityFourier.L1lowBound := by
  intro n _ hodd B hB
  have hterm : ∀ t ∈ window B,
      ‖ft (sigmaC (n := n)) (hC n + (t : ZMod n))‖ ≤ 1 / |2 * (t : ℝ) + 1| := by
    intro t ht
    simp only [window, mem_Icc] at ht
    apply term_le hodd t
    rw [abs_le]
    constructor <;> omega
  have hpos : (0 : ℝ) < 1 / (2 * (B : ℝ) + 1) := by positivity
  calc L1low n B
      ≤ ∑ t ∈ window B, 1 / |2 * (t : ℝ) + 1| := sum_le_sum hterm
    _ ≤ 2 + Real.log (2 * (B : ℝ) + 1) - 1 / (2 * (B : ℝ) + 1) := harm_le B
    _ ≤ 2 + Real.log (2 * (B : ℝ) + 1) := by linarith

theorem jConcentrationExplicit : Ecdlp.ParityFourier.JConcentrationExplicit := by
  intro n _ _ hn2 lam hlam B hB hBn
  have hodd : Odd n := (Fact.out : n.Prime).odd_of_ne_two hn2
  have h1 := ProofsC44.jConcentration n hn2 lam hlam B hB
  have hL := l1lowBound n hodd B hBn
  have hL0 : 0 ≤ L1low n B := ProofsC44.L1low_nonneg B
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  refine le_trans h1 ?_
  gcongr ?_ ^ 2 / _
  linarith

end Ecdlp.ParityFourier.ProofsC44L
