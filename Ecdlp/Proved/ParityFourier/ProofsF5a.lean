import Ecdlp.Proved.ParityFourier.StatementsF5

/-!
# Proof of F5a (closed form of the parity-sign spectrum)

For odd `n` put `w = exp(-2 pi i a / n)`. Each summand of `sigmaHat n a` is
`(-w)^k`, so the geometric-sum identity gives `S * (w + 1) = 1 - (-w)^n = 2`
(because `(-w)^n = -w^n = -1`). Writing `theta = pi a / n`, we have
`w + 1 = 2 cos(theta) exp(-i theta)`, hence `‖w + 1‖ = 2 |cos theta|`, so
`‖S‖ * |cos theta| = 1`; in particular `cos theta ≠ 0`, and
`‖sigmaHat n a‖ = (1/n) ‖S‖ = 1 / (n |cos theta|)`.
-/

namespace Ecdlp.ParityFourier.ProofsF5a

open Finset Ecdlp.ParityFourier

theorem sigmaHatClosedForm : Ecdlp.ParityFourier.SigmaHatClosedForm := by
  intro n hn a
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  set w : ℂ := Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) / (n : ℂ)) with hw
  -- each summand is `(-w)^k`
  have hterm : ∀ k : ℕ, ((-1 : ℂ) ^ k) *
      Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (k : ℂ) / (n : ℂ)) = (-w) ^ k := by
    intro k
    rw [neg_eq_neg_one_mul w, mul_pow, hw, ← Complex.exp_nat_mul]
    congr 2
    ring
  have hS : ∑ k ∈ range n, ((-1 : ℂ) ^ k) *
      Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (k : ℂ) / (n : ℂ)) =
      ∑ k ∈ range n, (-w) ^ k := sum_congr rfl (fun k _ => hterm k)
  -- `w` is an `n`-th root of unity
  have hwn : w ^ n = 1 := by
    rw [hw, ← Complex.exp_nat_mul]
    have : (n : ℂ) * (-2 * Real.pi * Complex.I * (a : ℂ) / (n : ℂ)) =
        ((-a : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      field_simp
      push_cast
      ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  -- geometric sum
  have hgeom : (∑ k ∈ range n, (-w) ^ k) * (w + 1) = 2 := by
    have h := geom_sum_mul (-w) n
    rw [Odd.neg_pow hn, hwn] at h
    linear_combination -h
  -- `w + 1 = 2 cos(theta) exp(-i theta)`
  set θ : ℝ := Real.pi * (a : ℝ) / (n : ℝ) with hθ
  have hwplus : w + 1 = (2 * Complex.cos (θ : ℂ)) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.two_cos]
    have e1 : Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      push_cast
      ring_nf
      exact Complex.exp_zero
    have e2 : Complex.exp (-(θ : ℂ) * Complex.I) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) = w := by
      rw [← Complex.exp_add, hw, hθ]
      congr 1
      push_cast
      field_simp
      ring
    linear_combination -e1 - e2
  have hnormw : ‖w + 1‖ = 2 * |Real.cos θ| := by
    rw [hwplus, norm_mul, Complex.norm_exp_ofReal_mul_I, norm_mul, ← Complex.ofReal_cos,
      Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hkey : ‖∑ k ∈ range n, (-w) ^ k‖ * |Real.cos θ| = 1 := by
    have h := congrArg norm hgeom
    rw [norm_mul, hnormw] at h
    norm_num at h
    linarith
  have hcos : |Real.cos θ| ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hkey
    exact zero_ne_one hkey
  unfold sigmaHat
  rw [hS, norm_mul, norm_div, norm_one, Complex.norm_natCast]
  field_simp
  linarith
