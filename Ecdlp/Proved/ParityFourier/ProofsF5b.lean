import Ecdlp.Proved.ParityFourier.StatementsF5

/-!
# Proof of F5b (tail bound for the Fourier mass of the parity sign)

Proves the frozen statement `SigmaTail` from `Ecdlp.ParityFourier.StatementsF5`.

The argument is self-contained (it does not import `ProofsF5a`):

1. geometric sum: `sigmaHat n a * (1 + ω) = 2 / n` with `ω = exp(-2πi a/n)`, for odd `n`;
2. `‖1 + ω‖ = 2 |cos(π a / n)|`, hence `‖sigmaHat n a‖ * (n |cos(π a / n)|) = 1`;
3. at `a = h ± t` the cosine is `∓ sin(π m / (2n))` with `m = 2t ± 1 ≤ n`, and Jordan's
   inequality gives `n |cos(π a / n)| ≥ m`, so each squared coefficient is at most `1 / m^2`;
4. `1/(2t+1)^2 + 1/(2t-1)^2 ≤ 1/(2(t-1)) - 1/(2t)`, which telescopes to at most `1/(2B)`.
-/

namespace Ecdlp.ParityFourier.ProofsF5b

open Ecdlp.ParityFourier Finset

/-- Geometric-sum identity: `sigmaHat n a * (1 + ω) = 2 / n`. -/
lemma sigmaHat_mul_one_add (n : ℕ) (hn : Odd n) (a : ℤ) :
    sigmaHat n a * (1 + Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) / (n : ℂ)))
      = 2 / (n : ℂ) := by
  set ω := Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) / (n : ℂ)) with hω
  have hn0 : (n : ℂ) ≠ 0 := by
    have : n ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hn)
    exact_mod_cast this
  have hterm : ∀ k : ℕ,
      ((-1 : ℂ) ^ k) * Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (k : ℂ) / (n : ℂ))
        = (-ω) ^ k := by
    intro k
    rw [neg_pow ω k, hω, ← Complex.exp_nat_mul]
    congr 2
    ring
  have hωn : ω ^ n = 1 := by
    rw [hω, ← Complex.exp_nat_mul]
    have : (n : ℂ) * (-2 * Real.pi * Complex.I * (a : ℂ) / (n : ℂ))
        = ((-a : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hgeom := geom_sum_mul (-ω) n
  rw [neg_pow, hωn, hn.neg_one_pow] at hgeom
  unfold sigmaHat
  simp_rw [hterm]
  rw [mul_assoc]
  have hS : (∑ i ∈ range n, (-ω) ^ i) * (1 + ω) = 2 := by
    linear_combination (-1 : ℂ) * hgeom
  rw [hS]
  ring

/-- `‖1 + exp(-2πi a/n)‖ = 2 |cos(π a / n)|`. -/
lemma norm_one_add_exp (n : ℕ) (a : ℤ) :
    ‖1 + Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) / (n : ℂ))‖
      = 2 * |Real.cos (Real.pi * (a : ℝ) / (n : ℝ))| := by
  set θ : ℝ := Real.pi * (a : ℝ) / (n : ℝ) with hθ
  have h1 : 1 + Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) / (n : ℂ))
      = Complex.exp ((-θ : ℝ) * Complex.I) * (2 * Complex.cos (θ : ℂ)) := by
    rw [Complex.two_cos, mul_add, ← Complex.exp_add, ← Complex.exp_add]
    have e1 : ((-θ : ℝ) : ℂ) * Complex.I + (θ : ℂ) * Complex.I = 0 := by push_cast; ring
    have e2 : ((-θ : ℝ) : ℂ) * Complex.I + -(θ : ℂ) * Complex.I
        = -2 * Real.pi * Complex.I * (a : ℂ) / (n : ℂ) := by
      rw [hθ]; push_cast; ring
    rw [e1, e2, Complex.exp_zero]
  rw [h1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, ← Complex.ofReal_cos,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- `‖sigmaHat n a‖ * (n |cos(π a / n)|) = 1` for odd `n`. -/
lemma norm_sigmaHat_mul (n : ℕ) (hn : Odd n) (a : ℤ) :
    ‖sigmaHat n a‖ * ((n : ℝ) * |Real.cos (Real.pi * (a : ℝ) / (n : ℝ))|) = 1 := by
  have h := congrArg norm (sigmaHat_mul_one_add n hn a)
  rw [norm_mul, norm_one_add_exp, norm_div] at h
  have hn0 : (0 : ℝ) < n := by
    have : n ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hn)
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [Complex.norm_natCast] at h
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2] at h
  field_simp at h
  linear_combination h

/-- If `n |cos(π a/n)| ≥ m > 0` then `‖sigmaHat n a‖ ^ 2 ≤ 1 / m ^ 2`. -/
lemma sq_norm_le (n : ℕ) (hn : Odd n) (a : ℤ) (m : ℝ) (hm : 0 < m)
    (hc : m ≤ (n : ℝ) * |Real.cos (Real.pi * (a : ℝ) / (n : ℝ))|) :
    ‖sigmaHat n a‖ ^ 2 ≤ 1 / m ^ 2 := by
  have h := norm_sigmaHat_mul n hn a
  set c := (n : ℝ) * |Real.cos (Real.pi * (a : ℝ) / (n : ℝ))|
  have hc0 : 0 < c := lt_of_lt_of_le hm hc
  have hs : ‖sigmaHat n a‖ = 1 / c := by
    field_simp
    linarith
  rw [hs, div_pow, one_pow]
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ hm.le hc 2

/-- Jordan's inequality in the form `n sin(π m / (2n)) ≥ m` for `0 ≤ m ≤ n`. -/
lemma jordan (n : ℝ) (hn : 0 < n) (m : ℝ) (hm0 : 0 ≤ m) (hmn : m ≤ n) :
    m ≤ n * Real.sin (Real.pi * m / (2 * n)) := by
  have hx0 : 0 ≤ Real.pi * m / (2 * n) := by positivity
  have hx1 : Real.pi * m / (2 * n) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  have hj := Real.mul_le_sin hx0 hx1
  have : 2 / Real.pi * (Real.pi * m / (2 * n)) = m / n := by
    field_simp
  rw [this, div_le_iff₀ hn] at hj
  linarith

/-- Bound on the `h + t` coefficient. -/
lemma plus_bound (N t : ℕ) (ht : t ≤ N) :
    ‖sigmaHat (2 * N + 1) (((2 * N + 1 + 1) / 2 : ℕ) + (t : ℤ))‖ ^ 2
      ≤ 1 / (2 * (t : ℝ) + 1) ^ 2 := by
  have hodd : Odd (2 * N + 1) := odd_two_mul_add_one N
  apply sq_norm_le _ hodd _ _ (by positivity)
  have hh : ((2 * N + 1 + 1) / 2 : ℕ) = N + 1 := by omega
  rw [hh]
  have hn : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hang : Real.pi * ((((N + 1 : ℕ) : ℤ) + (t : ℤ) : ℤ) : ℝ) / ((2 * N + 1 : ℕ) : ℝ)
      = Real.pi * (2 * (t : ℝ) + 1) / (2 * ((2 * N + 1 : ℕ) : ℝ)) + Real.pi / 2 := by
    push_cast
    field_simp
    ring
  rw [hang, Real.cos_add_pi_div_two, abs_neg]
  have hj := jordan ((2 * N + 1 : ℕ) : ℝ) hn (2 * (t : ℝ) + 1) (by positivity)
    (by push_cast; have : (t : ℝ) ≤ N := by exact_mod_cast ht
        linarith)
  have hs : 0 ≤ Real.sin (Real.pi * (2 * (t : ℝ) + 1) / (2 * ((2 * N + 1 : ℕ) : ℝ))) := by
    nlinarith
  rw [abs_of_nonneg hs]
  exact hj

/-- Bound on the `h - t` coefficient. -/
lemma minus_bound (N t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ N) :
    ‖sigmaHat (2 * N + 1) (((2 * N + 1 + 1) / 2 : ℕ) - (t : ℤ))‖ ^ 2
      ≤ 1 / (2 * (t : ℝ) - 1) ^ 2 := by
  have hodd : Odd (2 * N + 1) := odd_two_mul_add_one N
  have ht1r : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  apply sq_norm_le _ hodd _ _ (by linarith)
  have hh : ((2 * N + 1 + 1) / 2 : ℕ) = N + 1 := by omega
  rw [hh]
  have hn : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hang : Real.pi * ((((N + 1 : ℕ) : ℤ) - (t : ℤ) : ℤ) : ℝ) / ((2 * N + 1 : ℕ) : ℝ)
      = Real.pi / 2 - Real.pi * (2 * (t : ℝ) - 1) / (2 * ((2 * N + 1 : ℕ) : ℝ)) := by
    push_cast
    field_simp
    ring
  rw [hang, Real.cos_pi_div_two_sub]
  have hj := jordan ((2 * N + 1 : ℕ) : ℝ) hn (2 * (t : ℝ) - 1) (by linarith)
    (by push_cast; have : (t : ℝ) ≤ N := by exact_mod_cast ht
        linarith)
  have hs : 0 ≤ Real.sin (Real.pi * (2 * (t : ℝ) - 1) / (2 * ((2 * N + 1 : ℕ) : ℝ))) := by
    nlinarith
  rw [abs_of_nonneg hs]
  exact hj

/-- Pointwise telescoping majorant, for `t ≥ 2`. -/
lemma term_le (t : ℝ) (ht : 2 ≤ t) :
    1 / (2 * t + 1) ^ 2 + 1 / (2 * t - 1) ^ 2 ≤ 1 / (2 * (t - 1)) - 1 / (2 * t) := by
  have h1 : 1 / (2 * t + 1) ^ 2 ≤ 1 / (2 * t - 1) ^ 2 := by
    apply one_div_le_one_div_of_le (by nlinarith)
    nlinarith
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  have h2 : 1 / (2 * (t - 1)) - 1 / (2 * t) = 1 / (2 * t * (t - 1)) := by
    field_simp
    ring
  have h3 : 2 * (1 / (2 * t - 1) ^ 2) ≤ 1 / (2 * t * (t - 1)) := by
    rw [mul_one_div, div_le_div_iff₀ (by nlinarith) (by nlinarith)]
    nlinarith
  linarith

/-- Telescoping sum. -/
lemma telescope (B : ℕ) (M : ℕ) (hM : B ≤ M) :
    ∑ t ∈ Icc (B + 1) M, (1 / (2 * ((t : ℝ) - 1)) - 1 / (2 * (t : ℝ)))
      = 1 / (2 * (B : ℝ)) - 1 / (2 * (M : ℝ)) := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hBM ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

theorem sigmaTail : Ecdlp.ParityFourier.SigmaTail := by
  intro n hn B hB
  obtain ⟨N, rfl⟩ := hn
  have hN : (2 * N + 1 - 1) / 2 = N := by omega
  rw [hN]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  calc
    (∑ t ∈ Icc (B + 1) N,
        (‖sigmaHat (2 * N + 1) (((2 * N + 1 + 1) / 2 : ℕ) + (t : ℤ))‖ ^ 2 +
         ‖sigmaHat (2 * N + 1) (((2 * N + 1 + 1) / 2 : ℕ) - (t : ℤ))‖ ^ 2))
        ≤ ∑ t ∈ Icc (B + 1) N, (1 / (2 * ((t : ℝ) - 1)) - 1 / (2 * (t : ℝ))) := by
      apply sum_le_sum
      intro t ht
      rw [mem_Icc] at ht
      have ht2 : (2 : ℝ) ≤ t := by
        have : 2 ≤ t := by omega
        exact_mod_cast this
      have hp := plus_bound N t ht.2
      have hm := minus_bound N t (by omega) ht.2
      have := term_le (t : ℝ) ht2
      linarith
    _ ≤ 1 / (B : ℝ) := by
      rcases le_or_gt B N with hBN | hBN
      · rw [telescope B N hBN]
        have hNr : (0 : ℝ) < N := by
          have : 0 < N := by omega
          exact_mod_cast this
        have : 0 < 1 / (2 * (N : ℝ)) := by positivity
        have : 1 / (2 * (B : ℝ)) ≤ 1 / (B : ℝ) := by
          apply one_div_le_one_div_of_le hBr
          linarith
        linarith
      · rw [Icc_eq_empty (by omega), sum_empty]
        positivity

end Ecdlp.ParityFourier.ProofsF5b
