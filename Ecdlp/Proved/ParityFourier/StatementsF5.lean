import Mathlib

/-!
# Frozen statements F5 (spectrum of the parity sign; C44 Lemmas 1-2)

This file fixes the statements before any proof is searched. Proof files must
not edit it.

* `sigmaHat n a = (1/n) * sum_{k < n} (-1)^k * exp(-2 pi i a k / n)` is the
  normalised Fourier coefficient of the parity sign `sigma` on `Z/n`.
* F5a: for odd `n` and every integer `a`,
  `|sigmaHat n a| = 1 / (n |cos(pi a / n)|)`.
* F5b: with `h = (n + 1) / 2`, the Fourier mass of `sigma` outside the window
  `{h + t : |t| <= B}` is at most `1 / B` for every `B >= 1`.
-/

namespace Ecdlp.ParityFourier

open Finset

/-- Normalised Fourier coefficient of `k ↦ (-1)^k` on `Z/n` at frequency `a`. -/
noncomputable def sigmaHat (n : ℕ) (a : ℤ) : ℂ :=
  (1 / (n : ℂ)) * ∑ k ∈ range n,
    ((-1 : ℂ) ^ k) * Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (k : ℂ) / (n : ℂ))

/-- F5a. Closed form of `|sigmaHat|` for odd `n`. -/
def SigmaHatClosedForm : Prop :=
  ∀ (n : ℕ), Odd n → ∀ a : ℤ,
    ‖sigmaHat n a‖ = 1 / ((n : ℝ) * |Real.cos (Real.pi * (a : ℝ) / (n : ℝ))|)

/-- F5b. Tail bound: the mass of `sigma` outside `{h + t : |t| ≤ B}` is at most `1/B`. -/
def SigmaTail : Prop :=
  ∀ (n : ℕ), Odd n → ∀ B : ℕ, 1 ≤ B →
    (∑ t ∈ Icc (B + 1) ((n - 1) / 2),
        (‖sigmaHat n (((n + 1) / 2 : ℕ) + (t : ℤ))‖ ^ 2 +
         ‖sigmaHat n (((n + 1) / 2 : ℕ) - (t : ℤ))‖ ^ 2)) ≤ 1 / (B : ℝ)

end Ecdlp.ParityFourier
