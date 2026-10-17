import Mathlib

/-!
# Frozen statement C44-6' (concentration of the ordered-sector sign J)

This file fixes the statement before any proof is searched. Proof files must
not edit it.

Notation, all on `ZMod n` with `n` prime and `n ≠ 2`:
* `ft f β = (1/n) * sum_k f k * exp(-2 pi i β.val k.val / n)` is the
  normalised Fourier coefficient of `f : ZMod n → ℂ`;
* `sigmaC k = (-1)^k.val` and `JC lam k = sigmaC (lam k) * sigmaC (lam^2 k)`
  are the parity sign and the C44 ordered-sector sign;
* `h = (n + 1) / 2` is the centre of the spectrum of sigma;
* `GammaJ lam B = { lam (h + t1) + lam^2 (h + t2) : |t1|, |t2| ≤ B }` is the
  CM-lattice set of the C44 document (Proposition 6(a));
* `L1low B = sum_{|t| ≤ B} |ft sigmaC (h + t)|` is the L1 norm of the
  low-pass part of sigma.

Statement C44-6'. The Fourier mass of `J` outside `GammaJ lam B` is at most
`(1 + L1low B)^2 / B`. This is Proposition 6(b) of the C44 document with the
uniform Gibbs bound (Lemma 3) replaced by the L1 bound (Lemma 4). Since
`L1low B` grows like `(2/pi) log B`, the bound is `O(log^2 B / B)`, which still
makes J well concentrated in Akavia's sense, up to the logarithm.
-/

namespace Ecdlp.ParityFourier

open Finset

/-- Normalised Fourier coefficient on `ZMod n`. -/
noncomputable def ft {n : ℕ} [NeZero n] (f : ZMod n → ℂ) (β : ZMod n) : ℂ :=
  (1 / (n : ℂ)) * ∑ k : ZMod n,
    f k * Complex.exp (-2 * Real.pi * Complex.I * ((β.val * k.val : ℕ) : ℂ) / (n : ℂ))

/-- Parity sign as a complex function. -/
noncomputable def sigmaC {n : ℕ} (k : ZMod n) : ℂ := (-1 : ℂ) ^ k.val

/-- The ordered-sector sign as a complex function. -/
noncomputable def JC {n : ℕ} (lam k : ZMod n) : ℂ := sigmaC (lam * k) * sigmaC (lam ^ 2 * k)

/-- The centre `h = (n + 1) / 2` as an element of `ZMod n`. -/
def hC (n : ℕ) : ZMod n := (((n + 1) / 2 : ℕ) : ZMod n)

/-- The window offsets `t` with `|t| ≤ B`, as integers. -/
noncomputable def window (B : ℕ) : Finset ℤ := Icc (-(B : ℤ)) (B : ℤ)

/-- `GammaJ lam B = { lam (h + t1) + lam^2 (h + t2) : t1, t2 ∈ window B }`. -/
noncomputable def GammaJ {n : ℕ} (lam : ZMod n) (B : ℕ) : Finset (ZMod n) :=
  ((window B) ×ˢ (window B)).image
    (fun p => lam * (hC n + (p.1 : ZMod n)) + lam ^ 2 * (hC n + (p.2 : ZMod n)))

/-- L1 norm of the low-pass part of sigma. -/
noncomputable def L1low (n : ℕ) [NeZero n] (B : ℕ) : ℝ :=
  ∑ t ∈ window B, ‖ft (sigmaC (n := n)) (hC n + (t : ZMod n))‖

/-- C44-6'. Concentration of `J` with an explicit bound. -/
def JConcentration : Prop :=
  ∀ (n : ℕ) [NeZero n] [Fact n.Prime], n ≠ 2 → ∀ (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    ∀ B : ℕ, 1 ≤ B →
      (∑ γ ∈ (univ \ GammaJ lam B), ‖ft (JC lam) γ‖ ^ 2) ≤ (1 + L1low n B) ^ 2 / (B : ℝ)

end Ecdlp.ParityFourier
