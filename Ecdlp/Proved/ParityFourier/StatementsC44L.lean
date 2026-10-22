import Ecdlp.Proved.ParityFourier.StatementsC44

/-!
# Frozen statements C44-L4 and C44-6x (explicit concentration of J)

This file fixes the statements before any proof is searched. Proof files must
not edit it.

* C44-L4 (Lemma 4 of the C44 document, in a simple form): for odd `n` and
  `2B + 1 ≤ n`, `L1low n B ≤ 2 + log (2B + 1)`. The proof idea is
  `|sigma_hat(h + t)| ≤ 1 / |2t + 1|` (closed form plus `sin x ≥ 2x/π`) and a
  harmonic-sum estimate.
* C44-6x: combining C44-6' with C44-L4, the Fourier mass of `J` outside
  `GammaJ lam B` is at most `(3 + log (2B + 1))^2 / B` when `2B + 1 ≤ n`.
-/

namespace Ecdlp.ParityFourier

open Finset

/-- C44-L4. Logarithmic growth of the low-pass L1 norm of sigma. -/
def L1lowBound : Prop :=
  ∀ (n : ℕ) [NeZero n], Odd n → ∀ B : ℕ, 2 * B + 1 ≤ n →
    L1low n B ≤ 2 + Real.log (2 * (B : ℝ) + 1)

/-- C44-6x. Explicit concentration of `J`. -/
def JConcentrationExplicit : Prop :=
  ∀ (n : ℕ) [NeZero n] [Fact n.Prime], n ≠ 2 → ∀ (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    ∀ B : ℕ, 1 ≤ B → 2 * B + 1 ≤ n →
      (∑ γ ∈ (univ \ GammaJ lam B), ‖ft (JC lam) γ‖ ^ 2) ≤
        (3 + Real.log (2 * (B : ℝ) + 1)) ^ 2 / (B : ℝ)

end Ecdlp.ParityFourier
