import Ecdlp.Proved.ParityFourier.StatementsC44

/-!
# Frozen statement C44-B (balance of J)

This file fixes the statement before any proof is searched. Proof files must
not edit it.

C44-B: if `1 ≤ B` and `3 (2B + 1)^2 < n`, then
`|J_hat(0)|^2 ≤ (3 + log (2B + 1))^2 / B`. Taking the largest such `B`
(about `sqrt(n/12)`) gives `|J_hat(0)| = O(n^(-1/4) log n)`, a rigorous form
of the balance of `J` (Section 3.6 of the C44 document gives `O(n^(-1/4))`
on paper).
-/

namespace Ecdlp.ParityFourier

/-- C44-B. Balance of `J` from concentration and `0 ∉ GammaJ`. -/
def JBalanceBound : Prop :=
  ∀ (n : ℕ) [NeZero n] [Fact n.Prime], n ≠ 2 → ∀ (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    ∀ B : ℕ, 1 ≤ B → 3 * (2 * B + 1) ^ 2 < n →
      ‖ft (JC lam) 0‖ ^ 2 ≤ (3 + Real.log (2 * (B : ℝ) + 1)) ^ 2 / (B : ℝ)

end Ecdlp.ParityFourier
