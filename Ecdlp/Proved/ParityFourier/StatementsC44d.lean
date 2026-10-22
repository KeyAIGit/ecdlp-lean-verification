import Ecdlp.Proved.ParityFourier.StatementsC44

/-!
# Frozen statements C44-N and C44-6d (the norm lemma; 0 is not in GammaJ)

This file fixes the statements before any proof is searched. Proof files must
not edit it.

* C44-N, the norm lemma of the C44 document: if `x + lam y = 0` in `ZMod n`
  for integers `(x, y) ≠ (0, 0)`, then `x^2 - x y + y^2 ≥ n`.
* C44-6d, Proposition 6(d) of the C44 document: if `3 (2B + 1)^2 < n`, the
  frequency `0` is not in `GammaJ lam B`. (Paper argument, not formalized
  here: the reduction of the C44 document, Theorem 10, uses this to know that
  the heavy coefficient it finds is invertible.)
-/

namespace Ecdlp.ParityFourier

/-- C44-N. The norm lemma for the Eisenstein lattice `{(x, y) : x + lam y = 0}`. -/
def NormLemma : Prop :=
  ∀ (n : ℕ) [Fact n.Prime], ∀ (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    ∀ x y : ℤ, (x, y) ≠ (0, 0) → (x : ZMod n) + lam * (y : ZMod n) = 0 →
      (n : ℤ) ≤ x ^ 2 - x * y + y ^ 2

/-- C44-6d. The frequency `0` is not in `GammaJ lam B` when `3 (2B + 1)^2 < n`. -/
def ZeroNotInGammaJ : Prop :=
  ∀ (n : ℕ) [Fact n.Prime], n ≠ 2 → ∀ (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    ∀ B : ℕ, 3 * (2 * B + 1) ^ 2 < n → (0 : ZMod n) ∉ GammaJ lam B

end Ecdlp.ParityFourier
