import Ecdlp.Proved.ParityFourier.StatementsC44

/-!
# Frozen statements WT and WT-lsb (the Weil-transfer layer)

This file fixes the statements before any proof is searched. Proof files must
not edit it.

Setting: `V : ZMod n → ZMod p` is a public function of the index `k` (for a
curve, `k ↦ V([k]G)`), `b : ZMod p → ℂ` reads a bit of `V`, and
`T : ZMod n → ℂ` is a target such as the parity sign.

* `eChar x = exp(2 π i x.val / m)` is the additive character of `ZMod m`.
* `twistedSum V a α = ∑_{k ≠ 0} eChar (a V(k)) eChar (α k)`.
* WT (Weil transfer): if every twisted sum with `a ≠ 0` is at most `C` in
  absolute value, then
  `|∑_{k ≠ 0} b(V k) T(k)| ≤ |b̂(0)| |∑_{k ≠ 0} T(k)| + C (∑_{a ≠ 0} |b̂(a)|) (∑_α |T̂(α)|)`,
  with `ft` the normalised Fourier transform of `StatementsC44.lean`.
* WT-lsb: for odd primes `n` and `p`, with `b = T = (-1)^val` (the lowest bit
  of `V` against the parity of `k`) and an assumed twisted-sum bound
  `C = 2 sqrt p`, the correlation sum is at most
  `2 sqrt p (2 + log p) (2 + log n)`.

The hypothesis on twisted sums is the analytic input (for the Weierstrass zeta
of a prime-order curve it is the lab's unproved hypothesis D2.2.1). The
constant `2 sqrt p` is not known to hold for elliptic-curve coordinate maps
(the standard bound for a function `f` is `2 deg(f) sqrt p`); WT covers a
general `C`. These statements only check the finite Fourier transfer.
-/

namespace Ecdlp.ParityFourier

open Finset

/-- The additive character `e_m(x) = exp(2 π i x.val / m)` of `ZMod m`. -/
noncomputable def eChar {m : ℕ} (x : ZMod m) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℕ) : ℂ) / (m : ℂ))

/-- Twisted exponential sum of `V` at `(a, α)`, over `k ≠ 0`. -/
noncomputable def twistedSum {n p : ℕ} [NeZero n] (V : ZMod n → ZMod p) (a : ZMod p) (α : ZMod n) : ℂ :=
  ∑ k ∈ (univ.erase (0 : ZMod n)), eChar (a * V k) * eChar (α * k)

/-- WT. A uniform bound on twisted sums bounds every correlation. -/
def WeilTransfer : Prop :=
  ∀ (n p : ℕ) [NeZero n] [NeZero p] (V : ZMod n → ZMod p) (b : ZMod p → ℂ)
    (T : ZMod n → ℂ) (C : ℝ),
    (∀ a : ZMod p, a ≠ 0 → ∀ α : ZMod n, ‖twistedSum V a α‖ ≤ C) →
      ‖∑ k ∈ (univ.erase (0 : ZMod n)), b (V k) * T k‖ ≤
        ‖ft b 0‖ * ‖∑ k ∈ (univ.erase (0 : ZMod n)), T k‖ +
          C * (∑ a ∈ (univ.erase (0 : ZMod p)), ‖ft b a‖) * (∑ α : ZMod n, ‖ft T α‖)

/-- WT-lsb. Lowest bit of `V` against the parity of the index, with an assumed
twisted-sum bound `C = 2 sqrt p`. -/
def WeilTransferLsb : Prop :=
  ∀ (n p : ℕ) [NeZero n] [NeZero p] [Fact n.Prime] [Fact p.Prime], n ≠ 2 → p ≠ 2 →
    ∀ V : ZMod n → ZMod p,
      (∀ a : ZMod p, a ≠ 0 → ∀ α : ZMod n, ‖twistedSum V a α‖ ≤ 2 * Real.sqrt p) →
        ‖∑ k ∈ (univ.erase (0 : ZMod n)), sigmaC (V k) * sigmaC k‖ ≤
          2 * Real.sqrt p * (2 + Real.log p) * (2 + Real.log n)

end Ecdlp.ParityFourier
