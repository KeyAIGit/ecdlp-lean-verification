import Ecdlp.Proved.ParityFourier.Statements
import Ecdlp.Proved.ParityFourier.StatementsWT

/-!
# Frozen statements CT (Fourier route for character families; L1 bounds of J and g)

This file fixes the statements; proof files must not edit it. Disclosure:
complete scratch proofs (compiled, with no proof holes) of CT and of L1J were
written on 2026-10-22, before this file was written (`charTransfer` in
`map/CharTransfer.lean`, an earlier `fourierRoute` of the same form in
`paperlean/KummerFR.lean`, and `l1J_le` in `map/L1J.lean`; scratch files of
session 3eaafce7, not in the repository). L1G, WT-J and WT-g had no scratch
proof when this file was written.

Process note: for CT and L1J, a scratch proof was found before this file was
written (session 3eaafce7, 2026-10-22); the statement was audited against the
paper claim, not against the proof.

Notation as in `StatementsC44.lean` and `StatementsWT.lean`: `ft` is the
normalised Fourier coefficient on `ZMod n`, `eChar` the additive character,
`sigmaC` and `JC` the parity and ordered-sector signs as complex functions,
`twistedSum` the twisted exponential sum; `g` is the GLV carry sign of
`Statements.lean`.

* CT (Fourier transfer; the finite step behind map rows C, H, E and R, map
  Section 0 "Fourier route"): if every twisted sum
  `∑_{k ≠ 0} F(k) e_n(α k)` has absolute value at most `C`, then
  `|∑_{k ≠ 0} F(k) T(k)| ≤ C ∑_α |T̂(α)|`. It holds for any complex `F` and
  `T`, not only for character families. The bound on twisted sums is the
  analytic input (a Weil-type bound) and stays a hypothesis.
* L1J, L1G (map Section 0 and N10; note Section 6.3 and C6(b)): for odd `n`
  (prime or not) and every `lam`, `∑_γ |Ĵ(γ)| ≤ (2 + log n)^2` and
  `∑_γ |ĝ(γ)| ≤ (2 + log n)^3`. These constants are weaker than the paper's:
  about 1.3 bits for `J` and about 14 bits for `g` at 256 bits (the map's
  `O(log n)` bound N10 for `g` is not formalized).
* WT-J, WT-g (note C6 with `T = J` or `T = g`, lowest bit only): the WT-lsb
  bound with the target `J` or `g` in place of the parity sign. For `J` the
  term `(n - 1)/p` bounds `|b̂(0)| |∑_{k≠0} J(k)|`; for `g` that term vanishes
  because `g` is odd. WT-g keeps the hypothesis `lam ^ 2 + lam + 1 = 0` to
  match the GLV setting and the frozen `GOdd`; it is not needed for odd prime
  `n`. With `n ≈ p ≈ 2^256` these give `ε ≤ 2^-105.54` (`J`) and
  `ε ≤ 2^-98.05` (`g`) in the note's normalisation, against the note's C6
  figures `2^-107.51` and `2^-112.74`. By the audit's computation the bounds
  are informative (below the trivial bound `n - 1`) only for `p ≈ n` above
  about `2^28.8` (`J`) and `2^41.6` (`g`); at toy sizes they are trivially
  true and are not evidence.

Not claimed here:
* No Weil-type input is stated or proved: the twisted-sum bounds (SS Lemmas
  4–5, KS Theorem 1, the note's T5, map N3) are hypotheses, and the
  reductions N6 and N7 of rows H, E and R and the dilation invariance
  `L1(T(c ·)) = L1(T)` used in rows E and R are not formalized. Only the
  finite transfer step is stated.
* No L1 bound for the parity sign `sgn` is stated in this file.
* WT-J and WT-g cover the lowest bit only; the note's half-interval bit and
  general targets `T : ZMod n → [-1, 1]` are not stated.
-/

namespace Ecdlp.ParityFourier

open Finset

/-- CT. A uniform bound on twisted sums of `F` bounds its correlation with any `T`. -/
def CharTransfer : Prop :=
  ∀ (n : ℕ) [NeZero n] (F T : ZMod n → ℂ) (C : ℝ),
    (∀ α : ZMod n, ‖∑ k ∈ univ.erase (0 : ZMod n), F k * eChar (α * k)‖ ≤ C) →
      ‖∑ k ∈ univ.erase (0 : ZMod n), F k * T k‖ ≤ C * ∑ α : ZMod n, ‖ft T α‖

/-- L1J. The Fourier L1 norm of `J` is at most `(2 + log n)^2`. -/
def L1JBound : Prop :=
  ∀ (n : ℕ) [NeZero n], Odd n → ∀ lam : ZMod n,
    ∑ γ : ZMod n, ‖ft (JC lam) γ‖ ≤ (2 + Real.log n) ^ 2

/-- L1G. The Fourier L1 norm of `g` is at most `(2 + log n)^3`. -/
def L1GBound : Prop :=
  ∀ (n : ℕ) [NeZero n], Odd n → ∀ lam : ZMod n,
    ∑ γ : ZMod n, ‖ft (fun k => (g lam k : ℂ)) γ‖ ≤ (2 + Real.log n) ^ 3

/-- WT-J. Lowest bit of `V` against `J`, with `C = 2 sqrt p`. -/
def WeilTransferLsbJ : Prop :=
  ∀ (n p : ℕ) [NeZero n] [NeZero p] [Fact n.Prime] [Fact p.Prime], n ≠ 2 → p ≠ 2 →
    ∀ (lam : ZMod n) (V : ZMod n → ZMod p),
      (∀ a : ZMod p, a ≠ 0 → ∀ α : ZMod n, ‖twistedSum V a α‖ ≤ 2 * Real.sqrt p) →
        ‖∑ k ∈ univ.erase (0 : ZMod n), sigmaC (V k) * JC lam k‖ ≤
          ((n : ℝ) - 1) / p + 2 * Real.sqrt p * (2 + Real.log p) * (2 + Real.log n) ^ 2

/-- WT-g. Lowest bit of `V` against the GLV carry `g`, with `C = 2 sqrt p`. -/
def WeilTransferLsbG : Prop :=
  ∀ (n p : ℕ) [NeZero n] [NeZero p] [Fact n.Prime] [Fact p.Prime], n ≠ 2 → p ≠ 2 →
    ∀ (lam : ZMod n), lam ^ 2 + lam + 1 = 0 → ∀ V : ZMod n → ZMod p,
      (∀ a : ZMod p, a ≠ 0 → ∀ α : ZMod n, ‖twistedSum V a α‖ ≤ 2 * Real.sqrt p) →
        ‖∑ k ∈ univ.erase (0 : ZMod n), sigmaC (V k) * (g lam k : ℂ)‖ ≤
          2 * Real.sqrt p * (2 + Real.log p) * (2 + Real.log n) ^ 3

end Ecdlp.ParityFourier
