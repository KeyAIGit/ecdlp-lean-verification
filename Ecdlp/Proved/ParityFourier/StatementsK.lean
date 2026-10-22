import Ecdlp.Proved.ParityFourier.Statements

/-!
# Frozen statements K (row K of the parity coverage map, both directions)

This file fixes the statements; proof files must not edit it. Disclosure
(process exception): scratch Lean proofs of closely related statements were
compiled on 2026-10-22 (session 3eaafce7), before this file was written: the
abstract form over `ZMod n` in both directions (`kummerZero`,
`oddFeatureEvenTarget`), the `sgn` instance (`kummerZeroSigma`), the `J`
instance (`oddFeatureVsJ`), and the x-only curve instance against `sgn`
(`kummerZeroCurve`, with an `xFeature` of the same shape). K0 has the form of
`kummerZero`. These are scratch files (`map/KummerZero.lean` and the earlier
`paperlean/KummerFR.lean`), not in the repository. No scratch proof of the
`g` or Legendre conjuncts existed. Fidelity was judged by an independent
statement audit against map row K / N1, not against those proofs; the audit
records the same exception.

Process note: for K0 and for the `sgn` part of K-even, the `J` part of K-odd
and the `sgn` part of K-x (in the same or a closely related form), a scratch
proof was found before this file was written (session 3eaafce7, 2026-10-22);
the statement was audited against the paper claim, not against the proof.

Setting: `G` is an element of odd prime order `n` of an additive group `A`
(for a curve, `A = W.toAffine.Point`), and `Q = [k]G` with `[k] = k.val`.
A feature `Φ : A → ℂ` is *even* if `Φ(-P) = Φ(P)` for every `P` (for example
any function of the x-coordinate of a Weierstrass point). It is *odd* if
`Φ(-P) = -Φ(P)` for every `P` with `P ≠ -P` (for example `(-1)^lsb(y)` on a
short Weierstrass curve over `F_p`, `p` odd: `P ≠ -P` forces `y ≠ 0`; the
values at `O` and at 2-torsion points are free). Targets: the parity sign `sgn`,
the ordered-sector sign `J`, the GLV carry sign `g` (all from `Statements.lean`)
and the Legendre symbol `(k/n)`.

* K0 (map note N1, abstract form): over `ZMod n` with `n` odd, if `F` is even
  and `T` is odd on nonzero residues, then `∑_{k ≠ 0} F(k) T(k) = 0`.
* K-even (map row K / N1, for any even feature): an even feature has exactly
  zero correlation over `k ≠ 0` with `sgn`, with `g`, and, when
  `n ≡ 3 (mod 4)`, with `(k/n)`.
* K-odd (the odd half, N1′ of the proposed map revision; not in the map
  committed at 78a1764, novelty not checked against the literature): an odd
  feature has exactly zero correlation over `k ≠ 0` with `J` and, when
  `n ≡ 1 (mod 4)`, with `(k/n)`.
* K-x (map row K, "any Phi(x(Q))"): the x-only instance on any Weierstrass
  curve over any field: a function of `x([k]G)` (with an arbitrary value at
  `O`) has exactly zero correlation with `sgn`, with `g`, and, when
  `n ≡ 3 (mod 4)`, with `(k/n)`.

Not claimed here:
* These are exact symmetry identities (the terms at `k` and `-k` cancel), not
  hardness results; they say nothing about features that are neither even nor
  odd, and nothing about decoding `k`.
* K-even, K-odd and K-x assume `n` prime; odd composite `n` is covered only
  by the abstract K0. The `g` and `J` conjuncts assume `lam ^ 2 + lam + 1 = 0`
  (the paper's GLV setting), although the parity facts behind them hold for
  every `lam` when `n` is an odd prime.
* Row K's wording "every target that is odd under negation" is not stated at
  curve level: K-x lists only `sgn`, `g` and `(k/n)`. The general curve form
  follows from K0 plus the evenness of `k ↦ Φ(x([k]G))`, which is not itself
  a frozen statement.
* Curve-level features of `psi_m(Q)` (odd `m`) are not covered: Mathlib has
  no point evaluation of `psi_m` that would make them x-only features here.
* `A` and `K` range over `Type` (universe 0), which covers every object in the
  paper (`ZMod p`, Galois fields).
-/

namespace Ecdlp.ParityFourier

open Finset

/-- A function of the x-coordinate of a point of a Weierstrass curve, with value `c0` at `O`. -/
def xFeature {K : Type*} [Field K] (W : WeierstrassCurve K) (Φ : K → ℂ) (c0 : ℂ) :
    W.toAffine.Point → ℂ
  | .zero => c0
  | .some x _ _ => Φ x

/-- K0. Even against odd: orthogonal on the nonzero residues of `ZMod n`, `n` odd. -/
def ParityMismatchZero : Prop :=
  ∀ (n : ℕ) [NeZero n], Odd n → ∀ (F T : ZMod n → ℂ),
    (∀ k, F (-k) = F k) → (∀ k, k ≠ 0 → T (-k) = -T k) →
      ∑ k ∈ univ.erase (0 : ZMod n), F k * T k = 0

/-- K-even. An even feature of `[k]G` is uncorrelated with `sgn`, with `g`, and,
when `n ≡ 3 (mod 4)`, with `(k/n)`. -/
def EvenFeatureZero : Prop :=
  ∀ (A : Type) [AddCommGroup A] (G : A) (n : ℕ) [Fact n.Prime], n ≠ 2 → addOrderOf G = n →
    ∀ Φ : A → ℂ, (∀ P, Φ (-P) = Φ P) →
      (∑ k ∈ univ.erase (0 : ZMod n), Φ (k.val • G) * (sgn k : ℂ)) = 0 ∧
      (∀ lam : ZMod n, lam ^ 2 + lam + 1 = 0 →
        ∑ k ∈ univ.erase (0 : ZMod n), Φ (k.val • G) * (g lam k : ℂ) = 0) ∧
      (n % 4 = 3 →
        ∑ k ∈ univ.erase (0 : ZMod n), Φ (k.val • G) * (legendreSym n (k.val : ℤ) : ℂ) = 0)

/-- K-odd. An odd feature of `[k]G` is uncorrelated with `J`, and with `(k/n)` if `n ≡ 1 mod 4`. -/
def OddFeatureZero : Prop :=
  ∀ (A : Type) [AddCommGroup A] (G : A) (n : ℕ) [Fact n.Prime], n ≠ 2 → addOrderOf G = n →
    ∀ Ψ : A → ℂ, (∀ P, P ≠ -P → Ψ (-P) = -Ψ P) →
      (∀ lam : ZMod n, lam ^ 2 + lam + 1 = 0 →
        ∑ k ∈ univ.erase (0 : ZMod n), Ψ (k.val • G) * (J lam k : ℂ) = 0) ∧
      (n % 4 = 1 →
        ∑ k ∈ univ.erase (0 : ZMod n), Ψ (k.val • G) * (legendreSym n (k.val : ℤ) : ℂ) = 0)

/-- K-x. x-only features on a Weierstrass curve over any field. -/
def XOnlyZero : Prop :=
  ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (G : W.toAffine.Point)
    (n : ℕ) [Fact n.Prime], n ≠ 2 → addOrderOf G = n → ∀ (Φ : K → ℂ) (c0 : ℂ),
      (∑ k ∈ univ.erase (0 : ZMod n), xFeature W Φ c0 (k.val • G) * (sgn k : ℂ)) = 0 ∧
      (∀ lam : ZMod n, lam ^ 2 + lam + 1 = 0 →
        ∑ k ∈ univ.erase (0 : ZMod n), xFeature W Φ c0 (k.val • G) * (g lam k : ℂ) = 0) ∧
      (n % 4 = 3 →
        ∑ k ∈ univ.erase (0 : ZMod n),
          xFeature W Φ c0 (k.val • G) * (legendreSym n (k.val : ℤ) : ℂ) = 0)

end Ecdlp.ParityFourier
