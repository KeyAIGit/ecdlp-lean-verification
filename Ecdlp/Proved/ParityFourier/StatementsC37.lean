import Ecdlp.Proved.ParityFourier.Statements

/-!
# Frozen statements C37 (relabelling with a defect; exact branch oracle gives the DL; square-root branch)

This file fixes the statements; proof files must not edit it.

Process note: no proof of these statements existed when this file was frozen.

Source: `reports/research_os/C37_BRANCH_REDUCTION_NOTE.md` ("the note"
below): Section 2, Proposition 1 (items 1–3) and Corollary 2 ("Exact case");
Section 2b (the branch `β` is public); Section 3, row
"half-index-miller-residual-branch". Notation as in `Statements.lean`
(`sgn`, F3 `Relabel`, `groupHalvingState`, F4b `GroupHalvingRecovers`).

Setting: `σ(Q) = (-1)^k` for `Q = [k]G`, `0 < k < n`, which is `sgn y` for
`Q = y.val • G`, `y ≠ 0`. A public label `c` takes the values `+1`, `-1` or
"undefined"; it is modelled as `c : X → Option ℤ`, with `none` for
undefined.

Definitions:
* `relabelPred c P` is the predictor `B'` of Proposition 1, item 1 (and `A'`
  of item 2): `c(x) P(x)` where `c(x)` is defined, and `+1` where it is
  undefined. It reads `c` only, never the exceptional set `Ω`, which depends
  on the hidden scalar.
* `bitOfSign s P` turns a sign oracle into a parity-bit oracle: `0` at the
  identity, `0` where `s P = 1`, and `1` otherwise.

Statements:
* C37-1 `RelabelDefect` (Proposition 1, items 1–3, on any finite domain `X`
  with the uniform distribution; the note's domain is `H \ {O}` with
  `|X| = n - 1`): let `c` be `±1` where defined, and let `Ω ⊆ X` be a set
  outside which `c` is defined and `σ = c b`. If `|Ω| ≤ δ |X|`, then
  (1) a predictor `P` of `b` with agreement at least `(1/2 + ε)|X|` gives the
  predictor `relabelPred c P` of `σ` with agreement at least
  `(1/2 + (ε - δ))|X|`; (2) the same from `σ` to `b`; (3) if `Ω = ∅` the
  agreement counts are equal in both directions. F3 (`Relabel`) is item (3)
  for a total `c`.
* C37-DL `RelabelDL` (Corollary 2, "Exact case", and Section 3, row
  "half-index-miller-residual-branch": an exact decoder of the hidden bit `b`
  together with the public `c` gives the discrete logarithm by
  Lauter-Stange's halving, their Prop. 2): let `G` have odd prime order `n`,
  `2h ≡ 1 (mod n)`, let `c` be defined with `σ = c b` at every `[y]G`,
  `y ≠ 0` (`δ = 0`), and let the oracle `D` equal `b` there. Then the
  halving chain driven by the parity bit of `relabelPred c D` recovers
  `x.val` from `Q = [x]G` in `L` steps whenever `n ≤ 2^L`. This composes
  C37-1 (3) with F4b.
* C37-sqrt `SqrtBranch` (Section 2b: "`β(Q) = M_h(G,Q,S) / r(R(G,Q,S))` lies
  in `{+1, -1}`", and "changing the root rule `r` multiplies `β` by a public
  `±1` function"): in any field, if `R ≠ 0`, `M^2 = R`, `s^2 = R` and
  `s'^2 = R`, then `M/s = ±1`, `s/s' = ±1` and `M/s' = (M/s)(s/s')`. It is
  applied pointwise with `M = M_h(G,Q,S)`, `R` the public right-hand side,
  and `s = r(R)`, `s' = r'(R)` for two root rules `r`, `r'`.

How the chain fits: C37-sqrt makes `β` a `±1`-valued function, so
`σ = β · (σ β)` is a factorization `σ = c b` with `c := β` total. C37-1 with
`Ω = ∅` says that the hidden C37 bit `b = σ β` and `σ` are predicted equally
well by relabelling, and C37-DL says that an exact decoder of `b` gives the
discrete logarithm.

Deviations from the note:
* Advantage is measured by agreement counts on a finite domain. The note's
  `Pr_Q[B(Q) = b(Q)] = 1/2 + ε` is `#agree ≥ (1/2 + ε)|X|`; `ε` and `δ` are
  arbitrary reals, and `|Ω| ≤ δ |X|` replaces `|Ω| ≤ δ (n - 1)`.
* C37-1 puts no condition on the values of `P`, `σ` or `b`; only `c` must be
  `±1` where defined.
* C37-DL does not assume `c = ±1`: with integer values, `sgn y = v · b`
  forces `v = ±1`. It assumes odd prime order only, not Lauter-Stange's
  `gcd(n, p - 1) = 1`; the note says the halving needs only odd order.
* C37-sqrt needs `R ≠ 0`; in Lean `0 / 0 = 0`, and the note implicitly
  assumes that the evaluator and the right-hand side are defined and nonzero.

Not claimed here:
* Publicity and cost: that `c` uses public data only (condition (C1)), runs
  in time `T_c`, that `B'` costs `T + T_c`, that `β` costs `O(log n)`, and
  the `O(log n (T + polylog n))` cost of the DL step. Lean definitions are
  not a cost model, and the membership of `c` in any complexity class is not
  stated.
* The upstream C37 identity
  `M_h(P,Q,S)^2 = h_{P,Q}(S)^n / (ℓ_{hP,hP}(S+Q) / ℓ_{hP,hP}(S))` and the
  Miller evaluator itself: C37-sqrt takes `M^2 = R` as a hypothesis, and
  Mathlib has no Miller functions or divisors.
* Corollary 2 for predictors with advantage (Håstad–Näslund, Akavia): any
  noisy halving for approximate parity predictors, any statement with
  `δ > 0` beyond C37-1, and the hard-core conclusion.
* Lemma 3 (the Lauter–Stange eq. (4) erratum), the EDS parity bridge
  `(-1)^k = χ(φ_LS([k]P)) χ(W_P(k))`, fixture eligibility, the univariate
  degree bound of Section 2b, the carry identities of Section 3, Remark (i)
  for non-uniform query distributions and Remark (ii) on averages.
* That the restricted model "decoder of `S_G(Q)` alone" is or is not weaker
  than the unrestricted one (open in the note).
-/

namespace Ecdlp.ParityFourier

open Finset

/-- C37 Proposition 1: the relabelled predictor `c · P` where the public label `c` is defined
(`some v`), and `+1` where it is undefined (`none`). -/
def relabelPred {X : Type*} (c : X → Option ℤ) (P : X → ℤ) (x : X) : ℤ :=
  match c x with
  | some v => v * P x
  | none => 1

/-- Parity bit read from a sign oracle `s`: `0` at the identity, `0` where `s P = 1`, else `1`. -/
def bitOfSign {A : Type*} [AddCommGroup A] [DecidableEq A] (s : A → ℤ) (P : A) : ℕ :=
  if P = 0 then 0 else if s P = 1 then 0 else 1

/-- C37-1 (Proposition 1, items 1–3). Public relabelling with an exceptional set `Ω` of
relative size at most `δ` loses at most `δ` of advantage in each direction, and nothing when
`Ω` is empty. -/
def RelabelDefect : Prop :=
  ∀ (X : Type) [Fintype X] (sigma b : X → ℤ) (c : X → Option ℤ) (Ω : Finset X),
    (∀ x v, c x = some v → v = 1 ∨ v = -1) →
    (∀ x, x ∉ Ω → ∃ v, c x = some v ∧ sigma x = v * b x) →
    ∀ (P : X → ℤ) (ε δ : ℝ), (Ω.card : ℝ) ≤ δ * Fintype.card X →
      ((1 / 2 + ε) * Fintype.card X ≤ ((univ.filter (fun x => P x = b x)).card : ℝ) →
        (1 / 2 + (ε - δ)) * Fintype.card X ≤
          ((univ.filter (fun x => relabelPred c P x = sigma x)).card : ℝ)) ∧
      ((1 / 2 + ε) * Fintype.card X ≤ ((univ.filter (fun x => P x = sigma x)).card : ℝ) →
        (1 / 2 + (ε - δ)) * Fintype.card X ≤
          ((univ.filter (fun x => relabelPred c P x = b x)).card : ℝ)) ∧
      (Ω = ∅ →
        (univ.filter (fun x => relabelPred c P x = sigma x)).card =
            (univ.filter (fun x => P x = b x)).card ∧
          (univ.filter (fun x => relabelPred c P x = b x)).card =
            (univ.filter (fun x => P x = sigma x)).card)

/-- C37-DL (Corollary 2, exact case). An exact oracle `D` for the hidden bit `b`, relabelled by
the public `c` with `σ = c b` on `⟨G⟩ \ {O}`, drives the halving chain to the discrete
logarithm. -/
def RelabelDL : Prop :=
  ∀ (A : Type) [AddCommGroup A] [DecidableEq A] (G : A) (n : ℕ) [Fact n.Prime], n ≠ 2 →
    addOrderOf G = n → ∀ (h : ℕ), (2 * h) % n = 1 →
    ∀ (c : A → Option ℤ) (b D : A → ℤ),
      (∀ y : ZMod n, y ≠ 0 → ∃ v, c (y.val • G) = some v ∧ sgn y = v * b (y.val • G)) →
      (∀ y : ZMod n, y ≠ 0 → D (y.val • G) = b (y.val • G)) →
      ∀ (x : ZMod n) (L : ℕ), n ≤ 2 ^ L →
        (∑ i ∈ range L,
            bitOfSign (relabelPred c D)
                (groupHalvingState (bitOfSign (relabelPred c D)) G h (x.val • G) i) * 2 ^ i) =
          x.val

/-- C37-sqrt (Section 2b). Two square roots of the same nonzero element differ by a sign, so the
Miller branch `M / r(R)` is `±1`, and changing the root rule multiplies it by `±1`. -/
def SqrtBranch : Prop :=
  ∀ (K : Type) [Field K] (M R s s' : K), R ≠ 0 → M ^ 2 = R → s ^ 2 = R → s' ^ 2 = R →
    (M / s = 1 ∨ M / s = -1) ∧ (s / s' = 1 ∨ s / s' = -1) ∧ M / s' = M / s * (s / s')

end Ecdlp.ParityFourier
