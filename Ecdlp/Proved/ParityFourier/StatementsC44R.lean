import Ecdlp.Proved.ParityFourier.Statements
import Ecdlp.Proved.ParityFourier.StatementsC44

/-!
# Frozen statements C44-R (C44 Theorem 10 for J, with the SFT output as a hypothesis)

This file fixes the statements; proof files must not edit it.

Process note: no proof of these statements existed when this file was frozen.
Kernel-checked results already in the repository make some of them short:
`parseval` (`ProofsC44.lean`) for C44-HS, C44-N (`normLemma`) for the
equality case of C44-6a#, and C44-9J, C44-6d and C44-L4 for C44-10 and
C44-10x.

Source: `reports/research_os/C44_J_G_HARDCORE_PROOF.md` ("C44" below),
Section 4: Lemma 8, Theorem 10 for `P = J` (hypotheses, steps 1–4 of `R`,
proof steps 1–6), and Proposition 6(a); Akavia's Theorem 3.16 as quoted in
C44 Section 2.1. Notation as in `Statements.lean` (`sgn`, `J`) and
`StatementsC44.lean` (`ft`, `GammaJ`, `L1low`). The frozen inputs a proof is
expected to use are C44-9J (`JHeavy`, `StatementsC44H.lean`), C44-6d
(`ZeroNotInGammaJ`, `StatementsC44d.lean`) and C44-L4 (`L1lowBound`,
`StatementsC44L.lean`).

Setting (C44 Section 4). `G` is an element of prime order `n` of an additive
commutative group `A` with decidable equality (the paper's equality tests);
`lam ^ 2 + lam + 1 = 0` in `ZMod n`; `[u]G = u.val • G`. A predictor is any
function `Pred : A → ℤ` whose values at the nonzero multiples of `G` are
`±1` (a deterministic algorithm; only those values are ever queried, and
`Pred(O)` is never used). Its advantage
is any real `ε` with `#{u ≠ 0 : Pred([u]G) = J(u)} ≥ (1/2 + ε)(n - 1)`, that
is `Pr_{u ∈ (Z/n)^*}[Pred([u]G) = J(u)] ≥ 1/2 + ε`; any lower bound on the
true advantage may be used. `η = ε - 1/n`.

Definitions:
* `accessFn Pred Q` is the access function `w` of Lemma 8:
  `w(x) = Pred([x]Q)` for `x ≠ 0` and `w(0) = 1`. Step 1 of `R` runs the SFT
  algorithm on this `w`.
* `jReductionOutput lam B G Q Lst` is the set of outputs of `R` (Theorem 10,
  steps 1, 3 and 4) once the SFT run of step 1 has returned the list `Lst`.
  If `Q = O` it is `{0}`. Otherwise every `β ∈ Lst` and `α ∈ GammaJ lam B`
  (the table `{[α]Q : α ∈ GammaJ lam B}` of step 3) with a table hit
  `[β]G = [α]Q` propose `k' = β α⁻¹`, and a proposal is kept only if it
  passes the check `[k']G = Q`. `R` outputs the first kept proposal, so
  "`R` outputs `k`" means that this set is `{k}`, and "`R` never outputs a
  wrong value" means that it is contained in `{k}`. (In Lean `0⁻¹ = 0`: a hit
  with `α = 0` proposes `0`, which the check rejects unless `Q = O`.)

Statements:
* C44-8 `AccessCorrelation` (Lemma 8, second bullet): for every `k ≠ 0`
  (not only on average) and `Q = [k]G`,
  `(1/n) ∑_x w(x) J(x k) ≥ 2ε - 2/n = 2η`. The first bullet of Lemma 8
  (`w` is `±1`-valued when `k ≠ 0`) follows from the hypothesis on `Pred`;
  the third (dilation) is used inside C44-9J and is not restated.
* C44-6a# `GammaJCard` (Proposition 6(a), last bullet): the table has at
  most `(2B + 1)^2` entries, with equality when `12 B^2 < n`.
* C44-HS `HeavySetSmall` (supporting fact, not a claim of C44; the Parseval
  bound behind `|L| ≤ O(1/τ)` in Akavia's Theorem 3.16(2)): for `|w| ≤ 1`
  and `τ > 0`, at most `1/τ` frequencies are `τ`-heavy. So lists that satisfy
  the hypothesis of C44-10 with at most `1/τ` entries exist, not only the
  brute-force list `ZMod n`.
* C44-10s `JReductionSound` (Theorem 10, "never outputs a wrong value"; proof
  step 6): for every list, every output of `R` on `Q = [k]G` is `k`.
* C44-10 `JRecoverFromHeavyList` (Theorem 10 for `J`, proof steps 1–5, with
  the SFT output as a hypothesis). Parameter conditions: `B ≥ 1`,
  `3 (2B + 1)^2 < n`, `η > 0`, `(1 + L1low B)^2 / B ≤ η^2`, and a threshold
  `τ ≤ (η / L1low(B)^2)^2`. If the list `Lst` contains every `β` with
  `|ŵ(β)|^2 ≥ τ` (Theorem 3.16, property 1: `L ⊇ Heavy_τ(w)`), then the set
  of outputs of `R` on `Q = [k]G` is exactly `{k}`. It is stated for every
  `k`, including `k = 0` (`Q = O`, step 1).
* C44-10x `JRecoverExplicit`: C44-10 with parameters computable from `ε`,
  `n` and `B`: `(3 + log(2B + 1))^2 / B ≤ η^2` and the threshold
  `τ = (η / (2 + log(2B + 1))^2)^2`. This is the paper's
  `τ = (η / Lbar(B)^2)^2` with `Lbar(B) := 2 + log(2B + 1)`, an upper bound
  on `L1low B` by C44-L4.

Deviations from the paper:
* The paper's condition `T_J(B) ≤ η^2` is replaced by the kernel-checked
  expressions of C44-6' (in C44-10) and C44-6x (in C44-10x), and the paper's
  `Lbar(B) = (2/π)(ln B + 1.96) + o(1)` by `L1low B` or `2 + log(2B + 1)`.
  For a given `η`, `B` and the table are therefore larger than in the paper
  (estimate at `ε = 2^-8`: `B ≈ 2.85·10^7` for C44-10x and `B ≈ 1.0·10^7`
  for C44-10, using `L1low B ≈ (2/π)(ln B + 1.96)`, instead of `72269`).
* The paper assumes `ε > 2/n`; here only `η = ε - 1/n > 0` is assumed (the
  extra `1/n` is needed only for `g`). `B` need not be the least admissible
  integer. `n ≡ 1 (mod 3)` is not assumed separately: a root `lam` exists only
  if `n = 3` or `n ≡ 1 (mod 3)`, and `3 (2B + 1)^2 < n` with `B ≥ 1` forces
  `n > 27`.
* `R`'s output is modelled as the finite set of verified proposals, not as
  the first one in an enumeration order of `Lst`.
* `B ≥ 1` is load-bearing: in Lean `x / 0 = 0`, so with `B = 0` the
  conditions on `B` would hold trivially.

When the statements say something: the hypotheses force `η < 1/2`, so
`(1 + L1low B)^2 / B ≤ 1/4`; with `L1low B ≈ (2/π)(ln B + 1.96)` this needs
`B` of order `10^2` and then `n > 3 (2B + 1)^2` of order `10^5` (C44-10), and
with `2 + log(2B + 1)` it needs `B ≥ 370` and `n > 1.6·10^6` (C44-10x,
`ε = 1/2`). In that regime `0 ∉ GammaJ lam B` and the table is a proper
subset of `ZMod n`.

Not claimed here:
* Akavia's SFT algorithm (Theorem 3.16) is not formalized: not its
  existence, its success probability `≥ 1 - δ'` (`2/3` in Theorem 10), its
  list size `O(1/τ)`, nor its running time. `Lst` is an arbitrary finite set
  satisfying the containment, so C44-10 and C44-10x are statements about the
  success event of the SFT run. "`R` outputs `log_G Q` with probability at
  least `2/3`" follows only together with Theorem 3.16.
* No cost statement: the numbers of predictor calls, scalar multiplications
  and group operations, and the figures of Sections 4.1 and 5. Lean
  definitions are not a cost model. That `R` uses only group operations,
  equality tests and arithmetic mod `n` (Remark 10.1) is visible in the
  definitions but is not a theorem.
* Theorem 10 for `g`, Proposition 7 and Lemma 9(g); Remark 10.2 (x-only
  predictors); Remark 10.3 (randomized predictors); the search over
  `ε = 2^-1, 2^-2, …` when no bound on `ε` is given; Corollary 11 and
  Remarks 11.1–11.2.
* The paper's sharp constants (`T_J`, `Mbar`, `Lbar`), the asymptotics
  `B = O(1/ε^2)` and `τ ≥ ε^2 / polylog(1/ε)`, and any parameter-existence
  claim ("an admissible `B` exists for every `ε` once `n` is large").
* The reading of `J` as upstream's ordered-sector sign on secp256k1 or any
  concrete curve; `A` is an abstract group.
-/

namespace Ecdlp.ParityFourier

open Finset

/-- C44 Lemma 8: the access function `w(x) = Pred([x]Q)` for `x ≠ 0`, `w(0) = 1`. -/
def accessFn {A : Type*} [AddCommGroup A] {n : ℕ} (Pred : A → ℤ) (Q : A) (x : ZMod n) : ℤ :=
  if x = 0 then 1 else Pred (x.val • Q)

/-- C44 Theorem 10, steps 1, 3, 4: the set of outputs of `R` on `Q`, given the SFT list `Lst`.
Each table hit `[β]G = [α]Q` with `β ∈ Lst`, `α ∈ GammaJ lam B` proposes `β α⁻¹`; a proposal is
kept only if it passes the check `[k']G = Q`. If `Q = O` the output is `0`. -/
noncomputable def jReductionOutput {A : Type*} [AddCommGroup A] [DecidableEq A] {n : ℕ}
    (lam : ZMod n) (B : ℕ) (G Q : A) (Lst : Finset (ZMod n)) : Finset (ZMod n) :=
  if Q = 0 then {0} else
    (((Lst ×ˢ GammaJ lam B).filter (fun p => p.1.val • G = p.2.val • Q)).image
        (fun p => p.1 * p.2⁻¹)).filter (fun k' => k'.val • G = Q)

/-- C44-8 (Lemma 8). A predictor with advantage `ε` gives, for every `k ≠ 0`, an access
function with correlation at least `2 (ε - 1/n)` with `x ↦ J(x k)`. -/
def AccessCorrelation : Prop :=
  ∀ (A : Type) [AddCommGroup A] (G : A) (n : ℕ) [NeZero n] [Fact n.Prime],
    addOrderOf G = n → ∀ (lam : ZMod n) (Pred : A → ℤ),
    (∀ u : ZMod n, u ≠ 0 → Pred (u.val • G) = 1 ∨ Pred (u.val • G) = -1) →
    ∀ ε : ℝ, (1 / 2 + ε) * ((n : ℝ) - 1) ≤
        (((univ.erase (0 : ZMod n)).filter (fun u => Pred (u.val • G) = J lam u)).card : ℝ) →
    ∀ k : ZMod n, k ≠ 0 →
      2 * (ε - 1 / (n : ℝ)) ≤
        (1 / (n : ℝ)) * ∑ x : ZMod n, (accessFn Pred (k.val • G) x : ℝ) * (J lam (x * k) : ℝ)

/-- C44-6a# (Proposition 6(a), count). `|GammaJ lam B| ≤ (2B + 1)^2`, with equality if
`12 B^2 < n`. -/
def GammaJCard : Prop :=
  ∀ (n : ℕ) [Fact n.Prime] (lam : ZMod n), lam ^ 2 + lam + 1 = 0 → ∀ B : ℕ,
    (GammaJ lam B).card ≤ (2 * B + 1) ^ 2 ∧
      (12 * B ^ 2 < n → (GammaJ lam B).card = (2 * B + 1) ^ 2)

/-- C44-HS (supporting fact; Parseval). A function bounded by `1` has at most `1/τ`
frequencies `β` with `τ ≤ |ŵ(β)|^2`. -/
def HeavySetSmall : Prop :=
  ∀ (n : ℕ) [NeZero n] (w : ZMod n → ℂ), (∀ x, ‖w x‖ ≤ 1) → ∀ τ : ℝ, 0 < τ →
    τ * ((univ.filter (fun β : ZMod n => τ ≤ ‖ft w β‖ ^ 2)).card : ℝ) ≤ 1

/-- C44-10s (Theorem 10, "never outputs a wrong value"). Whatever the list, every output of
`R` on `Q = [k]G` is `k`. -/
def JReductionSound : Prop :=
  ∀ (A : Type) [AddCommGroup A] [DecidableEq A] (G : A) (n : ℕ) [NeZero n],
    addOrderOf G = n → ∀ (lam : ZMod n) (B : ℕ) (Lst : Finset (ZMod n)) (k : ZMod n),
      jReductionOutput lam B G (k.val • G) Lst ⊆ {k}

/-- C44-10 (Theorem 10 for `J`, with the SFT output as a hypothesis). If the list contains
every `τ`-heavy frequency of the access function, `R` outputs exactly the discrete logarithm. -/
def JRecoverFromHeavyList : Prop :=
  ∀ (A : Type) [AddCommGroup A] [DecidableEq A] (G : A) (n : ℕ) [NeZero n] [Fact n.Prime],
    n ≠ 2 → addOrderOf G = n → ∀ (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    ∀ (Pred : A → ℤ), (∀ u : ZMod n, u ≠ 0 → Pred (u.val • G) = 1 ∨ Pred (u.val • G) = -1) →
    ∀ ε : ℝ, (1 / 2 + ε) * ((n : ℝ) - 1) ≤
        (((univ.erase (0 : ZMod n)).filter (fun u => Pred (u.val • G) = J lam u)).card : ℝ) →
    0 < ε - 1 / (n : ℝ) →
    ∀ B : ℕ, 1 ≤ B → 3 * (2 * B + 1) ^ 2 < n →
    (1 + L1low n B) ^ 2 / (B : ℝ) ≤ (ε - 1 / (n : ℝ)) ^ 2 →
    ∀ τ : ℝ, τ ≤ ((ε - 1 / (n : ℝ)) / L1low n B ^ 2) ^ 2 →
    ∀ (k : ZMod n) (Lst : Finset (ZMod n)),
      (∀ β : ZMod n,
          τ ≤ ‖ft (fun x => ((accessFn Pred (k.val • G) x : ℤ) : ℂ)) β‖ ^ 2 → β ∈ Lst) →
        jReductionOutput lam B G (k.val • G) Lst = {k}

/-- C44-10x (Theorem 10 for `J` with explicit parameters): `(3 + log(2B+1))^2 / B ≤ η^2` and
the threshold `τ = (η / (2 + log(2B+1))^2)^2`. -/
def JRecoverExplicit : Prop :=
  ∀ (A : Type) [AddCommGroup A] [DecidableEq A] (G : A) (n : ℕ) [NeZero n] [Fact n.Prime],
    n ≠ 2 → addOrderOf G = n → ∀ (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    ∀ (Pred : A → ℤ), (∀ u : ZMod n, u ≠ 0 → Pred (u.val • G) = 1 ∨ Pred (u.val • G) = -1) →
    ∀ ε : ℝ, (1 / 2 + ε) * ((n : ℝ) - 1) ≤
        (((univ.erase (0 : ZMod n)).filter (fun u => Pred (u.val • G) = J lam u)).card : ℝ) →
    0 < ε - 1 / (n : ℝ) →
    ∀ B : ℕ, 1 ≤ B → 3 * (2 * B + 1) ^ 2 < n →
    (3 + Real.log (2 * (B : ℝ) + 1)) ^ 2 / (B : ℝ) ≤ (ε - 1 / (n : ℝ)) ^ 2 →
    ∀ (k : ZMod n) (Lst : Finset (ZMod n)),
      (∀ β : ZMod n,
          ((ε - 1 / (n : ℝ)) / (2 + Real.log (2 * (B : ℝ) + 1)) ^ 2) ^ 2 ≤
            ‖ft (fun x => ((accessFn Pred (k.val • G) x : ℤ) : ℂ)) β‖ ^ 2 → β ∈ Lst) →
        jReductionOutput lam B G (k.val • G) Lst = {k}

end Ecdlp.ParityFourier
