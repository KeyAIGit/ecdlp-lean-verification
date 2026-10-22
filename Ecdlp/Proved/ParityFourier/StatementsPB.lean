import Ecdlp.Proved.ParityFourier.Statements

/-!
# Frozen statements PB (parity reduction with random shifts and binary division)

This file fixes the statements; proof files must not edit it.

Process note: before this file was frozen, scratch proofs existed for
* PB-1 (`MajorityVote`), in a variant: the uniform product measure
  `Measure.pi (fun _ : Fin m => uniformOn univ)` and a `[0, 1]`-valued `V`
  in place of the counting form with an indicator frozen here;
* PB-2 (`VoteIdentity`), the same statement;
* a lemma that a proof of PB-3 may use: outside a window of shifts between
  `n - c` and `n - y.val`, the guessed wrap agrees with the true wrap (for an
  integer guess `c`; PB-3 uses a rational guess).
The drafter of this file read only the statement lines of those scratch
files, not the proofs. The statement audit should therefore judge PB-1 and
PB-2 against the paper claims, not against the scratch proofs. No proof of
PB-3, PB-4, PB-4g or PB-5 existed when this file was frozen.

Sources (all EXPLORATORY, none peer-reviewed):
* `reports/research_os/PARITY_BREAK_EVEN_2026_10.md` ("BE" below):
  Section 3 (mechanism: guess-independent queries `[2^-t]Q + [r]G`, a guess
  of `x` to precision about `ε`, one shared set of answers), Section 4
  (rigour sketch: on the correct-guess path the votes of a step are i.i.d.
  functions of fresh shifts with advantage at least `7ε/8`; Hoeffding plus a
  union bound over the `L` steps; wrong paths are rejected by checking
  `[k]G = Q`), Section 6 (rows "shared-query, tolerance eps/8" and
  "tolerance eps/2"), Section 7.
* `reports/research_os/PARITY_COVERAGE_MAP.md`, Section 0 ("Scale of
  relevance") and row P.
* The published ingredients as BE quotes them: random shifts, majority votes
  and a guess of `x` to precision `ε` (Schnorr, ECCC TR98-033, proof of
  Thm 5); Fischlin-Schnorr binary division on the guess-independent points
  `[2^-t]Q + [r]G` (as described in Sidorenko-Schoenmakers 2005, Sec. 3.1,
  and Hastad-Naslund ECCC TR99-037, Sec. 3.1). None of these papers is
  formalized; the statements below do not depend on them.

The frozen inputs a proof is expected to use: PB-1 and PB-3 (with PB-2) for
PB-4, PB-4 for PB-4g, and PB-4g for PB-5.

Notation as in `Statements.lean`: `n` is prime, `n ≠ 2`, `[u] = u.val`, the
representative of `u : ZMod n` in `[0, n)`; the parity of `u` is
`u.val % 2`. F4a and F4b (`HalvingRecovers`, `GroupHalvingRecovers`) are the
exact-oracle case, with Schnorr's decision-dependent query `(y - lsb y)/2`;
the reduction here uses binary division instead.

Model (explicit choices):
* Predictor. A deterministic function `P : ZMod n → ℕ` (group form:
  `Pred : A → ℕ`, read at `[z]G = z.val • G`). It predicts the parity
  `z.val % 2`; a value other than `0` or `1` counts as wrong. Its advantage
  is any real `ε` with `#{z ∈ ZMod n : P z = z.val % 2} ≥ (1/2 + ε) n`,
  i.e. `Pr_z[P correct] ≥ 1/2 + ε` for uniform `z`, the point `z = 0`
  included. Errors may be placed arbitrarily (worst case), but they are
  fixed in advance: `P` is a function of the queried point only. No
  independence of errors is assumed.
* Randomness. The only randomness is the reduction's own: a table
  `r : Fin L → Fin m → ZMod n` of `L·m` shifts, uniform over all such tables
  (equivalently, `L·m` independent uniform shifts). "Probability" means the
  exact fraction `#{r : event} / #(Fin L → Fin m → ZMod n)` of tables. The
  scalar `x`, the predictor and the guess are fixed (every `x`, every `P`).
* Queries. At step `t < L` the reduction queries the `m` points
  `y_t + r t i`, where `y_t = x · 2^-t` in `ZMod n` (group form:
  `[h^t]Q + [r t i]G` with `2h ≡ 1 (mod n)` and `Q = [x]G`). These points do
  not depend on any guess or on any earlier decision, so all guesses share
  one answer table `a t i` (`pbAnswers`, `pbGroupAnswers`); the decoder
  receives only `r`, `a` and a guess, never `x` or `P`.
* Vote (binary division). For `n` odd, `(y + r).val ≡ y.val + r.val + w`
  (mod 2) with the wrap `w = [n ≤ y.val + r.val]` (PB-2). Given an answer
  `a` for the parity of `y + r`, the shift `r` and a rational guess
  `c ≈ y.val`, the vote for the parity of `y` is
  `(a + r.val + [n - c ≤ r.val]) % 2`: the true wrap is replaced by the wrap
  decided by the guess (`pbVote`). A step decides `1` iff strictly more than
  half of its `m` votes are `1` (`pbBit`).
* Guess path. From a rational initial guess `c_0`, the guess is updated by
  `c_{t+1} = (c_t + b_t n) / 2`, where `b_t` is the decided bit (`pbPath`).
  If `b_t` is the parity of `y_t`, then `y_{t+1}.val = (y_t.val + b_t n)/2`,
  so the error `c_t - y_t.val` halves exactly at each step. After `L` steps
  with `n ≤ 2^L` the output is `x' = 2^L · round(c_L)` in `ZMod n`
  (`pbDecode`).
* Guess grid. The `N` guesses `(2j + 1) n / (2N)`, `j < N` (centres of `N`
  equal cells of `[0, n)`), all decoded from the same answer table
  (`pbCandidates`). Group form: a candidate `x'` is kept only if
  `[x']G = Q` (`pbGroupOutput`).
* Success. PB-4: the decoder run with one guess within `Δ` of `x.val`
  outputs `x`. PB-4g: `x` is among the `N` candidates. PB-5: the verified
  output set is exactly `{x}`.

Statements:
* PB-1 `MajorityVote` (BE Sec. 4, "Hoeffding"): if a uniform `ω ∈ Ω` is good
  with probability at least `1/2 + δ`, `δ ≥ 0`, then among `m` independent
  uniform draws at most half are good with probability at most
  `exp(-2 m δ^2)`.
* PB-2 `VoteIdentity` (BE Sec. 3, binary division): for odd `n`,
  `(y + r).val % 2 = (y.val + r.val + [n ≤ y.val + r.val]) % 2`.
* PB-3 `VoteAdvantage` (BE Sec. 3-4, translation-invariant counting): if
  `|c - y.val| ≤ Δ`, the vote at shift `r` from the answer `P (y + r)` gives
  the parity of `y` for at least `#{z : P z = z.val % 2} - (Δ + 1)` shifts.
  With advantage `ε` this is a vote advantage of at least `ε - (Δ + 1)/n`.
* PB-4 `NoisyHalvingRecovers` (BE Sec. 4, one guess): if `|c_0 - x.val| ≤ Δ`,
  `(Δ + 1)/n ≤ ε` and `n ≤ 2^L`, the decoder fails with probability at most
  `L · exp(-2 m (ε - (Δ + 1)/n)^2)` (Hoeffding per step on the correct
  path, union bound over the `L` steps). "Noisy" means that `P` may err; the
  errors are not assumed random.
* PB-4g `NoisyHalvingGrid` (BE Sec. 4 and Sec. 6, "tolerance eps/8"): with
  `N ≥ 4/ε` grid guesses sharing one answer table and `1/n ≤ 7ε/8`, `x` is
  missing from the candidates with probability at most
  `L · exp(-2 m (7ε/8 - 1/n)^2)`.
* PB-5 `GroupNoisyHalvingRecovers` (BE Sec. 4, lifting; "wrong paths are
  rejected by checking `[k]G = Q`"): in any additive commutative group with
  decidable equality and `G` of odd prime order `n`, with queries
  `[h^t]Q + [r]G`, the verified output never contains a wrong value, and it
  differs from `{x}` with probability at most `L · exp(-2 m (7ε/8 - 1/n)^2)`.

Deviations from the paper:
* BE Sec. 4 gives the correct-path vote advantage as at least `7ε/8`; here
  it is `7ε/8 - 1/n` (PB-4g, PB-5) and `ε - (Δ + 1)/n` (PB-4): the `+1`
  counts the integer shifts in a window of real length `Δ`.
* BE speaks of about `8/ε` guesses (Sec. 7) or `2/ε` to `8/ε` (Sec. 3);
  PB-4g and PB-5 use `N ≥ 4/ε` centred grid points, which gives the
  tolerance `εn/8` of the BE Sec. 6 row "tolerance eps/8". PB-4 with a
  general `Δ` also covers other tolerances (e.g. `Δ = εn/2`).
* The advantage counts all of `ZMod n`, the point `z = 0` (`O`) included,
  as in BE Sec. 1 ("over uniform points"). A predictor with
  `#{z ≠ 0 correct} ≥ (1/2 + ε)(n - 1)` (the convention of
  `StatementsC44R.lean`) satisfies the hypothesis with `ε - 1/n` in place
  of `ε`.
* Ties in a majority (possible for even `m`) count as failures in PB-1; the
  decision rule `pbBit` resolves a tie as `0`.
* BE's histogram evaluation of the votes (about `16/ε` buckets, `O(1)` per
  vote) is not modelled: `pbBit` recounts all `m` votes for each guess. This
  changes the cost, not the output.
* The reduction is given `ε` (through `N` and the hypotheses). BE does not
  discuss an unknown `ε`; a search over `ε` is not modelled.

When the statements say something: the hypotheses hold for the exact
predictor `P z = z.val % 2` (`ε = 1/2`) and for predictors that err on up to
`(1/2 - ε) n` arbitrary points; `ε ≤ 1/2` is forced. The bounds are below `1`
once `m > ln L / (2 δ^2)` with `δ` the vote advantage. Arithmetic estimate,
not formalized: `L · exp(-2 m δ^2) ≤ 1/4` for `m ≥ ln(4L) / (2 δ^2)`; with
`δ ≈ 7ε/8` and `L = 256` this is `L · m ≈ 2^10.2 ε^-2` predictor calls per
run; BE's `2^10.59` (and `2^12.21` for `δ ≈ ε/2`) additionally divides by
`1 - 1/4` for restarts after a failed run (BE script `breakeven.py`), which
are not modelled here. The
BE Section 6 constants (`c ≈ 2^10.59`, `2^12.21`, `2^17`) rest on BE's own
parameter choices and are not restated or checked here.

Not claimed here:
* No cost statement. That the reduction makes `L·m` predictor calls, shared
  by all `N` guesses, is visible in the definitions (the table `pbAnswers`
  has `L·m` entries and does not depend on the guess) but is not a theorem.
  Not formalized: the cost constant `c` in `c·ε^-2` calls (`2^10.6` to
  `2^12.2` derived in BE, `2^17` from Schnorr's `m = 2n ε^-2`), the per-call
  cost `C = C_F + C_Q`, the histogram lookups, the memory, the `N`
  verifying scalar multiplications, running time in any model, and the
  break-even `ε*` (about `2^-56` to `2^-51`) against rho with negation and
  GLV (`2^127.03` group operations).
* Not formalized: the Fischlin-Schnorr black-box lower bound
  `(ln 2/4) L ε^-2` (Rabin function) and the floor near `2^-58`; the
  `ε^-4`, `ε^-6` and `ε^-8` terms (FS via SS Lemma 8, SS eq. (7), ACGS) and
  the claim that they are RSA/Rabin artefacts; the verdicts on D5.2.1,
  D9.2.1, D9.2.3 and on the "2^-26" figure.
* Not formalized: the harness `reduction.py` (which re-queries for every
  guess), its `55 L ε^-3` worst-case cost and its logged constants
  (`27.0-99.8 L ε^-2`); the toy checks of BE Sec. 5.
* Shifts that are not uniformly random: nothing is claimed for shifts
  drawn from a pseudo-random generator or for any structured table.
* Other oracle models: randomized predictors (unless every fixing of the
  coins has advantage `ε`), stateful or adaptive oracles that see earlier
  queries. The harness oracle (`planted_oracle` in `reduction.py`) and the
  toy oracles of BE Sec. 5 are deterministic functions of the point, covered
  only after recoding to `0/1` and with their exact advantage, not their
  nominal `ε`. AGS
  list decoding (needed for J and g, not here) is not formalized.
* Other bits and targets: Schnorr's Theorem 5 for bits other than the least
  significant one (`j0 ≥ 1`), his decision-dependent query, Akavia's
  segment-predicate route (row P), J and g.
* Hard-core statements in the asymptotic sense (polynomial time, negligible
  advantage): only the success probability of one run with given
  `ε, N, L, m` is stated.
* Elliptic curves: `A` is an abstract group; no curve, secp256k1 included,
  is instantiated.
* Reductions from `Q` alone in the `ZMod n` forms: PB-3, PB-4 and PB-4g
  apply `P` to scalars, and `pbAnswers P x r` is formed with `x`. They state
  only that the decoder is correct on such answers. Only PB-5 forms its
  queries from `Q = [x]G` with group operations.
-/

namespace Ecdlp.ParityFourier

open Finset

/-- Binary-division vote for the parity of `y`, from an answer `a` for the parity of `y + r`,
the shift `r` and a rational guess `c ≈ y.val`: `(a + r.val + [n - c ≤ r.val]) % 2`. The true
wrap `[n ≤ y.val + r.val]` is replaced by the wrap decided by the guess. -/
def pbVote {n : ℕ} (a : ℕ) (c : ℚ) (r : ZMod n) : ℕ :=
  (a + r.val + (if (n : ℚ) - c ≤ (r.val : ℚ) then 1 else 0)) % 2

/-- Majority decision of one step: `1` iff strictly more than half of the `m` votes are `1`. -/
def pbBit {n m : ℕ} (r : Fin m → ZMod n) (a : Fin m → ℕ) (c : ℚ) : ℕ :=
  if m < 2 * (univ.filter (fun i => pbVote (a i) c (r i) = 1)).card then 1 else 0

/-- Guess path: `c_0` is the initial guess; for `t < L`,
`c_{t+1} = (c_t + b_t n) / 2` with `b_t = pbBit (r t) (a t) c_t`. The path is constant after
step `L`. -/
def pbPath {n L m : ℕ} (r : Fin L → Fin m → ZMod n) (a : Fin L → Fin m → ℕ) (c0 : ℚ) : ℕ → ℚ
  | 0 => c0
  | t + 1 =>
      if h : t < L then
        (pbPath r a c0 t + (pbBit (r ⟨t, h⟩) (a ⟨t, h⟩) (pbPath r a c0 t) : ℚ) * (n : ℚ)) / 2
      else pbPath r a c0 t

/-- Output of the decoder for one initial guess: `2^L · round(c_L)` in `ZMod n`. It reads only
the shift table, the answer table and the guess. -/
def pbDecode {n L m : ℕ} (r : Fin L → Fin m → ZMod n) (a : Fin L → Fin m → ℕ) (c0 : ℚ) :
    ZMod n :=
  (2 : ZMod n) ^ L * (((round (pbPath r a c0 L) : ℤ)) : ZMod n)

/-- The answer table of the predictor `P` on the guess-independent queries
`y_t + r t i`, `y_t = x · 2^-t`. -/
def pbAnswers {n L m : ℕ} (P : ZMod n → ℕ) (x : ZMod n) (r : Fin L → Fin m → ZMod n) :
    Fin L → Fin m → ℕ :=
  fun t i => P (x * (2 : ZMod n)⁻¹ ^ (t : ℕ) + r t i)

/-- The `j`-th grid guess `(2j + 1) n / (2N)`: the centre of the `j`-th of `N` equal cells
of `[0, n)`. -/
def pbGuess (n N j : ℕ) : ℚ := (2 * (j : ℚ) + 1) * (n : ℚ) / (2 * (N : ℚ))

/-- Candidates from the `N` grid guesses, all decoded from the same shift and answer tables. -/
def pbCandidates {n L m : ℕ} (N : ℕ) (r : Fin L → Fin m → ZMod n) (a : Fin L → Fin m → ℕ) :
    Finset (ZMod n) :=
  (range N).image (fun j => pbDecode r a (pbGuess n N j))

/-- Group form of the answer table: `Pred` at the points `[h^t]Q + [r t i]G`. -/
def pbGroupAnswers {A : Type*} [AddCommGroup A] {n L m : ℕ} (Pred : A → ℕ) (G Q : A) (h : ℕ)
    (r : Fin L → Fin m → ZMod n) : Fin L → Fin m → ℕ :=
  fun t i => Pred ((h ^ (t : ℕ)) • Q + (r t i).val • G)

/-- Verified output of the group reduction: the candidates `x'` with `[x']G = Q`. -/
def pbGroupOutput {A : Type*} [AddCommGroup A] [DecidableEq A] {n L m : ℕ} (G Q : A) (N : ℕ)
    (r : Fin L → Fin m → ZMod n) (a : Fin L → Fin m → ℕ) : Finset (ZMod n) :=
  (pbCandidates N r a).filter (fun x' => x'.val • G = Q)

/-- PB-1. Majority vote (Hoeffding): if at least a `1/2 + δ` fraction of `Ω` is good, `δ ≥ 0`,
then the fraction of `m`-tuples in which at most half of the entries are good is at most
`exp(-2 m δ^2)`. -/
def MajorityVote : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (good : Ω → Prop) [DecidablePred good] (δ : ℝ),
    0 ≤ δ → (1 / 2 + δ) * (Fintype.card Ω : ℝ) ≤ ((univ.filter good).card : ℝ) →
    ∀ m : ℕ,
      ((univ.filter (fun s : Fin m → Ω =>
          2 * (univ.filter (fun i => good (s i))).card ≤ m)).card : ℝ) /
        (Fintype.card (Fin m → Ω) : ℝ) ≤ Real.exp (-2 * (m : ℝ) * δ ^ 2)

/-- PB-2. Vote identity: for odd `n`, the parity of `y + r` is the parity of
`y.val + r.val` plus the wrap `[n ≤ y.val + r.val]`. -/
def VoteIdentity : Prop :=
  ∀ (n : ℕ) [NeZero n], Odd n → ∀ y r : ZMod n,
    (y + r).val % 2 = (y.val + r.val + (if n ≤ y.val + r.val then 1 else 0)) % 2

/-- PB-3. Vote advantage: with a guess `c` within `Δ` of `y.val`, the vote from the answer
`P (y + r)` gives the parity of `y` for at least `#{z : P z = z.val % 2} - (Δ + 1)` shifts. -/
def VoteAdvantage : Prop :=
  ∀ (n : ℕ) [NeZero n], Odd n → ∀ (P : ZMod n → ℕ) (y : ZMod n) (c : ℚ) (Δ : ℝ),
    |(c : ℝ) - (y.val : ℝ)| ≤ Δ →
      ((univ.filter (fun z : ZMod n => P z = z.val % 2)).card : ℝ) - (Δ + 1) ≤
        ((univ.filter (fun r : ZMod n => pbVote (P (y + r)) c r = y.val % 2)).card : ℝ)

/-- PB-4. One guess: a predictor with advantage `ε` and an initial guess within `Δ` of
`x.val`, with `(Δ + 1)/n ≤ ε` and `n ≤ 2^L`, make the decoder output `x` except on a fraction
at most `L · exp(-2 m (ε - (Δ + 1)/n)^2)` of the shift tables. -/
def NoisyHalvingRecovers : Prop :=
  ∀ (n : ℕ) [Fact n.Prime], n ≠ 2 →
    ∀ (P : ZMod n → ℕ) (ε : ℝ),
      (1 / 2 + ε) * (n : ℝ) ≤ ((univ.filter (fun z : ZMod n => P z = z.val % 2)).card : ℝ) →
    ∀ (x : ZMod n) (c0 : ℚ) (Δ : ℝ), |(c0 : ℝ) - (x.val : ℝ)| ≤ Δ →
      (Δ + 1) / (n : ℝ) ≤ ε →
    ∀ L m : ℕ, n ≤ 2 ^ L →
      ((univ.filter (fun r : Fin L → Fin m → ZMod n =>
          pbDecode r (pbAnswers P x r) c0 ≠ x)).card : ℝ) /
        (Fintype.card (Fin L → Fin m → ZMod n) : ℝ) ≤
      (L : ℝ) * Real.exp (-2 * (m : ℝ) * (ε - (Δ + 1) / (n : ℝ)) ^ 2)

/-- PB-4g. Guess grid: with `N ≥ 4/ε` grid guesses sharing one answer table and
`1/n ≤ 7ε/8`, `x` is missing from the candidates on a fraction at most
`L · exp(-2 m (7ε/8 - 1/n)^2)` of the shift tables. -/
def NoisyHalvingGrid : Prop :=
  ∀ (n : ℕ) [Fact n.Prime], n ≠ 2 →
    ∀ (P : ZMod n → ℕ) (ε : ℝ),
      (1 / 2 + ε) * (n : ℝ) ≤ ((univ.filter (fun z : ZMod n => P z = z.val % 2)).card : ℝ) →
    1 / (n : ℝ) ≤ 7 * ε / 8 →
    ∀ (x : ZMod n) (N L m : ℕ), 4 ≤ ε * (N : ℝ) → n ≤ 2 ^ L →
      ((univ.filter (fun r : Fin L → Fin m → ZMod n =>
          x ∉ pbCandidates N r (pbAnswers P x r))).card : ℝ) /
        (Fintype.card (Fin L → Fin m → ZMod n) : ℝ) ≤
      (L : ℝ) * Real.exp (-2 * (m : ℝ) * (7 * ε / 8 - 1 / (n : ℝ)) ^ 2)

/-- PB-5. Group lifting: `G` of odd prime order `n`, `2h ≡ 1 (mod n)`, `Q = [x]G`, a predictor
`Pred` with advantage `ε` on the multiples of `G`, queries `[h^t]Q + [r]G`, `N ≥ 4/ε` grid
guesses and the check `[x']G = Q`. For every shift table the verified output is contained in
`{x}`, and it differs from `{x}` on a fraction at most `L · exp(-2 m (7ε/8 - 1/n)^2)` of the
shift tables. -/
def GroupNoisyHalvingRecovers : Prop :=
  ∀ (A : Type) [AddCommGroup A] [DecidableEq A] (G : A) (n : ℕ) [Fact n.Prime], n ≠ 2 →
    addOrderOf G = n → ∀ h : ℕ, (2 * h) % n = 1 →
    ∀ (Pred : A → ℕ) (ε : ℝ),
      (1 / 2 + ε) * (n : ℝ) ≤
        ((univ.filter (fun z : ZMod n => Pred (z.val • G) = z.val % 2)).card : ℝ) →
    1 / (n : ℝ) ≤ 7 * ε / 8 →
    ∀ (x : ZMod n) (N L m : ℕ), 4 ≤ ε * (N : ℝ) → n ≤ 2 ^ L →
      (∀ r : Fin L → Fin m → ZMod n,
          pbGroupOutput G (x.val • G) N r (pbGroupAnswers Pred G (x.val • G) h r) ⊆ {x}) ∧
      ((univ.filter (fun r : Fin L → Fin m → ZMod n =>
          pbGroupOutput G (x.val • G) N r (pbGroupAnswers Pred G (x.val • G) h r) ≠ {x})).card
            : ℝ) /
        (Fintype.card (Fin L → Fin m → ZMod n) : ℝ) ≤
      (L : ℝ) * Real.exp (-2 * (m : ℝ) * (7 * ε / 8 - 1 / (n : ℝ)) ^ 2)

end Ecdlp.ParityFourier
