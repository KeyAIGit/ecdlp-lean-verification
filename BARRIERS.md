# Formalization-status registry (barriers & no-go map)

What of the ECDLP knowledge corpus (`data/KG_CLAIM_FORMALIZATION_v1.csv`, 486
atomic claims) can be machine-checked in Lean 4 + Mathlib today, and what cannot —
and *why*. The "cannot" rows are the contribution: they are a precise map of the
foundations that formal cryptography for ECDLP still lacks.

Categories below are grounded in the corpus's own `formal_status` / `mathlib_area`
annotations (the corpus authors' assessment), cross-checked against the verified
base. This is a living document; counts are for the v1 corpus.

## Summary

| Status | Count | Meaning |
|---|---|---|
| **Proved** | see `VERIFIED.md` (~268 distinct results / 307 rows) | accepted by the Lean kernel, no `sorry`, no custom axioms |
| **Tractable now** | ~55 | `GroupTheory.OrderOfElement / Subgroup` — structural group facts |
| **Barrier: no cost model** | ~55 | complexity claims; Lean has no "group-operation count" framework |
| **Barrier: not in Mathlib** | ~62 | 38 quantum-circuit cost model, 24 lattice reduction |
| **Partial: curve / polynomial depth** | ~33 | `EllipticCurve`, `DivisionPolynomial`, `MvPolynomial` — Mathlib has prerequisites, not isogeny/pairing/ECDLP constructions |
| **Informal / meta** | ~133 | survey/commentary; not a formal statement by nature |
| **Unassigned** | ~174 | needs human triage before a Lean area can be chosen |

(Counts overlap at the margins and are indicative, not a partition.)

## Proved (the tractable zone, realised)

All in `Ecdlp/` and listed in `VERIFIED.md`. The structural theorems live in the
group-theory zone and are the realised part of "Tractable now":

- secp256k1 parameters & GLV/β eigenvalue facts — `native_decide` (concrete).
- `order_dvd_card` (Lagrange), `cofactor_card_mul_index` (`#E = n·h` abstractly),
  `orderOf_eq_card_of_prime` (prime order ⇒ generator, no small subgroup),
  `cube_root_of_eigenvalue` (root of `x²+x+1` ⇒ `x³=1`) — Mathlib.
- **Distinct-prime torsion x-loci are disjoint** (no-go certificate family, **kernel-verified**).
  For `y²=x³+7`, the `x`-coordinates of the `ℓ`- and `ℓ'`-torsion (`ℓ≠ℓ'` prime) never coincide,
  via `gcd(ψ_ℓ, ψ_ℓ') = 1` with an explicit resultant + Bézout certificate. The **entire pairwise
  `{2,3,5,7}` family is now proved** in `Ecdlp/Proved/CoprimePsi{2Psi3,2Psi5,2Psi7,3Psi5,3Psi7,5Psi7}.lean`,
  together with the full `preΨ₄ ⊥ {2,3,5,7}` set (`CoprimePsi{2PrePsi4,3PrePsi4,4Psi5,4Psi7}.lean`) —
  giving **full mutual disjointness of the `{2,3,4,5,7}`-torsion `x`-loci**. Each is an `IsCoprime`
  theorem discharged by a CAS extended-Euclid Bézout certificate over `𝔽_p` (`native_decide` residue
  equations); e.g. `E[5]⊥E[7]` (`Res = 2¹⁹²·3¹⁴⁴·7⁹⁶`, `CoprimePsi5Psi7.lean`). In every case the
  resultant's prime support equals the bad-reduction primes `{2,3,7}` of the curve — the only primes
  where the loci can collide on reduction. Certificates in `scripts/certs/torsion_disjoint_*.py`.

### Foundation formalized: the generic-group `Ω(√p)`/`Θ(√n)` results
Previously listed under B1 as blocked-by-missing-cost-model, the **Shoup/Nechaev
generic lower bound is now machine-checked** (`Ecdlp/Proved/GenericGroupBound.lean`,
`Secp256k1GenericSecurity.lean`, `BabyStepGiantStep.lean`, `PollardRho.lean`). The
key insight: its information-theoretic core needs no general cost model — the
algebraic data available to a generic algorithm is exactly the set of affine forms
`a + b·X` it has formed over `ZMod p`, and the bound is a collision count over that
set. Results: `generic_dlog_query_bound` (`p ≤ q·q`), `generic_dlog_sqrt_bound`
(`√p ≤ q`), `generic_success_le` (quantitative), `secp256k1_generic_security`
(`2^127 < q` — ≥128-bit generic security of secp256k1, conditional on the published
primality of `n`); matching `O(√n)` upper bounds `bsgs_decomp` / `pollard_rho_*`
(so generic DLP is `Θ(√n)`). This is the first Mathlib-checked generic-group lower
bound for the discrete log.

**Scope of this bound (read `notes/SECURITY_SCOPE.md`).** It is a *real theorem* but a
narrow one: it bounds only **classical, generic** (black-box) algorithms. It is **not**
unconditional — it says nothing about non-generic attacks that read the point encoding
(for `𝔽_p^×`, index calculus provably beats `Ω(√p)`; for EC over a prime field no such
algorithm is known but its non-existence is unproven), and it is **classical-only** —
Shor solves ECDLP in quantum polynomial time. secp256k1's resistance to all *known*
non-generic classical attacks is separately machine-checked (anti-MOV/anti-Smart, below).

## Barriers (the contribution)

### B1. No cost model in Lean (~54 claims)
Remaining complexity statements — index calculus subexponential, distinguished-point
parallel speedups, exact `Θ` running times. Lean has no framework for "number of
group operations" / oracle-query cost, so these cannot be stated faithfully, only
their *structural* corollaries. (The generic `Ω(√p)` lower bound and `O(√n)` upper
bounds are now formalized — see above — because their cores sidestep the cost
model.) **Foundation still needed:** a general oracle / cost model in Mathlib for
exact `Θ` statements.

### B2. Not in Mathlib — missing theories (~62 claims)
- **Lattice reduction (24)** — HNP / biased-nonce ECDSA attacks (LLL/BKZ, CVP).
  Mathlib has no lattice-reduction theory.
- **Quantum circuit cost model (38)** — Shor-style ECDLP resource estimates.
  Out of scope for Mathlib.

### B3. Partial foundations — curve & polynomial depth (~33 claims)
- **Summation / Semaev polynomials** (`MvPolynomial`, partial) — Mathlib has
  multivariate polynomials but not the elliptic summation polynomials `Sₙ`. **Base case
  broken open:** the 3rd Semaev polynomial `S₃` and its *forward* direction
  (`P₁+P₂+P₃ = O ⇒ S₃(x₁,x₂,x₃) = 0`) are now machine-checked in **both** nondegenerate
  cases — chord (`S₃_eq_zero_of_chord`) and tangent/doubling (`S₃_eq_zero_of_tangent`), each
  with a secp256k1 corollary (`Ecdlp/Proved/SemaevThree.lean`) — the first Semaev
  formalization in Lean, and now **connected to Mathlib's formalized elliptic-curve group
  law** in every nondegenerate case (`secp256k1_semaev_three_point` for the chord case and
  `secp256k1_semaev_three_point_double` for tangent/doubling: the hypothesis is the actual
  group relation `P₁+P₂+P₃ = O` on `secp256k1.toAffine.Point`, not a coordinate equation).
  The **full `S₃` characterization is now closed** — `S₃_eq_zero_iff` /
  `secp256k1_semaev_three_iff` prove `S₃(x₁,x₂,x₃) = 0 ⟺ x₃ = x(P₁+P₂) or x(P₁−P₂)` (both
  directions), via a sympy-certified two-root master factorization. And **`S₄` is now started**
  (`Ecdlp/Proved/SemaevFour.lean`): `S₄ = Res_X(S₃(x₁,x₂,X), S₃(x₃,x₄,X))` built on Mathlib's
  `Polynomial.resultant`, with **both directions**: the forward `S₄_eq_zero_of_common_root` (a shared root of the two
  `S₃` slices ⟹ `S₄ = 0`) and the reverse/meaning `S₄_common_root_of_eq_zero` (`S₄ = 0` ⟹ the
  two slices share a root **in the field**, since `S₃`'s slice splits with the known roots
  `x(P₁±P₂)` — via `resultant_eq_prod_eval`), plus symmetries — the first `S₄` in Lean, and the
  recursion index calculus over `𝔽_{p^k}` actually uses.

  **Scope of what this closes — and why it is *not* an attack on secp256k1.** Semaev summation
  polynomials are the algebraic engine of **index calculus over *extension* fields `𝔽_{p^n}`,
  `n > 1`** (Gaudry–Diem–Semaev): one solves the `Sₙ = 0` system over a factor base with Gröbner
  bases, and the complexity depends on `n`. Over a **prime** field — which is exactly
  secp256k1's `𝔽_p` — there is **no known** summation-polynomial index-calculus algorithm that
  beats the generic `Ω(√n)` bound, and known variants (including Petit's composed low-degree
  rational maps, *Faster Algorithms for the ECDLP in the Large Characteristic Case*) lose to
  generic methods at cryptographic parameters — but the **asymptotic picture and the role of any
  special structure remain open**; this is *not* a proven no-go. So this line is a
  **formalization contribution** (and an open research direction), not a path toward breaking
  secp256k1: `S₃`/`S₄` are the standard objects and
  their defining recursion, now machine-checked, but they compute nothing about any specific
  discrete log on a prime-field curve. `S₃` (base case, fully characterized) together with `S₄`
  (first recursion step, both directions) is the **conceptually complete unit**: it establishes
  the object *and* proves the resultant recursion means what it should. And the **forward
  direction is now generalized to the whole infinite family in a single lemma**
  (`resultant_eq_zero_of_common_root`, `Ecdlp/Proved/SemaevFour.lean`): for *any* two univariate
  polynomials sharing an evaluation-root, their resultant vanishes — so since each Semaev step is
  `Sₙ₊₁ = Res_X(Sₙ(…,X), S₃(…,X))`, "the two slices share a root ⟹ `Sₙ₊₁ = 0`" holds at *every*
  level `n` by instantiating that one lemma (`S₄`'s forward direction is literally its `n = 3`
  case). Higher `Sₙ` (`n ≥ 5`) are thus the *same* recursion at larger degree — their forward
  direction is already covered by the engine lemma, and the concrete plumbing is deliberately
  **not** pursued, as it adds scale without new content or new reach against the curve.

  **Decomposition layer + the prime-field cost frontier (partial, honestly bounded).** On top of
  the polynomials, the *point-decomposition* meaning is now machine-checked
  (`Ecdlp/Proved/PointDecomposition.lean`): a target `R = P₁ + P₂` forces
  `S₃(x(P₁),x(P₂),x(R)) = 0`, so every 2-term decomposition lies on the Semaev variety — the
  structural reduction index calculus rests on. And one exact quantitative ingredient of the cost
  is proved (`Ecdlp/Proved/SemaevDegree.lean`): `S₃` has degree **exactly 2** in each variable
  (base of the `deg Sₘ = 2^{m−2}` tower), so each factor-base coordinate has **≤ 2 completions** —
  bounded relation fan-out. **What remains genuinely open (NOT a theorem here):** that this
  bounded-fan-out plus factor-base balance yields *no* subexponential algorithm over `𝔽_p`. The
  obstruction is that a prime field affords **no Weil restriction** to split the raw
  coordinate-only factor-base equation into the extension-field Gröbner systems used by
  Gaudry–Diem. Published prime-field variants instead add structured univariate map equations,
  and their total solving cost remains open; neither presentation is proved as hard as the
  original problem. This is part of the studied heuristic behind prime-field ECDLP staying
  `Θ(√n)`, but a *proof* would settle an open hardness conjecture and is **not** claimed. The
  kernel-checked results map
  *where the search lives and how it branches*; the cost lower bound itself stays in the open
  frontier, recorded here, not dressed as proved.

  **Exact M16 representation frontier (through TASK-025; theorem-only, non-run).**
  TASK-022 first kernel-checked the exact 56-variable, 29-equation guarded
  representation. TASK-023 now replaces that raw projective-scale and
  guard-witness redundancy by an exact finite affine/infinity chart cover.
  For a fixed `I : Finset (Fin 14)`, slots in `I` are `[1:0]` and every other
  slot is `[X_i:1]`; the literal polynomial system has exactly
  `14 - I.card` scalar variables and fifteen `H` equations. The base, thirteen
  internal, and final equation families have total-degree ceilings two, four,
  and two. The existential cover is exactly equivalent to the stage-14 chain,
  the guarded system, and, after injective base change into an algebraically
  closed target, the source frozen predicate. `[1:0]` is retained and `[0:0]`
  is never introduced. The `2^14` logical masks are not enumerated or
  materialized. These are representation counts and upper bounds, not
  independent relations, rank, yield, solving behavior, or a base-field
  descent theorem.
  TASK-024 then proves exact necessary conditions on those infinity masks.
  For affine external inputs, two adjacent intermediate infinity slots would
  force an external `v` coordinate to vanish. The exact logical cover therefore
  restricts from 16384 masks to the 987 separated subsets of the fourteen-slot
  path. Infinity at either boundary forces its endpoint projective determinant
  to vanish; if both endpoint determinants are nonzero, slots 0 and 13 are
  affine and the conditional cover has 377 masks. An isolated infinity also
  fixes each existing affine neighbor to the normalized current-input
  coordinate. These filters are necessary, not sufficient or unique, and the
  mask families are not production-enumerated.
  TASK-025 propagates those forced coordinates. Infinity slots at distance two
  force an explicit consecutive-input projective determinant to vanish, and
  slots at distance three force a literal three-input `HValue` to vanish.
  Under named local nonvanishing assumptions, the exact conditional logical
  mask counts contract cumulatively from 377 to 129, 69, and 36; an independent
  boundary-only refinement contracts 129 to 60. These counts describe
  necessary candidate-mask families, not realizable masks. A one-way
  projective-chain-to-`frozenC` implication over any field then gives explicit
  prefix and suffix obstructions. Six prefix and six suffix values cover all
  twelve internal slots with maximum frozen stage five. On the stated
  affine-input, endpoint-nonzero, balanced-obstruction-nonzero locus, every
  solution mask is empty and both complete covers are exactly the single
  affine chart. The source stage-14 equation is linked to that target chart
  only after the existing injective algebraically closed base change; target
  witnesses are not proved to descend.
  The regular locus remains conditional: symbolic nonzeroness, nonemptiness,
  density, probability, and genericity are not proved. One chart does not
  imply a unique witness, independent relation, usable yield or rank, solver
  readiness, reduced solving degree, or reduced total cost. Exactly four new
  mask-cardinality facts use `native_decide`; all propagation and cover
  implications use the ordinary kernel/Mathlib trust base.
  `CELL-M-PKC-SMOOTH-M16` remains `open_non_executable`,
  `CQ-SEMAEV-S17-SYSTEM-COST` remains `partial`, and
  `B-PKC-M16-COMPLETE-COST-BRIDGE` remains open on establishing a nonempty
  source-checkable regular locus or otherwise orchestrating the remaining
  finite cover, plus usable relation yield and rank, solving, recovery, sparse
  linear algebra, and total work. TASK-026 now resolves one bounded subquestion:
  on the three frozen synthetic `E_7` toy subgroups, fixed-before-sampling
  relations did reach the named affine regular locus (911 accepted exact
  relations, 907 affine regular; all six curve-arm gates passed). The matched
  GLV-orbit/plain differences were `-0.006987`, `-0.006329`, and `0.000000`
  with overlapping intervals and no `H_NEW`-qualifying size, so this is a
  known local simplification, not evidence of a GLV-specific mechanism.
  Source-faithful PKC relation construction, independence, rank, solver
  degree/memory/slope, recovery, end-to-end cost, and 256-bit persistence all
  remain open. The singleton is consumed; no solver or experiment is authorized.

  **GLV–Semaev relation-generation experiments (partial negatives, not a no-go;
  `HYP_GLV_SEMAEV_001`; P0→P4).**
  A five-rung reproducible benchmark line asks one question about the `j=0` family
  `E_b : y²=x³+b` over `p ≡ 1 (mod 3)`: does closing a Semaev factor base under the order-3 GLV
  automorphism orbit (`x ↦ βx`, invariant `u=x³`), or under a composed low-degree map, change
  the *relation-generation* cost beyond a constant factor? Every rung is an **empirical
  measurement, not a Lean theorem**. The replay checks establish relation-set agreement in their
  stated scopes; they do not validate complexity estimates or every solver component.

  A later exact scoped analysis closes the specific coordinatewise quotient premise.
  Simultaneous GLV relations carry a diagonal `C3` action, whereas `u_i=x_i^3`
  is the invariant map for `C3^m` and generically merges `3^(m-1)` diagonal
  orbits. The frozen certificate in `experiments/glv_diagonal_obstruction/`
  records 483 pairs on one diagonal-action graph versus 1449 coordinatewise
  same-cube pairs over `F_1009`; its independent validator exhaustively
  reconstructs the raw sets. This is an algebraic obstruction to that
  presentation, not a Semaev attack run or a universal Groebner lower bound.

  - **P0** (`experiments/p0_glv_semaev/`, m=2, lookup model): enumerate pair sums `P_i±P_j`,
    hash x-coords; the hit rate `≈ c·B_eff²/p` (16/20/24-bit toy curves; every counted equality
    re-verified by an actual `ec_add`). GLV closure gives `B_eff=3·B`, `u=x³` raises the constant
    to `c≈5.45` (`≈2.8×` vs plain) — a **constant ~3×**, **no exponent change**. Direct EC-pair
    enumeration is itself `Θ(B²)`, so it is *not* an index-calculus algorithm. (Two legacy 24-bit
    rows used cofactor-3 curves with an ambient-`E(𝔽_p)` base — geometry/yield sanity data, not
    valid subgroup-log relations; the corrected generator uses cofactor-1.)
  - **P1 / m=3** (`experiments/p1_petit/`, `p1_petit_m3/`): *solve* `S₃=0` (Tonelli–Shanks)
    resp. `S₄(x_i,x_j,X,x_R)=Res_Y(S₃(x_i,x_j,Y),S₃(X,x_R,Y))=0` instead of enumerating.
    The m=3 comparison covers three distinct factor-base indices; repeated-index decompositions
    are excluded. Its brute-force path is independent of `S₄` but shares `confirm_relation3`, so
    it is not a separately implemented EC oracle.
  - **P3** (`experiments/p3_sm_system/`, m=2,3): builds and Gröbner-solves the explicit
    finite-set presentation `{Sₘ₊₁=0, f_F(Xᵢ)=0}`, where `f_F=∏_{a∈F}(X-a)` has degree `|F|`
    by construction. For m=2 the custom Macaulay proxy returned `2|F|+1` for the tested
    `|F|=4,6,8,10,12` and two toy-prime sizes. Its two-empty-degree stopping rule has not been
    cross-checked with Singular/Sage/`msolve` or justified by a Hilbert-series theorem, so this
    is an observed proxy pattern, not an exact or p-independent degree-of-regularity law. The
    coupled `U=X³` auxiliary-variable presentation was ~15–20× larger and ~80× slower on the
    tested instances. The later diagonal-action analysis rules out treating
    coordinatewise cubes as the exact quotient, but does not rule out a
    materially different rational or elimination mechanism.
  - **P4** (`experiments/p4_petit/`, m=2): tests one six-variable composed-polynomial-map
    presentation at `|F|=4`. The proxy number was 7 versus 9, while the observed matrix and time
    were ~100× and ~4300× larger. This is useful descriptive data for that presentation, but it
    is neither a faithful implementation of Petit nor evidence against composed maps in general.

  **What the line establishes (measured):** the tested toy formulations provide reproducible
  partial negatives, and their relation sets replay against EC arithmetic in the stated scopes.
  **What it does not establish (open):** an exact/general degree-of-regularity law, the best
  prime-field factor-base encoding, a materially different phase-preserving formulation, a faithful
  Petit construction, or any asymptotic advantage/no-advantage result. The
  `O(|F|^{m-1}·solve)` loops are **not** subexponential
  index-calculus algorithms. So the real question — whether invariant-coordinate *relation
  generation* can change the prime-field asymptotics by a mechanism other than fixed orbit
  compression stays mathematically **open**, while
  `HYP_GLV_SEMAEV_001` is operationally **PARKED** by the decision substrate. No result here
  is a step toward breaking secp256k1; equality-replay alone
  cannot establish a complexity no-go. Per-run manifests + independent validators live under
  each `experiments/*/` directory. External Gröbner validation and sharper formulations are
  prerequisites before promoting this line to a publishable complexity barrier.

  **Open next node — `Sₘ` degree tower `2^{m−2}` (recorded, not yet built).** The base case is
  proved (`secp256k1_S₃poly_natDegree`: `deg S₃ = 2` in each variable) and `S₄`'s full symmetry is
  proved (`S₄_symm₁₂`/`S₄_symm₃₄`/`S₄_block_swap`). The next quantitative step, `deg S₄ = 4` in each
  variable, is a legitimate barrier node — it measures the degree blow-up that makes higher-order
  decompositions intractable — but is **not built**: `S₄` is currently the *scalar* resultant
  `Res_X(S₃(x₁,x₂,X), S₃(x₃,x₄,X))`, and stating its degree in `x₁` needs `S₄` reconstructed as a
  *polynomial in `x₁`* (coefficients over `F[x₁]`) plus a resultant-degree-in-a-parameter lemma —
  a real construction, not a quick corollary. Recorded here as the honest next frontier.
- **Weil pairing / isogeny depth** (no elliptic-isogeny module in the audited
  pinned/current Mathlib trees) — blocks
  *formalizing the MOV/FR transfer reduction itself*; the pairing is not in Mathlib. **This is
  the one place the Weil pairing touches secp256k1, and its security-relevant consequence is
  already closed here without the pairing:** MOV/FR would transfer the ECDLP into `𝔽_{p^k}^×`
  only for small embedding degree `k`, and `secp256k1_embedding_degree_gt_100`
  (`EmbeddingDegree.lean`) machine-checks `p^k ≢ 1 (mod n)` for all `1 ≤ k ≤ 100`, so no such
  transfer exists for secp256k1. Building the pairing itself (`e_n : E[n]×E[n] → μ_n` + the
  structure theorem `E[n] ≅ (ℤ/n)²`) is a multi-month research-grade port absent from all of
  Mathlib, master, and open PRs (see the upstream scan below) — worth doing as an upstream
  contribution, but it would add **no** security fact about secp256k1 that the embedding-degree
  bound does not already give. **In-repo frontier (2026-07):** the ladder toward
  `E[n] ≅ (ℤ/n)²` has moved — the L4 engine is ported (`normEDS_isEllSequence`,
  `NormEDSIsElliptic.lean`), the eval-bridge descent reduced node N5 to a scalar
  no-consecutive-zeros lemma, now **unblocked** and stated as the open stem
  `Ecdlp/Targets/normeds_no_consecutive_zero.lean`; the remaining CORE-by-effort item on
  that path is N7 (general multiplication formula). See the TASK-005 memo in
  `notes/POINT_COUNTING_KEYSTONE.md` and `notes/DIVISION_POLY_TORSION_MAP.md`.
  - **N7-uniform `x([n]P) = Φₙ(x)/ΨSqₙ(x)` (general `n`) — precise wall mapped (2026-07-18).**
    Fixed `n = 2,3,4,5` are landed as per-`n` coordinate-level `linear_combination` certificates
    (`MultiplicationFormula.lean`, `Triple/Quadruple/QuintupleMultiplicationFormula.lean`); the
    *uniform* statement is the missing rung. Mathlib v4.31 provides the univariate `Φ`/`ΨSq`/`preΨ`
    polynomials **and** their recurrences (`preΨ_even/odd`, `ΨSq_even/odd`, `Φ_ofNat`,
    `mk_Ψ_sq`) — but has **no y-coordinate (`ω`) division polynomial**, **no multiplication-by-`n`
    coordinate map**, and **no `Point`↔`Ψ/Φ` connection at all** (`Point` occurs once in
    `DivisionPolynomial/Basic.lean`, zero times in `Degree.lean`; verified against the pinned tree).
    So a from-substrate uniform proof must first **build** (i) the `ωₙ` (y-coordinate) division
    polynomial and its addition/recurrence theory, then (ii) the coordinate `[n]`-map, then (iii)
    the general induction `x([n+1]P) = addX(x([n]P), x, slope(…))` with `x([n]P)=Φₙ/ΨSqₙ` and the
    `ω`-based `y([n]P)` substituted — a single monstrous rational-function identity per step. This
    is upstream-grade, multi-month infrastructure (comparable to a stalled Mathlib PR), and it does
    **not** decompose into small independent rungs. **Note on the fast-feedback lever:** the live
    `server-run.yml` bridge (~5 s single-file `lake env lean`) speeds *verification* but not the
    *authoring* of this missing theory, so it does not change the scale. Recorded as the precise
    wall; the `#E[n]=n²` structure is already landed for `n ∈ {2,3,4,5,7}` without it.
    - **Substrate progress against step (i), and where the wall now sits (2026-07-18).** Two
      curve-generic substrate bricks landed: the coordinate-ring translation `φₙ·ΨSqₙ = Φₙ·ψₙ²`
      (`MultiplicationXCoordinateRing.lean`) and the doubling divisibility `ψₙ ∣ ψ₂ₙ`
      (`DivisionPolynomialDoubling.lean`, the explicit `ψ₂ₙ/ψₙ = complEDS₂ …`) — the latter is
      exactly the "as a start" prerequisite Mathlib's own `ω`-`TODO` names. With it, the remaining
      obstruction to *defining* `ωₙ := (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ+a₃ψₙ²))/2` is pinned to the single
      `÷2` well-definedness: `2 ∣ (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ+a₃ψₙ²))` in `R[X][Y]`. **This obstruction is
      genuine only in characteristic `2`** — where `2` is invertible (any char `≠ 2` field, so in
      particular secp256k1's `𝔽_p`) it is vacuous and `ωₙ` is immediately definable. In *full*
      generality it needs the char-`0` universal ring `ℤ[A₁..A₆][X][Y]` + specialization morphism,
      which **Mathlib does not provide** (no `WeierstrassCurve.Universal`; verified against the
      pinned tree). But even a defined `ωₙ` proves nothing until step (iii): there is still **no
      `Point`↔`ω/ψ` connection**, so `ωₙ` would be a bare polynomial with no `y([n]P)` meaning. The
      true wall is thus unchanged — step (iii), the coordinate `[n]`-map induction — and it does not
      shrink by defining `ωₙ` alone. No thin `ωₙ`-definition brick is minted for that reason.
    - **The wall reduced and its reduction machine-checked (2026-07-19).** Two moves collapse the
      scale estimate above. **(a) ω-free reformulation** sidesteps step (i) entirely: the `y`-conjunct
      is stated with only Mathlib's `ψ`, as `Y·(4y)·ψₙ³ = ψ(n+2)ψ(n-1)² − ψ(n-2)ψ(n+1)²` (the identity
      `4y·ωₙ = …`), so **no `ωₙ` object, no `÷2` obstruction, no universal ring** is needed — the
      anchors at `n=2,3` are landed (`OmegaRecurrenceAnchors.lean`) and the general relation is the
      `r=2` case of the landed `ψ_isEllSequence`. **(b) The full induction skeleton now elaborates in
      the Lean kernel.** `Ecdlp/Targets/n7_uniform_carrier_induction.lean` carries the joint `(x,y)`
      predicate `Carrier` through `WeierstrassCurve.normEDSRec'`; the base leaves `n=0,1,2`, the `n=4`
      x-conjunct, the entire **`Point`-group plumbing** (`even_step_group`/`odd_step_group`: `add_nsmul`
      decomposition, degenerate-branch handling via `some_ne_zero`/`add_self_of_Y_eq`, tangent/secant
      slope reconstruction, `some.injEq`), and the `normEDSRec'` capstone `secp256k1_nsmul_coords` are
      **`sorry`-free and server-verified** (`lake env lean` → `LEAN_OK`, only the named-wall `sorry`
      warnings). So step (iii) is no longer a "single monstrous identity" but a *machine-checked
      reduction* of the whole uniform target to a short list of **named** standalone lemmas. The
      residual wall is now precisely: `even_x_algebra`/`odd_x_algebra` (the per-step x-identity — the
      point-transport of the already-proved curve-generic `φ_ψ_diff`), `even_y_algebra`/`odd_y_algebra`
      (the ω-free y-step), the non-degeneracy bridge `nsmul_eq_zero_iff_psi_evalEval_zero` /
      `psiSq_ne_zero_of_nsmul_some`, and the mechanical leaves `carrier_three` / `carrier_four`-y.
      Crucially the x-walls are **not** the previously-feared missing `Point↔ω/ψ` map: the eval bridge
      `eval_ΨSq_eq_normEDS_sq` / `eval_Φ_eq_normEDS` (`DivisionPolynomialEvalBridge.lean`) already
      transports `ΨSqₙ.eval x`, `Φₙ.eval x` to the scalar `wₙ = ψₙ.evalEval x y`, turning each x-wall
      into a scalar field identity provable from `φ_ψ_diff` — attackable, not upstream-grade. Held on
      branch `claude/admiring-darwin-uouep1` (open stem, `sorry`s, excluded from the gate).
    - **Wall-crack pass + honest correction (2026-07-19).** `carrier_three` (the `n=3` base leaf,
      both conjuncts) is now server-verified `sorry`-free — base leaves `n=0,1,2,3` and the `n=4`
      x-conjunct are done. `even_x_algebra` reduces to two univariate division-polynomial
      *doubling* identities (`ΨSq(2k)=4B(A³+7B³)`, `Φ(2k)=A⁴−56AB³` with `A=Φ(k),B=ΨSq(k)`) — both
      **true** (reproducibly CAS-certified `k=1..8`, degrees to 255/256, in
      `scripts/certs/division_doubling_secp.py` → `CERT_OK`), but a deeper audit found they are
      **not a finite certificate**:
      substituting `normEDS_even/odd`+Somos-4 leaves a remainder in `w(k±2)²` whose pinning cascades
      outward unboundedly, so closing them needs a **strong induction on `k`** over the elliptic net
      (the `NormEDSSomos4.lean` technique, ~200 lines) — a real EDS sub-development, not a `ring` fill.
      **Reduction fully mapped + CAS-validated (2026-07-19, ultracode `n7-even-x-doubling`).** `even_x`
      now reduces to two curve-generic scalar cores over `w=normEDS β c d` — CORE-I
      `(w(k−1)²w(k+2)−w(k−2)w(k+1)²)² = 4β²(A³+7B³)` and CORE-II
      `w(2k+1)w(2k−1) = 3A⁴+4PA³+84AB³+28PB³` — each provable by `WeierstrassCurve.normEDSRec'` with the
      *same seven-case skeleton and index window as the landed `normEDS_somos4`*. Both cores + both
      targets + all 10 base cases (in the curve ideal, remainder 0) are CAS-validated end-to-end
      (`scripts/certs/core_check.py`, 804 tests True; full plan in `notes/N7_EVEN_X_REDUCTION.md`). The
      residual is now purely mechanical: 4 `linear_combination` step certificates (coreI/coreII ×
      even/odd) whose ~20–40-term cofactor bundles must be machine-generated (sympy Groebner/linear-solve)
      and kernel-judged, exactly like `somos4_odd_step`/`somos4_even_step_scaled`. No mathematical unknown
      remains; the closure is a multi-cycle CAS+kernel effort (heavier than the original `NormEDSSomos4`),
      bottlenecked without a local Lean toolchain to iterate the induction assembly.
      **Correction to the "clean reduction" above:** an
      adversarial audit found that three of the abstracted step-lemmas — `odd_x_algebra`,
      `even_y_algebra`, `odd_y_algebra` — are *under-hypothesized* (they leave the `y`-sign of the
      intermediate points free, so the universally-quantified forms are literally false: flipping
      `Yk↦−Yk` realises `(−kP)+(k+1)P=P`). The induction is still sound — every instance the
      `even/odd_step_group` callers use is a genuine consecutive-multiple pair where the identity
      holds — but completing the proof requires these three lemmas *restated* to thread the `Carrier`
      y-coupling through their signatures (or inlined into the step-group), not merely a `sorry` fill.
      So the residual is: (1) the two `even_x` univariate doubling identities, (2) restate+prove the
      three coupled step-identities, (3) the torsion bridge `nsmul_eq_zero_iff_psi_evalEval_zero`
      (the one genuine missing-Mathlib `Point→ψ` direction), (4) the `carrier_four` y-leaf.
    - **`carrier_four`-y sharpened (2026-07-19).** Residual (4) is now down to a single missing
      certificate. The `n=4` ω-anchor is landed and server-verified: `secp256k1_omega_recurrence_four`
      (`OmegaRecurrenceAnchors.lean`) proves `ψ₆ψ₃²−ψ₂ψ₅² = 4y·ω₄` with the degree-24
      `ω₄`, built on the freshly-derived even-index brick `secp256k1_psi6_evalEval`
      (`ψ 6 = 2y·(3x¹⁶+4704x¹³−131712x¹⁰−7639296x⁷−12907776x⁴−103262208x)`, from `ψ_even 3` after
      cancelling the `ψ₂=2y` factor). Both close by `ring` after the evalEval bricks; CAS-validated
      (on-curve `(A,B)` representation) and kernel-checked (no `native_decide`). The carrier's y-coupling
      RHS is thereby discharged; the one remaining piece for the leaf is a `y(4P)=ω₄/ψ₄³` cert (the
      doubling² y-formula, the `n=4` analogue of `DoublingPointFormula`/`MultiplicationYTripleFormula`).
    - **`y(4P)` + `carrier_four` fully landed (2026-07-19, PR #210).** `secp256k1_quadruple_y`
      (`QuadrupleMultiplicationYFormula.lean`) closes the doubling² `y`-cert, and
      `secp256k1_four_nsmul_coords_ωfree` (`NsmulCoordsBaseFour.lean`) closes `carrier_four`
      (both conjuncts). Base leaves `n=0..4` of `normEDSRec'` are now all closed.
    - **Frontier re-scoped after the `n=4` landing (2026-07-19, scout).** With every base leaf and
      anchor closed, the two named residuals — (2) the three under-hypothesized step lemmas and (3)
      the torsion bridge `nsmul_eq_zero_iff_psi_evalEval_zero` — are **not two independent bricks but
      one entangled monolith.** The scout confirmed: (a) the landed per-`n` bridges
      (`secp256k1_{two,three,five,seven}_nsmul_eq_zero_iff`) are **bespoke `n=2+1`-style hand proofs**
      (explicit `P+P+P` expansion + 2-torsion case split reduced to the *specific* `ψₙ` polynomial) that
      do **not** generalize mechanically; (b) our pinned Mathlib `DivisionPolynomial/{Basic,Degree}`
      carries only algebraic `ψ`/`Φ`/`ΨSq` facts — **no `Point ↔ ψ` vanishing lemma** (the `Point→ψ`
      link lives only in the stalled upstream PR #13782); and (c) the uniform bridge is **circular with
      the still-open uniform x-map** `x([n]P)=Φₙ/ΨSqₙ` — proving the bridge needs the x-coordinatisation,
      whose non-degeneracy needs the bridge. **Concrete unblock (single route):** strengthen the stem's
      `Carrier` predicate to also carry `n•P affine ⟺ ψₙ(P) ≠ 0`, proving the x-map, the y-relation, and
      the torsion bridge **jointly** in the one `normEDSRec'` induction (the stem docstring already names
      this). That is a **single multi-cycle refactor of the induction**, not a mergeable single-cycle
      brick; per-`n` formulas beyond `n=4` are ledger inflation and are not to be minted. Alternative:
      port the mul-by-`n`/torsion machinery if upstream PR #13782 lands.
  - **Weil reciprocity `f(div g) = g(div f)` (ladder rung W4-1) — frozen no-go
    (2026-07-18).** The evaluation half of the Weil pairing is landed at the
    function-field level (W3e-1 divisor evaluation, W3e-2 representative-scaling),
    but the reciprocity crux resists an honest cycle: it is a genuine Mathlib gap
    with **no reachable non-vacuous special case**. The landed Weil layer rides on
    Mathlib's `toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing)` (the
    Abel–Jacobi map into the *ideal class group* = divisors mod principal); passing
    to classes forgets exactly the `F*`-valued products `f(div g)`, `g(div f)` that
    reciprocity equates, so `toClass`/`ClassGroup` — necessary for W1/W2 — is
    provably insufficient for W4 and cannot be leveraged into a special case. The
    exact missing Mathlib lemmas (absent at v4.31 **and** on current master, verified
    by code search): (1) a differential residue on a function field and the residue
    theorem `∑_P res_P ω = 0` (Mathlib's only `residue` is `IsLocalRing.residue
    R→R/m`); (2) a tame/local symbol `(f,g)_v` and its product formula `∏_v (f,g)_v =
    1`; (3) a `Divisor` type with `degree`/`deg(div f)=0` and a valuation family over
    **all** closed points including the place at infinity `O` (Mathlib's
    `HeightOneSpectrum` valuations cover only the affine coordinate ring, missing `O`
    — and the target divisors `n·([P]−[O])` mix affine points with `O`). Each of the
    three proof routes (residue theorem; tame-symbol product formula; `x:E→ℙ¹`
    pull-back reducing to `Polynomial.resultant` symmetry via a symbol
    norm-compatibility lemma) needs a new upstream-grade development comparable to the
    Riemann–Roch gap. A concrete `native_decide` instance is also blocked: the repo's
    Miller function is produced non-constructively (`ClassGroup.mk_eq_one_iff`), so
    `divEval f_P` does not reduce to a `ZMod p` computation. **Status:** W4-1/W4-2 and
    all of W5 (`eₙ`, bilinear/alternating/non-degenerate) stay parked behind this; the
    loop routes to the independent rung W3e-3 (support-disjointness packaging), which
    builds only on the landed `evalReg`/`divEval` layer. See `notes/WEIL_LADDER.md`.
- **Point counting** — **closed for secp256k1**: `#E(𝔽_p) = n` is now a kernel
  theorem (`CurveCardinalityExact.lean` — a curve-specific certificate, `n ∣ #E`
  plus `#E ≤ 2p+1 < 3n` plus `E[2] = {O}`, no Hasse/Schoof needed). The general
  Schoof/Hasse machinery is still absent from Mathlib, so other curves (e.g.
  P-256, whose `j ≠ 0` blocks this certificate route) remain open.

**Realized despite the barrier — the transfer *resistance* of secp256k1.** Although
the transfer attacks themselves cannot yet be formalized (no pairing), the
security-relevant boundary facts — that the attacks *cannot help against secp256k1* —
are now machine-checked, sidestepping the missing foundation the same way the
generic bound sidestepped the cost model:
- `secp256k1_embedding_degree_gt_100` (`EmbeddingDegree.lean`) — `p^k ≢ 1 (mod n)`
  for `1 ≤ k ≤ 100`, so the MOV/FR target field `𝔽_{p^k}` is intractably large.
- `secp256k1_trace_ordinary_nonanomalous` (`TraceOfFrobenius.lean`) — trace `t ≠ 0`
  (ordinary, not supersingular), `t ≠ 1` (not anomalous, so Smart/SSSA does not
  apply), and `t² ≤ 4p` (Hasse). With Pohlig–Hellman (`PohligHellman.lean`) and the
  generic `Θ(√n)` bound, **the tractable attack landscape is now saturated**: every
  classical ECDLP attack expressible without a missing Mathlib foundation has a
  verified node, and the rest are precisely the barriers above.

### B4. Informal / meta (~133 claims)
Survey scope, research-gap notes, applicability commentary — no formal statement
to verify. Correctly excluded.

## How to read this for research value
- **Levels 1–2 (the asset):** everything under *Proved* and the rest of *Tractable
  now* — a verified, reusable secp256k1 base and first formalizations.
- **No-go / barrier results:** B1–B3 are publishable in themselves — a formal-methods
  community needs to know exactly which foundations (cost model, lattice reduction,
  Semaev polynomials, Weil pairing) are missing to formalize ECDLP cryptanalysis.
- **Lottery (level 3):** a genuinely new structural / no-go result would come from
  the *Tractable now* zone, not from forcing a barrier.

## Upstream-existence check (machine-assisted, evidence-backed)
An automated multi-agent scan of mathlib4 (master + open PRs + Zulip) — see
`notes/UPSTREAM_SCAN.md` — confirms the barrier map above against the live upstream, and
sharpens it: the **generic scaffolding is already upstream** (Weierstrass group law in three
models, division-polynomial `preΨ`/`ΨSq`/`Φ` infrastructure (but no general
point bridge or bivariate `ωₙ`), rank-1 `normEDS`/`IsEllSequence`, `ZLattice`/Minkowski,
`MvPolynomial`+resultants — all free by import on the pinned v4.31), while the
**cryptographically load-bearing superstructure is a green field**, absent from master, every
surfaced PR, and wider-GitHub Lean search:
- **Weil pairing** `e_n : E[n]×E[n]→μ_n` and the structure theorem `E[n] ≅ (ℤ/n)²` — nothing.
- **Division-polynomial torsion bridge** `ψₙ(P)=0 ⟺ P ∈ E[n]` — the keystone; `ψₙ` is free but
  the link to the point group / mul-by-`n` lives only in stalled PR #13782. **Highest-ROI next port.**
- **Semaev summation polynomials** `S_n` — the dated upstream and surfaced-PR scan recorded in
  `notes/UPSTREAM_SCAN.md` found no other Lean formalization. The `S₃` base case + forward
  direction is formalized **in this repo** (`Ecdlp/Proved/SemaevThree.lean`); absence from that
  bounded scan is not proof of global uniqueness.
- **General multi-index elliptic nets** (rank ≥ 2, subnet functoriality) — only rank-1 exists
  (master + stalled PR #25989).
- **EC isogenies / endomorphisms / Frobenius** as point-group homs — no module.
- **Other standard curves** (P-256, Curve25519/ed25519) + **point counting** — no Montgomery /
  twisted-Edwards model, no Schoof; group orders only assertable.
- **Generic-group cost model** and **lattice reduction (LLL/BKZ, SVP/CVP, HNP)** — no Lean
  formalization anywhere (prior art is Isabelle/HOL only).

The scanner itself is a reusable engine capability (upstream-dedup): before building or
re-deriving, it detects whether a target is already proved upstream — which is how the L4
net-relation proof (PR #13155) was found and ported (`Ecdlp/Proved/NormEDSIsElliptic.lean`).
