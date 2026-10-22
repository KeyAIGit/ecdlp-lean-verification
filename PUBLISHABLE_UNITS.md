# PUBLISHABLE_UNITS.md

Separating the *mathematical-content* units that can stand alone as papers or Mathlib
contributions from the *engine* narrative (strong-model-proposes / kernel-judges). Every
theorem named below is a real, kernel-accepted entry in `VERIFIED.md` with `status = proved`,
`0 sorry`, no custom axioms. Trust caveats (`native_decide` → `Lean.ofReduceBool`) are stated
per unit and catalogued in `TRUST_REPORT.md`. For the live ledger count see `STATUS.md`.

**How to read this.** Units 1–3 are the load-bearing, self-contained publishable results. Each
gives a one-line thesis, the actual theorems proved, honest scope, a target venue, and the single
opening sentence an abstract would use. Section 4 lists further candidate units at lower detail.
Section 5 is the engine story — a *separate methods track*, deliberately not merged with the math
units. Section 6 collects the non-claims that must travel with any of these.

---

## Unit 1 — The generic-group `Ω(√p)` fixed-transcript collision core

**Thesis.** The **fixed-transcript affine collision core** of the Shoup/Nechaev generic-group
lower bound for the discrete log — plus the two matching `√n` arithmetic relations on the
upper side — are now machine-checked in Lean 4 / Mathlib, by isolating the one
information-theoretic counting fact that needs no general oracle cost model. **Honest scope:**
this is *not* the full Shoup theorem (no adaptive adversary, no random encoding/oracle-simulator,
no probability over a random log) and *not* a formal `Θ(√n)` complexity theorem (no executable
algorithm / cost semantics / birthday analysis). It is the reusable combinatorial kernel and the
arithmetic relations those complexity statements rest on.

**What is actually proved** (`Ecdlp/Proved/`, namespace `Ecdlp.GenericGroup`):
- Lower bound: `generic_dlog_query_bound` (`p ≤ q·q`), `generic_dlog_sqrt_bound` (`√p ≤ q`),
  and the quantitative `generic_success_le` (success count `≤ q·q − q + 1`)
  — `GenericGroupBound.lean`.
- The model's soundness lemmas that make the bound meaningful: `eval_add`, `eval_neg`,
  `eval_zero` (a generic algorithm's state is exactly the set of affine forms `a + b·X` it has
  formed over `ZMod p`; group operations correspond to form operations), plus the collision
  counting `collisionSet_card_le_one` and `badSet_card_le` — `GenericGroupBound.lean`.
- Matching upper-side `√n` arithmetic relations (not a formal running-time bound): `bsgs_decomp` and `bsgs_steps_sq_ge` (`n ≤ ⌈√n⌉²`)
  — `BabyStepGiantStep.lean`; `pollard_rho_collision`, `pollard_rho_periodic`
  — `PollardRho.lean`; the collision-solve algebra `collision_modEq`, `collision_zmod`,
  `collision_recovers_log`, `dlog_unique` — `CollisionEquation.lean`.
- secp256k1 corollary: `secp256k1_generic_security` (`2^127 < q` — ≥128-bit generic security),
  from `two_pow_255_lt_secp256k1_n` and `secp256k1_bsgs_steps_le`
  — `Secp256k1GenericSecurity.lean`.

**Honest scope / caveats.**
- The lower bound is a **real theorem but a narrow one**: it bounds only *classical, generic*
  (black-box) algorithms. It says nothing about non-generic attacks that read the point encoding
  — for `𝔽_p^×` index calculus provably beats `Ω(√p)`; for EC over a prime field no such attack
  is known but its non-existence is unproven. It is **classical-only**: Shor solves ECDLP in
  quantum polynomial time.
- The bound is stated over an abstract prime-order group; the generic-algorithm model (state = set
  of affine forms) is the paper's modeling choice and a reviewer's first question — it must be
  presented as the Shoup/Nechaev information-theoretic core, not as a general cost model (Lean still
  has none; see `BARRIERS.md` B1).
- The secp256k1 instantiation uses the base-point subgroup order `n`. That order is now proved:
  `#E(𝔽_p) = n` is machine-checked curve-specifically (`CurveCardinalityExact.lean`, no Schoof) and
  `n` is proved prime (Unit 2), so the once-conditional point-counting part is fully discharged.
- `secp256k1_generic_security` and `secp256k1_bsgs_steps_le` use `native_decide` for the 256-bit
  numeric leaf, so they carry `Lean.ofReduceBool` (compiler in the TCB); the abstract bounds
  (`generic_dlog_query_bound`, `bsgs_decomp`, …) are pure-kernel.

**Target venue.** CPP or ITP (formal-methods primary). The abstract generic bound is a plausible
**Mathlib upstream** contribution on its own.

**Opening sentence.** "We give a machine-checked Lean 4 / Mathlib formalization of the
fixed-transcript affine-collision core of the Shoup–Nechaev generic-group lower bound for the
discrete logarithm, together with the matching `√n` arithmetic relations underlying the
baby-step/giant-step and Pollard-rho upper bounds — the reusable information-theoretic kernel of
the `Θ(√n)` generic complexity, short of the full adaptive-adversary model and a formal cost
semantics."

---

## Unit 2 — Machine-checked Pratt primality certificates for secp256k1 `p` and `n`

**Thesis.** The two security-load-bearing constants of secp256k1 — the field prime
`p = 2²⁵⁶ − 2³² − 977` and the group order `n` — are certified prime by full, kernel-checked
Pratt (Lucas/Pocklington) certificates whose compiler-trusted footprint is deliberately minimized.

**What is actually proved:**
- `Ecdlp.Primality.secp256k1_p_prime` — `Ecdlp/Proved/Secp256k1PrimeP.lean`.
- `Ecdlp.Primality.secp256k1_n_prime` — `Ecdlp/Proved/Secp256k1PrimeN.lean`.
- The corresponding `instance : Fact (Nat.Prime …)`, which discharges the `[Fact …]` hypotheses on
  the curve-grounding and generic-security theorems automatically (so those become effectively
  unconditional).
- Downstream facts that rest on it: `secp256k1_scalar_no_proper_subgroup` (`ℤ/n` has no proper
  nontrivial subgroup — small/invalid-subgroup resistance) and `secp256k1_scalar_num_generators`
  (`#{a | addOrderOf a = n} = n − 1`, i.e. `φ(n)` valid keys) — `ScalarGroupStructure.lean`.

**Honest scope / caveats.**
- These are **kernel-only**. Each is a kernel-checked recursion using Mathlib's
  `lucas_primality`; the arithmetic leaves (each witness exponentiation `a^((p−1)/q) ≠ 1 mod p`
  and each factorization identity `p − 1 = 2^a·(q₁·…)`) are evaluated by the kernel on `Nat`
  (`decide +kernel`, `Ecdlp.Kernel.powMod` in `KernelPowMod.lean`). `#print axioms` shows only
  `propext`, `Classical.choice`, `Quot.sound`; the trusted base is the Lean kernel, including its
  built-in big-number `Nat` arithmetic (`TRUST_REPORT.md` §1). Earlier versions discharged these
  leaves with `native_decide` (`archive/docs/REVIEW_DOSSIER.md` finding 9).
- Scope is exactly these two specific constants. The *method* (Pratt in Lean) is general; the
  *deliverable* is a fully machine-auditable certificate for secp256k1's `p` and `n`.
- Internal recursive Pratt sub-lemmas (~22) are not separate ledger results.

**Target venue.** ITP short paper / verified-artifact track, or a **Mathlib upstream** data
contribution (the certificates as reusable `Fact` instances). Realistically a section or artifact
rather than a standalone full paper — strongest as the reproducibility backbone cited by Unit 1.

**Opening sentence.** "We present kernel-checked Pratt primality certificates in Lean 4 for both
secp256k1 constants — the 256-bit field characteristic and the prime group order — structured so
that native compilation is trusted only for bounded arithmetic leaves inside an otherwise
kernel-verified Lucas–Pocklington recursion."

---

## Unit 3 — The Weil/Semaev foundational ladder (first-in-Lean)

**Thesis.** The two elliptic-curve objects at the heart of ECDLP cryptanalysis that were entirely
absent from Lean — Semaev summation polynomials and the divisor-theoretic foundations of the Weil
pairing — now have their first formalized rungs, presented as a foundation-and-no-go contribution,
explicitly not as an attack on secp256k1.

This unit has two components (distinct objects, common "first-in-Lean foundations" thesis; a single
paper could carry both, or they could split).

### 3a — Semaev summation polynomials `S₃`, `S₄`

**What is actually proved** (namespace `Ecdlp.Semaev`):
- `S₃` forward, both nondegenerate cases: `S₃_eq_zero_of_chord`, `S₃_eq_zero_of_tangent`
  (+ secp256k1 specializations `secp256k1_semaev_three_chord/tangent`) — `SemaevThree.lean`.
- `S₃` on **Mathlib's actual elliptic-curve group law** (hypothesis is the real relation
  `P₁+P₂+P₃ = O`, not a coordinate equation): `secp256k1_semaev_three_point`,
  `secp256k1_semaev_three_point_double` — `SemaevThree.lean`.
- `S₃` reverse + full characterization: `S₃_root_of_eq_zero`, `S₃_eq_zero_iff`,
  `secp256k1_semaev_three_iff` (`S₃ = 0 ⟺ x₃ = x(P₁+P₂) or x(P₁−P₂)`); symmetries
  `S₃_symm₁₂`, `S₃_symm₂₃`.
- `S₃` on Mathlib's group law for every curve in short normal form over a field, without case
  hypotheses: forward `S₃_eq_zero_of_add_add_eq_zero`, the characterization
  `S₃_eq_zero_iff_exists_point` (`S₃(x₁,x₂,x₃) = 0` iff an affine point over `x₃` completes
  `P₁ ± P₂` to `O`), its signed-sum form `S₃_eq_zero_iff_signed_sum`
  (+ `secp256k1_semaev_three_point_iff`), and the identity `S₃_eq_addSubMap` with Mathlib's
  `WeierstrassCurve.addSubMap` — `SemaevThreePoint.lean`. Mathlib PR #43292 (from v4.34.0)
  proves `sym2x_add_sub_eq_addSubMap_sym2x`, which overlaps the characterization.
- `S₄`: definition as `Res_X(S₃(x₁,x₂,X), S₃(x₃,x₄,X))` on Mathlib's `Polynomial.resultant`, both
  directions — forward `S₄_eq_zero_of_common_root` (+ `secp256k1_semaev_four_of_common_root`) and
  reverse/meaning `S₄_common_root_of_eq_zero` (+ `secp256k1_semaev_four_common_root_of_eq_zero`),
  with the slice factorization `S₃poly_master_factor` and the symmetries `S₄_block_swap`,
  `S₄_symm₁₂`, `S₄_symm₃₄` — `SemaevFour.lean`. Those three generate only an order-8 subgroup of
  the 24 permutations (not kernel-checked); invariance under every permutation is `S₄_perm` (with the missing
  transposition `S₄_symm₂₃`) — `SemaevFourSymmetry.lean`.
- `S₄` degree: coefficient of `x₄⁴` equal to `S₃(x₁,x₂,x₃)²` (`S₄slice_coeff_four`), hence degree
  exactly 4 in each variable when `S₃` of the other three is nonzero (`S₄slice_natDegree`,
  `S₄_natDegree_eq_four_of_perm`) and at most 4 completions (`S₄_completions_le_four`)
  — `SemaevFourSymmetry.lean`.
- The forward direction reduces to one lemma, `resultant_eq_zero_of_common_root` (any two
  univariate polys of bounded degree sharing an evaluation-root have vanishing resultant); a Semaev
  step inherits its forward direction as an instance once the previous slice is defined with its
  degree bound. No general `Sₙ` for `n ≥ 5` is defined here.
- Index-calculus meaning + one exact cost ingredient: `secp256k1_point_decomposition_semaev`
  (and `_double`) — every 2-term decomposition lies on the Semaev variety
  — `PointDecomposition.lean`; `secp256k1_S₃poly_natDegree` (degree exactly 2 in each variable) and
  `secp256k1_decomposition_completions_le_two` (≤ 2 completions per factor-base point)
  — `SemaevDegree.lean`.

**Honest scope / caveats.**
- **First Semaev summation polynomial formalized in Lean/Mathlib anywhere** (green-field per the
  upstream scan; zero hits on master, PRs, GitHub-wide).
- This is a **formalization contribution (and an open research direction), not an attack**. Semaev
  index calculus is subexponential over *extension* fields `𝔽_{p^n}, n > 1` (Gaudry–Diem–Semaev, via
  Weil restriction). secp256k1's field is *prime* `𝔽_p`, which affords no Weil restriction, and
  **no known** summation-polynomial method beats generic `Ω(√n)` there — but whether special
  structure could help asymptotically is **open** (cf. Petit, prime-field ECDLP); this is not a
  proven no-go. The
  decomposition collapses to a single high-degree equation as hard as the original. `S₃`/`S₄`
  compute nothing about any specific discrete log on a prime-field curve.
- The prime-field hardness itself is **not** a theorem here — that would settle an open conjecture.
  The proved facts map *where* the search lives and *how it branches*; the cost lower bound stays in
  the open frontier (`BARRIERS.md` B3).
- The degree tower `deg Sₘ = 2^{m−2}`: exact for `m = 3` (`deg S₃ = 2` in its last variable when
  `x₁ ≠ x₂`, proved for secp256k1) and `m = 4` (`deg S₄ = 4` when `S₃` of the other three
  arguments is nonzero). `Sₘ` for `m ≥ 5` is not defined here at
  general `(a,b)` (a recursive definition with the upper bound `deg ≤ 2^{m−2}` is in draft
  PR #448 (parked)), and no point-level `S₄` characterization (`S₄ = 0 ⟺ ±P₁±P₂±P₃±P₄ = O`) is built.

### 3b — Weil-pairing divisor foundations `W1–W3`

**What is actually proved** (namespace `Ecdlp.Weil`):
- W1 — torsion ⟺ principal divisor: `secp256k1_torsion_iff_principal` (`n•P = 0 ⟺ n·([P]−[O])`
  principal), via Mathlib's Abel–Jacobi map `toClass` — `WeilDivisorClass.lean`.
- W2 — the Miller function exists: `secp256k1_miller_function_exists` (a generator `f_P` of the
  principal ideal `(XYIdeal' h)ⁿ`) — `WeilDivisorClass.lean`.
- W3 (representative-independence half) — `secp256k1_miller_function_unique` (two Miller functions
  differ by a unit of the coordinate ring) — `WeilDivisorClass.lean`.
- The function-evaluation layer Mathlib lacks, built here: `evalAt` with `evalAt_surjective`,
  `evalAt_ker` (regular-function evaluation `F[E] →+* F`) and `xyIdeal_isMaximal`
  — `PointEvaluation.lean`; the localization extension `evalRatAt_algebraMap`
  — `EvalRatAtCompat.lean`; divisor-support separation `xyIdeal_ne_of_x_ne`, `xyIdeal_ne_of_ne`
  (+ `xyIdeal_ne_of_y_ne`) — `PointSeparation.lean`; the vanishing/nonvanishing criteria
  `evalRatAt_eq_zero_iff`, `evalRatAt_ne_zero_iff_isUnit` — `EvalRatAtNonvanishing.lean`.
- The abstract-function and divisor-evaluation completion: `evalFracAt`, quotient extraction,
  `RegularAt`/`evalReg`, `divEval_mul`, Miller-representative scaling, and
  `secp256k1_miller_jointly_regular`/`divEval_one` — `FunctionField{Eval,Repr,Regular}.lean`
  and `Weil{DivisorEval,DivisorRepIndep,MillerEval}.lean`. This closes the reachable W3
  evaluation scaffolding.
- The bridge welding the division-polynomial tower to the divisor class:
  `secp256k1_psi3_root_iff_class_torsion` (+ `_psi5_`, `_psi7_`) — `ψₙ(P)=0 ⟺ n•toClass P = 0`
  — `MillerDivisionPolynomialBridge.lean`.

**Honest scope / caveats.**
- These are **foundational rungs toward the Weil pairing, not the pairing**. The heavy substrate
  (Abel–Jacobi `toClass`, `FunctionField`, `μₙ`) is *already in Mathlib*; W1/W2 are applications of
  it. The genuinely new-to-Lean machinery is the point-evaluation layer (`evalAt` and its
  localization/separation/nonvanishing lemmas) and the `ψₙ ↔ class-torsion` bridge.
- The pairing `eₙ : E[n] × E[n] → μₙ` is **not** defined, and bilinear/alternating/non-degenerate
  are **not** proved. What remains open and hard is Weil reciprocity
  `f(div g) = g(div f)` (W4), then the root-of-unity/bilinearity/non-degeneracy assembly (W5).
  The raw W3 evaluation domain and algebra are present; they are not the pairing.
- `secp256k1_miller_function_unique` was **designed by the strong model and kernel-verified**
  — an engine-track provenance note, not a mathematical claim; the result stands on the kernel.
- Everything is stated for secp256k1, though much of the evaluation layer is curve-agnostic
  (proved for any Weierstrass curve over a field).

**Target venue (whole Unit 3).** ITP, and **Mathlib upstream** for the reusable pieces (Semaev
polynomials, `evalAt`/point-evaluation layer — both flagged in the upstream scan as absent). The
strong-model-designed rung is an AITP data point but belongs to the engine track (Section 5), not
the math thesis.

**Opening sentence.** "We report the first formalizations in Lean 4 / Mathlib of Semaev's third and
fourth summation polynomials — with both directions of the `S₃` characterization and of the `S₄`
resultant recursion — and of the divisor-class foundations underlying the Weil pairing on
secp256k1, framed as a formal map of what elliptic-curve cryptanalysis over a prime field can and
cannot yet express inside a proof assistant."

---

## Section 4 — Further candidate units (lower detail)

These are coherent enough to publish but are secondary to Units 1–3.

- **The `ψₙ ⟺ E[n]` torsion-bridge ladder + point-cardinality bounds.** Full both-direction bridges
  `secp256k1_{two,three,five,seven}_nsmul_eq_zero_iff`, the exact-order classifier
  `secp256k1_smallprime_addOrderOf`, and genuine *point* counts `#E[n] ≤ n²`
  (`secp256k1_{three,five,seven}_torsion_card_le`, tight `secp256k1_two_torsion_ncard_le ≤ 4`) via a
  ≤2-to-1 fiber argument that dodges point counting. Caveat: `n`-specific (no general-`n` bridge —
  that is the open rung-4 gap, `notes/FOUNDATIONS.md`). Venue: ITP.
- **Division-polynomial coprimality family (one family unit — NOT one result per pair).**
  Explicit 𝔽_p Bézout certificates `IsCoprime ψ_m ψ_n` for the low prime/prime-power pairs
  `{2⊥3, 3⊥4, 2⊥4, 3⊥5, 2⊥5, 3⊥7}` (`Ecdlp/Proved/CoprimePsi*.lean`), each certifying that the
  affine `m`- and `n`-division-polynomial `x`-loci are disjoint — i.e. **no nonidentity point is
  annihilated by both `m` and `n`**. *Honest classification (per external review):* these are
  **computed certificates**, not novel mathematics — each is a cheap `native_decide`/CAS instance of
  the one-line group fact (`gcd(m,n)=1`, Bézout `am+bn=1` ⇒ `[m]P=[n]P=O ⟹ P=O`); the *general*
  statement `IsCoprime ψ_m ψ_n` for all coprime `m,n` is the right unit but needs the
  `ψ_n(x)=0 ⟺ x∈E[n]` torsion↔root bridge (a missing Mathlib keystone) plus separability. The
  genuinely reusable output is not the matrix but **(i)** the first explicit-form theorems for the
  5- and 7-division polynomials `secp256k1_preΨ₅`/`preΨ₇` (via Mathlib `preΨ'_odd`), and **(ii)** the
  observation that each resultant's prime support equals the curve's bad-reduction primes `{2,3,7}`.
  **Do not headline-count each pair.** Value: substrate/regression fixtures + a division-polynomial
  library contribution; novelty low, ECDLP impact none. Venue: at most an artifact/Mathlib PR, not a
  standalone paper.
- **The GLV/CM endomorphism, homomorphism half + no-go.** `glvPoint_add`/`glvHom` (additive
  endomorphism), `secp256k1_glv_cube_relation`/`glvHom_minpoly` (`φ²+φ+1=0`),
  `secp256k1_glvHom_ne_id` (primitive cube root ⇒ genuine CM by `ℤ[ζ₃]`), and the no-go
  `secp256k1_glv_preserves_dlog`/`secp256k1_glv_single_scalar` (CM gives no asymptotic ECDLP
  advantage). **Now proved on the rational points:** `glvPoint = [λ]` with the concrete λ holds on all
  of `⟨G⟩ = E(𝔽_p)` unconditionally (`secp256k1_glvPoint_eq_lam_on_zmultiples` + `grp_eq_top`), plus
  `glvHom = [k]` on the whole group (`secp256k1_glvHom_eq_zsmul`); only the *geometric* `E[n](F̄_p)`
  eigenvalue identity stays open. Venue: ITP.
- **Transfer-resistance saturation.** `secp256k1_embedding_degree_gt_100` (anti-MOV/FR),
  `secp256k1_trace_ordinary_nonanomalous` (anti-Smart/SSSA, non-supersingular, Hasse),
  `anomalous_iff_trace_one`, Pohlig–Hellman (`projection`/`component`/`reconstruct`). Thesis: every
  classical ECDLP attack expressible without a missing Mathlib foundation has a verified
  *resistance* node. Caveats: the attack *mechanisms* are not formalized (no pairing); several rely
  on `native_decide`. Venue: CPP/ITP.
- **Multi-curve Mathlib grounding.** secp256k1 / P-256 / Curve25519 as Mathlib `EllipticCurve`s
  (incl. a Montgomery model), with structural contrasts (`j=0` CM vs `c₄≠0`). Venue: ITP short /
  artifact.
- **The barrier map itself** (`BARRIERS.md`): a position/survey paper on exactly which foundations
  (cost model, lattice reduction, Semaev, Weil pairing) formal ECDLP cryptanalysis still lacks.
  Venue: a formal-methods survey or AITP.

---

## Section 5 — The engine story (separate track — NOT a math-content unit)

`docs/ENGINE_PORTFOLIO.md` records a *methods* result: a strong model proposes short-but-hard
answers and an independent verifier (a fresh sympy run, or the Lean kernel) judges — "8/8 hard
problems solved under independent verification," and one kernel-promoted rung
(`secp256k1_miller_function_unique`) whose *proof* was model-designed. This is a genuine narrative,
but it is a **systems / automated-reasoning** contribution, not a mathematical one, and it must not
be conflated with Units 1–3:

- The 8/8 challenge answers (mult-by-`n` `x`-coordinate maps, `ψ₅`/`ψ₇`, the `E[2]⊥E[3]` /
  `E[5]⊥E[7]` disjointness certificates) are **sympy-verified, not kernel-verified** — offline CAS
  certificates, candidates for promotion, not yet Lean theorems (except where separately landed).
- The publishable math claim for any promoted result is carried by the **kernel**, independent of
  who or what designed the proof. Provenance ("model-designed") is a footnote, not a theorem.
- Venue for the engine story: **AITP** or a systems/ML-for-math venue — as a paper about the
  propose-and-verify loop, kept distinct from the Lean-content papers so that neither overclaims on
  behalf of the other.

---

## Section 6 — Global honest non-claims (must travel with any unit)

- **"0 axioms" means no axioms beyond `{propext, Classical.choice, Quot.sound}`** — not axiom-free
  foundations. Machine-enforced by the axiom-audit gate on a headline set (not the whole ledger).
- **Some concrete large-integer facts use `native_decide`** and therefore trust the Lean compiler
  via `Lean.ofReduceBool` (TCB beyond the kernel); `TRUST_REPORT.md` §2(b)/(c) is the disclosure.
  The two primality theorems (Unit 2) and the secp256k1 group-structure chain (`#E = n`,
  `E(𝔽_p) ≃+ ℤ/n`, the GLV `[λ]` corollaries) do not: their 256-bit arithmetic is evaluated by
  the kernel (`decide +kernel`).
- **`#E(𝔽_p) = n` is proved** (curve-specifically, no Schoof — `CurveCardinalityExact.lean`: `#E≤2p+1<3n`
  plus `E[2]={O}`), so secp256k1 cofactor 1 is unconditional. Still open: the **geometric** torsion
  structure `E[n](F̄_p) ≅ (ℤ/n)²` (a distinct object from the rational `#E=n`), and general Hasse/Schoof.
- **`glvPoint = [λ]` is proved on the rational points `⟨G⟩ = E(𝔽_p)`** (concrete λ, unconditional);
  only the full *geometric* `E[n](F̄_p)` eigenvalue identity remains conditional on `E[n] ≅ (ℤ/n)²`.
- **The discrete-log protocol algebra** (Schnorr/EdDSA, DH, ElGamal, Pedersen, Okamoto,
  Chaum–Pedersen, MuSig2/Taproot, Feldman VSS, adaptor/blind Schnorr, ECDSA nonce-reuse) is proved
  over an **abstract `[Module (ZMod n) G]`** and now **also instantiated at the concrete secp256k1
  point group `⟨G⟩`** (`ProtocolInstantiation.lean`), still with **no adversary/hash/probability model**
  (`ABSTRACT_SCOPE.md`). These are sound Lean theorems but
  narrower than their cryptographic prose — they are not part of Units 1–3 and should not be marketed
  as "verified protocol security."
- **The Weil pairing and Semaev index calculus are foundations/no-go, not attacks.** No result here
  breaks, or claims to break, secp256k1.
