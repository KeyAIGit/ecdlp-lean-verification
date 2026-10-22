# TRUST_REPORT.md — trust-boundary report for the ECDLP Lean layer

> Counts here are a snapshot; the single canonical figure is **`STATUS.md`** (generated from `data/stats.json`). If they differ, STATUS.md wins.

**Scope of the verified body.** `325 ledger rows / ~283 distinct kernel-verified
results`. A row may group several supporting declarations; the exact expansion is
generated in `data/result_registry.json`. The built surface has **0 `sorry`, 0
`admit`, and 0 custom axioms**. Open target stems are explicitly outside the built
surface and are counted in `repo/FORMAL_SUBSTRATE.json`.

This document states *precisely* what "verified" rests on, which results extend the
trusted computing base (TCB) via the Lean compiler, and what CI actually enforces
versus merely documents. It is the catalogue referenced by the axiom-audit note in
`VERIFIED.md` and by the generated `Ecdlp/LedgerAxiomAudit.lean`.

---

## 1. Trusted computing base

A "verified" result in this repo is a Lean 4 / Mathlib theorem that the Lean **kernel**
accepts. The kernel is a small, fixed type-checker; trusting a proof means trusting:

1. **The Lean 4 kernel** — the type-checker that re-validates every proof term. This is
   the primary judge of correctness.

2. **The three standard Lean/Mathlib axioms** that essentially every Mathlib proof
   depends on:
   - `propext` (propositional extensionality),
   - `Classical.choice` (the axiom of choice),
   - `Quot.sound` (soundness of quotient types).

   When this repo says "**0 axioms**" / "no custom axioms," it means **no axioms beyond
   these three** (and no `sorryAx`). It does *not* mean the empty axiom set. No result
   introduces a project-specific or `sorry`-derived axiom.

3. **For `native_decide` results only — the Lean COMPILER**, surfaced as the axiom
   `Lean.ofReduceBool`. `native_decide` does **not** discharge a goal by kernel
   reduction. Instead it compiles a `Decidable` instance to native code, runs it, and
   asks the kernel to *trust* that the compiled program returned `true`. That trust is
   recorded as a dependency on `Lean.ofReduceBool`. This is a **real extension of the
   TCB**: it adds the Lean compiler, its code generator, and the runtime to the set of
   things that must be correct. A miscompilation could in principle admit a false
   `native_decide` goal that the kernel would never accept under pure reduction.

   This is the single caveat to CLAUDE.md's "the Lean kernel is the only judge of
   correctness": for the `native_decide` rows, the compiler is *also* a judge. The
   axiom audit (Section 3) makes this dependency explicit rather than hidden.

Nothing in the repo depends on `sorryAx`, `Lean.trustCompiler`, or `Lean.guardMsgsAx`;
these are on the audit's permanent forbidden list.

---

## 2. Method classification of the verified results

Every result falls into exactly one of three buckets. The partition is by whether the
result's proof term depends on `Lean.ofReduceBool` (i.e. uses `native_decide` anywhere,
directly or transitively). The kernel `decide` tactic is also used, for a handful of
small finite checks (e.g. `¬ (p ∣ m)` for tiny `m`, and `Fin`/`ZMod` residue facts);
unlike `native_decide`, `decide` is **kernel-checked** — it emits a proof term the kernel
re-validates — so those results stay in bucket (a) and add **nothing** to the TCB. Only
`native_decide` (the compiler path) extends it, and those facts are catalogued in (b).

### (a) Pure Mathlib / kernel — NO `native_decide` (kernel-only TCB)

These rest only on the kernel + `{propext, Classical.choice, Quot.sound}`. This is the
large majority of the ledger: the entire abstract discrete-log protocol algebra, the
generic-group combinatorial core, the torsion/division-polynomial algebra, and the
ring-identity curve invariants. Representative theorems (file → theorem):

- `Ecdlp/Proved/GenericGroupBound.lean` → `generic_dlog_query_bound`,
  `generic_dlog_sqrt_bound`, `generic_success_le`, `collisionSet_card_le_one`,
  `badSet_card_le`, `eval_add`, `eval_neg`, `eval_zero`
- `Ecdlp/Proved/BabyStepGiantStep.lean` → `bsgs_decomp`, `bsgs_steps_sq_ge`
- `Ecdlp/Proved/PollardRho.lean` → `pollard_rho_collision`, `pollard_rho_periodic`
- `Ecdlp/Proved/CollisionEquation.lean` → `collision_modEq`, `collision_zmod`,
  `collision_recovers_log`, `dlog_unique`
- `Ecdlp/Proved/SchnorrSoundness.lean` → `schnorr_extract`, `schnorr_witness_unique`,
  `pedersen_binding_extract`, `secp256k1_schnorr_extract`, `adaptor_extract`,
  `blind_unblind`
- `Ecdlp/Proved/DlogCompleteness.lean` → `schnorr_verify`, `dh_agree`,
  `threshold_schnorr_aggregate`, `feldman_vss_verify`, `musig_key_aggregate`,
  `threshold_elgamal_combine`, `schnorr_batch_verify`, `adaptor_complete`,
  `taproot_tweak_verify`
- `Ecdlp/Proved/DlogPrimitives.lean` → `elgamal_decrypt`, `pedersen_homomorphic`,
  `elgamal_rerandomize_decrypt`, `elgamal_additively_homomorphic`,
  `pedersen_vector_homomorphic`
- `Ecdlp/Proved/DlogAdvanced.lean` → `okamoto_extract`, `chaum_pedersen_verify`
- `Ecdlp/Proved/PohligHellman.lean` → `projection`, `component`, `reconstruct`
- `Ecdlp/Proved/Torsion.lean` + `CurveTorsion.lean` → `mem_torsionBy_iff_addOrderOf_dvd`,
  `torsionBy_dvd_le`, `zmod_module_nsmul_eq_zero`, `torsionBy_eq_top`,
  `torsionBy_eq_ker_nsmul`, `zmultiples_le_torsionBy`, and the `secp256k1_*` curve-named
  copies, `secp256k1_G_ne_zero`
- `Ecdlp/Proved/DivisionPolynomial.lean` → `secp256k1_b₂`, `secp256k1_b₄`,
  `secp256k1_b₆`, `secp256k1_b₈`, `secp256k1_Ψ₂Sq`, `secp256k1_Ψ₃`
- `Ecdlp/Proved/TwoTorsion.lean` / `ThreeTorsion.lean` / `FourDivisionPolynomial.lean`
  (ring-identity parts) → `secp256k1_Ψ₂Sq_root_of_two_torsion`, `secp256k1_Ψ₃_ne_zero`,
  `secp256k1_three_torsion_x_card_le`, `secp256k1_Ψ₂Sq_ne_zero`,
  `secp256k1_two_torsion_x_card_le`, `secp256k1_preΨ₄`, `secp256k1_preΨ₄_ne_zero`
- `Ecdlp/Proved/Invariants.lean` → `secp256k1_c₆`, `secp256k1_c_relation`
- `Ecdlp/Proved/Secp256k1Curve.lean` → `secp256k1_c₄_eq_zero`, `secp256k1_j_eq_zero`
- `Ecdlp/Proved/AnomalousScope.lean` → `anomalous_iff_trace_one`
- `Ecdlp/Proved/CubeRoot.lean` → `cube_root_of_eigenvalue`, `orderOf_eigenvalue_eq_three`
- `Ecdlp/Proved/Cofactor.lean`, `PrimeOrder.lean`, `Lagrange.lean`,
  `Statements.lean` → `cofactor_card_mul_index`, `orderOf_eq_card_of_prime`,
  `order_dvd_card`, `glv_eigenvalue_zmod`
- `Ecdlp/Proved/GlvSlope.lean`, `GlvSlopeTangent.lean`, `GlvSlopeAll.lean`,
  `GlvAddFormula.lean`, `GlvHom.lean` → `secp256k1_glv_slope_of_X_ne`,
  `secp256k1_glv_slope_of_Y_ne`, `secp256k1_glv_slope`, `secp256k1_glv_addX`,
  `secp256k1_glv_addY`, **`glvPoint_add`** / **`glvHom`**
- `Ecdlp/Proved/FrozenProjectiveGuardSystem.lean` →
  `guardedEquation_totalDegree_le_four`,
  `frozenProjectiveChain_iff_guardedProjectiveSystem`,
  `frozenRecS17_iff_guardedProjectiveSystem_over` (the literal finite
  polynomial-family equivalence and degree upper bound are standard
  kernel/Mathlib proofs)
- `Ecdlp/Proved/FrozenProjectiveChartSystem.lean` →
  `card_chartVar`, `frozenProjectiveChain_iff_chartPolynomialCover`,
  `frozenGuardedProjectiveSystem_iff_chartPolynomialCover`,
  `frozenRecS17_iff_chartPolynomialCover_over`, and the base/step/final and
  uniform chart-polynomial degree upper bounds (the exact chart-cover
  equivalences, variable-count formula, and degree ceilings are standard
  kernel/Mathlib proofs)
- `Ecdlp/Proved/FrozenProjectiveInfinityStrata.lean` →
  `HValue_third_infinity`, `HValue_first_infinity`,
  `HValue_middle_infinity`, `HValue_first_third_infinity`,
  `frozenChartSystem_separatedInfinityMask`, the endpoint and forced-neighbor
  theorems, and the admissible/interior cover equivalences (the identities,
  necessary-mask results, and exact cover restrictions are standard
  kernel/Mathlib proofs)
- `Ecdlp/Proved/FrozenProjectiveInfinityPropagation.lean` →
  `frozenChartSystem_gapTwoInfinity_forces_det_zero`,
  `frozenChartSystem_gapThreeInfinity_forces_HValue_zero`, the two
  boundary-near propagation theorems,
  `specializeOver_frozenC_eq_zero_of_projectiveChain`, the prefix/suffix and
  empty-mask theorems, the conditional single-affine-chart equivalences, and
  `frozenRecS17_iff_affineChartPolynomialCover_over_of_balancedPropagatedRegular`
  (the local implications and the one-way resultant propagation hold over any
  field; the final source bridge reuses the injective algebraically closed
  target assumption; none of these structural results uses `native_decide`)
- `Ecdlp/Proved/PrimeOrderCardinality.lean` → `natCard_point_eq_of_addOrderOf`,
  `card_eq_of_prime_order_point`, `natCard_point_le`, `exists_cubic_root_of_two_nsmul_eq_zero`,
  `natCard_eq_of_dvd_of_lt_three_mul` (curve-generic exact count; no `native_decide`)
- `Ecdlp/Proved/CubicNoRootCertificate.lean` → `noRoot_of_cert` (adapted from
  pyca/verified-garbage), `natCard_point_eq_of_noRoot`, and for nine standard curves
  `cubic_ne_zero`, `two_mul_add_one_lt_three_mul`, `card_eq_of_addOrderOf` (upstream-derived;
  see the ported table in `VERIFIED.md`). The 192- to 521-bit certificate checks use
  `decide +kernel`: they are checked by kernel reduction, including the kernel's built-in
  GMP-backed `Nat` arithmetic (part of the standard kernel); no compiler trust.
- `Ecdlp/Proved/ParityFourier/*.lean` → `carrySum`, `carrySign`, `jEven`,
  `gOdd`, `gInvariant`, `jOrbitProduct`, `jBalance`, `relabel`,
  `halvingRecovers`, `groupHalvingRecovers`, `sigmaHatClosedForm`,
  `sigmaTail`, `l1lowBound`, `jConcentration`, `jConcentrationExplicit`,
  `normLemma`, `zeroNotInGammaJ`, `jBalanceBound`, `weilTransfer`,
  `weilTransferLsb` (finite Fourier analysis on `ZMod n` and halving with an
  exact parity oracle; each prints a subset of
  `{propext, Classical.choice, Quot.sound}`; `weilTransfer` and
  `weilTransferLsb` take the twisted-sum bound as a hypothesis, and the
  halving theorems take an exact parity oracle as a hypothesis)
- `Ecdlp/Proved/SemaevFourSymmetry.lean` → `S₄_perm`, `S₄_symm₂₃`,
  `resultant_quadratic_two_two`, `S₄slice_coeff_four`, `S₄slice_natDegree`,
  `S₄_natDegree_eq_four_of_perm`, `S₄_completions_le_four` (polynomial identities,
  resultant and degree bookkeeping over any commutative ring, except the three
  exact-degree/completion statements `S₄slice_natDegree`, `S₄_natDegree_eq_four_of_perm`
  and `S₄_completions_le_four`, which are over a field; no `native_decide`)

### (b) `native_decide` / compiler-trusted — TCB INCLUDES the Lean compiler

These depend on `Lean.ofReduceBool`. The proof's truth rests on the compiler in
addition to the kernel. These are the concrete 256-bit / large-integer facts that no
kernel reduction could feasibly check. Exact `file:line → theorem`:

- `Ecdlp/Secp256k1Verified.lean:8`  → `Secp256k1.p_special_form` (`p = 2²⁵⁶−2³²−977`)
- `Ecdlp/Secp256k1Verified.lean:10` → `Secp256k1.glv_lambda_eigenvalue`
- `Ecdlp/Secp256k1Verified.lean:12` → `Secp256k1.lambda_is_cube_root`
- `Ecdlp/Secp256k1Verified.lean:14` → `Secp256k1.lambda_ne_one`
- `Ecdlp/Secp256k1Verified.lean:16` → `Secp256k1.beta_field_eigenvalue`
- `Ecdlp/Secp256k1Verified.lean:18` → `Secp256k1.beta_is_cube_root`
- `Ecdlp/Secp256k1Verified.lean:20` → `Secp256k1.lam_lt_n`
- `Ecdlp/Secp256k1Verified.lean:21` → `Secp256k1.beta_lt_p`
- `Ecdlp/Secp256k1Verified.lean:29` → `Secp256k1.generator_on_curve` (`Gy²≡Gx³+7 mod p`)
- `Ecdlp/Proved/Secp256k1Params.lean:8`  → `p_mod_four` (`p ≡ 3 mod 4`)
- `Ecdlp/Proved/Secp256k1Params.lean:11` → `three_dvd_p_sub_one`
- `Ecdlp/Proved/Secp256k1Params.lean:15` → `three_dvd_n_sub_one`
- `Ecdlp/Proved/Secp256k1Curve.lean:27`  → `secp256k1_Δ_ne_zero`
- `Ecdlp/Proved/Invariants.lean:28`      → `secp256k1_c₆_ne_zero`
- `Ecdlp/Proved/EmbeddingDegree.lean:32/34` → `secp256k1_embedding_degree_gt_100`
  (`pᵏ ≢ 1 mod n` for `1≤k≤100`; MOV/FR resistance)
- `Ecdlp/Proved/TraceOfFrobenius.lean:33/37` → `secp256k1_trace_ordinary_nonanomalous`
  (`t≠0`, `t≠1`, `t²≤4p`; Smart/SSSA + supersingular resistance)
- `Ecdlp/Proved/Secp256k1GenericSecurity.lean:21` → `two_pow_255_lt_secp256k1_n`
  (`2²⁵⁵ < n`)
- `Ecdlp/Proved/FrozenProjectiveGuardSystem.lean:52,56` →
  `card_guardVar_fourteen`, `card_guarded_equations_fourteen` (the raw counts
  56 and 29 only; these two facts use `native_decide`, while the guarded-system
  equivalence and degree-bound theorems do not)
- `Ecdlp/Proved/FrozenProjectiveChartSystem.lean` →
  `card_chartEquation` (the fixed-mask count of fifteen equations only;
  `card_chartVar`, the chart-cover equivalences, and all degree-bound theorems
  do not use `native_decide`)
- `Ecdlp/Proved/FrozenProjectiveInfinityStrata.lean` →
  `card_infinityMask`, `card_separatedInfinityMask`,
  `card_interiorSeparatedInfinityMask` (the exact logical mask counts 16384,
  987, and 377 only; the infinity identities, necessity and forced-neighbor
  results, and cover equivalences do not use `native_decide`)
- `Ecdlp/Proved/FrozenProjectiveInfinityPropagation.lean` →
  `card_gapTwoInteriorInfinityMask`,
  `card_gapThreeInteriorInfinityMask`,
  `card_boundaryPropagatedInfinityMask`,
  `card_boundaryGapThreeInfinityMask` (the exact logical candidate-mask counts
  129, 69, 60, and 36 only; the local propagation, base-field one-way
  resultant argument, balanced obstruction, empty-mask, and affine-cover
  theorems do not use `native_decide`)

### (c) Mathlib + `native_decide` MIX — kernel proof skeleton, compiler-checked leaves

Here the *argument* is a kernel-checked Mathlib proof, but one or more small numeric
side-conditions inside it are discharged by `native_decide` (so the result still
depends on `Lean.ofReduceBool`). These are the rows tagged "Mathlib + native_decide" in
`VERIFIED.md`:

- `Ecdlp/Proved/Secp256k1GenericSecurity.lean:49` → `secp256k1_bsgs_steps_le` and the
  `2²⁵⁵<n`-fed `secp256k1_generic_security` (`Nat.sqrt_lt'` reduces the goal, leaf by
  `native_decide`)
- `Ecdlp/Proved/Secp256k1Order.lean:28,42` → `secp256k1_beta_orderOf`,
  `secp256k1_lambda_orderOf`, `secp256k1_three_cube_roots_of_unity` (order-3 / cube-root
  count; the `≠ 0` leaves go via `ZMod.natCast_eq_zero_iff` + `native_decide`)
- `Ecdlp/Proved/DivisionPolynomialDegree.lean:25,53` → `secp256k1_Ψ₂Sq_natDegree`,
  `secp256k1_Ψ₃_natDegree` (leading-coeff `≠ 0` leaf via `native_decide`)
- `Ecdlp/Proved/FourDivisionPolynomial.lean:42` → `secp256k1_preΨ₄_natDegree`
- `Ecdlp/Proved/Secp256k1Curve.lean:76` → `IsElliptic` instance,
  `secp256k1_generator_equation`, `secp256k1_generator_nonsingular`
- `Ecdlp/Proved/GlvEndomorphism.lean:` → `secp256k1_glv_preserves_equation`,
  `secp256k1_glv_preserves_nonsingular` (β³=1 leaf is `native_decide`)
- `Ecdlp/Proved/P256CardinalityExact.lean` → `p256_card_point_eq_n` (with
  `p256_no_two_torsion_cubic`, `p256_two_ne_zero`): the argument and the no-root certificate
  are kernel-only, but the result inherits `native_decide` through `p256_generator_addOrderOf`
  (`n • G = 0`), the curve facts of `P256Curve.lean`, and the Pratt certificates
- `Ecdlp/Proved/Secp256k1CardinalityGeneral.lean` → `secp256k1_card_point_eq_n_general`
  (second derivation of `secp256k1_card_point_eq_n`; its 2-torsion step is kernel-only, the
  order fact `secp256k1_generator_addOrderOf` and the Pratt certificates are not)

#### IMPORTANT mitigation — the primality certificates (`Secp256k1PrimeP.lean` / `Secp256k1PrimeN.lean`)

`secp256k1_p_prime` and `secp256k1_n_prime` are the most security-load-bearing facts in
the repo, and they are deliberately structured to **minimize compiler trust**. They are
**full Pratt certificates**: a kernel-checked recursion using Mathlib's
`lucas_primality`, where the heavy mathematical content (the Lucas/Pocklington
argument, factor primality propagated up a tree of sub-primes) is verified **by the
kernel**, and `native_decide` is invoked only to discharge **small, local checks** —
e.g. a single witness exponentiation `a^((p-1)/q) ≠ 1 mod p`, or a factorization
identity `p − 1 = 2^a·(q₁·…)` (see `Secp256k1PrimeN.lean:10–12`, `:127`, `:160`;
`Secp256k1PrimeP.lean:10–12`, `:175`). The compiler is therefore trusted only for
bounded arithmetic facts that sit *inside* a kernel-checked Lucas argument — not for the
primality conclusion itself. This is the correct way to use `native_decide` for a
high-stakes fact, and is the reason the trade-off in Section 4 is acceptable.
(Note: the ~22 internal recursive Pratt sub-lemmas are *not* counted as separate ledger
results — see the retired "128" figure in `VERIFIED.md`.)

**Count.** The generated full-ledger axiom audit prints the exact compiler-trusted set
for every CI run; `scripts/check_axioms.py` reports the count and fails on any
unregistered or disallowed dependency. The large majority of the ledger is pure-kernel
(bucket (a)); live ledger totals remain in **`STATUS.md`** / `data/stats.json`.

---

## 3. What CI actually ENFORCES vs documents

`.github/workflows/ci.yml` runs the following gates on every push / PR / dispatch.
Distinguishing *machine-enforced* (a red build blocks merge) from *documentation-only*:

| Step (ci.yml) | What it does | Enforced? |
|---|---|---|
| `Check count consistency (docs)` — `scripts/check_counts.py` | Parses the canonical ledger/stats surfaces, rejects retired headline strings, and checks that generated/current counts agree. | **MACHINE-ENFORCED** (build-breaking), complemented by `gen_stats.py --check` and the generated-artifact fixpoint gate. |
| `Ensure no incomplete proofs remain` | `grep -rniI --include='*.lean' --exclude-dir=Targets 'sorry' Ecdlp/` — fails if `sorry`/`admit` text appears in any **built** `.lean` file. `Ecdlp/Targets/` (open stems) is excluded by design. | **MACHINE-ENFORCED**, with the documented scope limit that it is a *text* grep over built files and deliberately skips `Targets/`. |
| `Ensure no built file imports an open target stem` | `grep` for `import Ecdlp.Targets` outside `Targets/`. Closes the hole where a built file could pull a `sorry`-bearing stem into the build graph (since `sorry` is only a warning). | **MACHINE-ENFORCED.** This is the guard that makes the previous grep sound. |
| `Fetch prebuilt Mathlib cache` + `Build and verify ALL proofs` — `lake build` | The **kernel** re-checks every built proof term. A `sorry` that reached the build graph, or any type error, fails here. | **MACHINE-ENFORCED.** This is the core verification: a green `lake build` means the kernel accepted every built theorem. |
| `Axiom audit (no sorryAx, no custom axioms)` — `lake env lean Ecdlp/LedgerAxiomAudit.lean` → `scripts/check_axioms.py` | Generates `#print axioms` for every named declaration resolved from all 325 ledger rows. It fails on `sorryAx`, guard/custom axioms, unknown names, or any mismatch between Lean output and `data/result_registry.json`; compiler-trust markers from `native_decide` are disclosed. | **MACHINE-ENFORCED and exhaustive over the named ledger declaration set.** Seven anonymous instance targets are source-resolved exemptions because they have no source-level declaration name; their defining files are still built and their named load-bearing theorems are audited. |
| `Typecheck open target stems (non-blocking)` | `lake env lean` over `Ecdlp/Targets/*.lean`; `continue-on-error: true`. | **DOCUMENTATION/INFO ONLY.** A stem failing to typecheck emits a warning, never blocks. |
| `Featherless API smoke test`, `Prover target attempt`, report upload | All `continue-on-error: true` and skipped on PRs. | **DOCUMENTATION/INFO ONLY.** Prover orchestration; cannot affect the verification verdict. |

**Net guarantee:** a green `main` machine-guarantees that (i) every built theorem is
kernel-accepted with no `sorry`, (ii) no built file imports an open stem, and (iii) the
all named declarations referenced by the ledger depend only on the allowed trusted
base — i.e. no custom axioms, and every compiler-trusted (`native_decide`) result is disclosed. The
count-consistency and stem-typecheck steps are doc-hygiene, not correctness guarantees.

---

## 4. Honest caveats

- **"0 axioms" is shorthand for "no axioms beyond the standard three."** Every result
  uses Mathlib and therefore transitively `{propext, Classical.choice, Quot.sound}`.
  The honest claim is: **no custom axioms, no `sorryAx`** — machine-enforced by the
  axiom-audit gate. It is *not* a claim of axiom-free foundations.

- **The concrete compiler-trusted set is emitted by every axiom-audit CI run.**
  These declarations extend the TCB beyond the kernel to include the Lean compiler/runtime, via
  `Lean.ofReduceBool`. This means CLAUDE.md's invariant "the Lean kernel is the only
  judge of correctness" is, strictly, **not true for those declarations** — the compiler is
  also a judge. This is **`archive/docs/REVIEW_DOSSIER.md` finding 9** ("`native_decide` enlarges the
  TCB beyond the kernel"; severity LOW), whose verdict is *ACCEPTABLE trade-off,
  honestly fixable*: the mitigation is correct where it matters most — the primality of
  `p` and `n` structures `native_decide` to discharge only small checks inside a
  kernel-checked Lucas argument (Section 2(c)). This report is the disclosure that
  finding 9 asked VERIFIED.md to carry.

- **The GLV map is proved an ADDITIVE endomorphism, but the eigenvalue identity is
  NOT proved.** `Ecdlp.Curve.glvPoint_add` (bundled as `glvHom : Point →+ Point` in
  `Ecdlp/Proved/GlvHom.lean`) establishes `glvPoint(P+Q) = glvPoint P + glvPoint Q` for
  all branches — the homomorphism *half*. The cryptographically operative claim
  **`glvPoint = [λ]`** (that the endomorphism acts as scalar multiplication by the GLV
  eigenvalue λ on ⟨G⟩) is **now also proved** (`secp256k1_glvPoint_eq_lam_on_zmultiples`,
  `GlvSubgroupEigenvalue.lean`); with `#E = n` giving `⟨G⟩ = ⊤` (`grp_eq_top`) it extends to the
  full point group (`secp256k1_glvHom_eq_zsmul_unconditional`). The scalar eigenvalue facts
  (`glv_lambda_eigenvalue`, `lambda_is_cube_root`, etc.) about λ in `ℤ/n` / β in `𝔽_p` are the
  arithmetic inputs to that action statement.

- **Scope reminder (not a TCB issue, but bears on "what verified means").** The
  discrete-log protocol algebra (Schnorr/EdDSA, DH, ElGamal, Pedersen, Okamoto,
  Chaum–Pedersen, MuSig2/Taproot, Feldman VSS, adaptor/blind Schnorr) is proved over an
  **abstract** `[Module (ZMod n) G]` **and** now also instantiated at the concrete secp256k1
  point group `⟨G⟩` (`ProtocolInstantiation.lean`); it still encodes **no adversary / hash /
  probability model** (see `ABSTRACT_SCOPE.md`).
  Several "soundness/extraction" rows are scalar-field ring identities. These are sound
  Lean theorems; they are simply narrower than their cryptographic prose suggests.
