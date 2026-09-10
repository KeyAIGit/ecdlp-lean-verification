# ECDLP Lean formalization (v0.2 release candidate)

**Release candidate, not an accepted v0.2 release.** This update prepares
assurance fixes and isolated information-loss proof candidates. Its new
Lean source is not part of the canonical theorem counts. See
`release_candidates/v0.2/README.md` for exact verification status,
scope limits, and the remaining release gates.

![Verified theorems](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/KeyAIGit/ecdlp-lean-verification/main/badges/theorems.json)

KeyAI is a **verification workspace for AI research**. This repository is its public
reference deployment: a kernel-verified Lean 4 + Mathlib library about the secp256k1
elliptic curve, an evidence-gated map of classical ECDLP routes, and the provenance
contracts around both. It is a *verified research substrate* and an honest no-go map —
**not** a solution to any hard problem and not yet a self-serve hosted product.

**Portfolio priority update, 2026-08-04:** primary new frontier work is now an
isolated Riemann Hypothesis Stage 0 lane under
`domains/riemann-hypothesis/` and `tasks/RIEMANN_HYPOTHESIS.md`. It begins with
the exact target already present in pinned Mathlib, a declaration-level
foundation audit, and adversarial route triage. The repository claims no RH
proof candidate or progress on the conjecture. Existing ECDLP results,
decisions, and authorizations remain unchanged.

This file is the front door for humans and low-context agents alike. Strategy lives in
`ROADMAP.md`; live numbers live in `STATUS.md`; exact attack-route decisions live in
`repo/ECDLP_DECISION_SUBSTRATE.json`; bounded exploration policy lives in
`repo/RESEARCH_ENGINE_V0.json`; product category, current-vs-future capability, and the
MVP evidence gate live in `repo/PRODUCT_MODEL.json`; agents start at `AGENTS.md`.

## Reuse, contributions, and release status

**Apache-2.0 for original project contributions.** See [LICENSE](LICENSE) and
[LICENSING.md](LICENSING.md). Known third-party components retain their terms in
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md); cited papers are not relicensed.
No custom license or noncommercial restriction is added.

For a first contribution, use [CONTRIBUTING.md](CONTRIBUTING.md) and
[SETUP.md](SETUP.md). For integrity issues, see [SECURITY.md](SECURITY.md).
The [2026-09-09 readiness review](docs/OSS_READINESS_REVIEW_20260909.md) records
the earlier pending state. The [adoption record](docs/LICENSE_ADOPTION_20260909.md)
records the current licensing decision. Neither document certifies a release,
grant award, or ECDLP result.

## The one invariant (never violate)

**A successful build and the exact axiom audits validate the statements actually checked,
relative to their declared hypotheses and trusted base.** Lean checks proof terms;
`native_decide` additionally trusts the compiler. A green status alone does not
establish scientific novelty, cryptographic security, or coverage of an unbuilt file. Never `sorry`/`admit`, weaken/delete a proof to pass CI, or add an
axiom. Open conjecture stems live in `Ecdlp/Targets/` (one `sorry` each) and are
intentionally never built or imported, so the invariant holds.

## Where the canonical numbers are

**`STATUS.md`** — the single generated snapshot (ledger rows, distinct results, proved
modules, `sorry` = 0, custom axioms = 0, corpus coverage). It is produced by
`scripts/gen_status.py` from `data/stats.json` (which **recounts the `VERIFIED.md`
ledger table mechanically**), `data/frontier_map.json`, and the ECDLP decision substrate.
Typed evidence counts come from `data/typed_evidence_state.json`; Research
Engine generation, gate, and outcome counts come from
`data/research_engine_state.json`.
Do not quote a count from any
other doc — prose may be stale; if in doubt, cite STATUS.md. Machine-readable:
`data/stats.json` · badge endpoint `badges/theorems.json`.

For cross-lane discovery, use generated **`VERIFIED_INDEX.md`** or
`data/verified_index.json`. They index both canonical ledgers without merging their
accounting: `VERIFIED.md` remains ECDLP-only and `VERIFIED_RESEARCHOS.md` remains
ResearchOS-only. The aggregate row total is navigation, not a security metric.

**Current research decision.** `RS-2026-07-24-001` is current and supersedes
`RS-2026-07-22-001`, while explicitly carrying forward its zero-promotion
assessment. Its only positive selection was the now-completed
`GLV-SEMAEV-ITER-001`: one route received bounded symbolic and Lean structural
work while **zero** routes were promoted and **zero** experiments authorized.
Exact symbolic
replay shows that only the diagonal `C3` action survives among the enumerated
coordinatewise scalar covariances of `S3` and `S4`. The complete fixed-target
certificate is for `S4`: at every nonzero affine target in the stated
characteristics, only identity remains a coordinate-scaling covariance, while
the zero slice has exactly the diagonal `C3`. Lean separately proves that the
zero slice contains no `F_p`-rational affine secp256k1 target. The separate kernel-checkable
package proves the positive diagonal covariance and point-relation transport
identities, not the exhaustive stabilizer classification. This is a bounded
negative for the naive independent `u_i=x_i^3` quotient, not a Groebner lower
bound or an ECDLP result. The scope excludes infinity, extension-field targets,
and non-scalar or birational automorphisms.
The route remains parked, exact-target work remains forbidden, and no
asymptotic claim follows. New evidence enters
through the digest-bound proposal/review contract in `experiments/engine/` and
the candidate-neutral contract in `experiments/framework/`, with
source-commit-bound raw-artifact replay, engine-derived outcome classification,
review-anchored events in `experiments/engine/outcomes/`, and explicit reconsideration
triggers. Before synthesis, the typed evidence layer joins mechanisms to
target properties, claim-level evidence, scoped barriers, and cost quantities.
It retires decidable cells at desk and emits seeds only from unresolved cells;
none is a submitted or quality-cleared hypothesis. Creative output remains
untrusted and non-executable.
A positive toy result is `supported`, never `proved`.

## What NOT to claim

- It does **not** solve ECDLP on secp256k1 and offers **no shortcut**. secp256k1's
  concrete hardness is an **open conjecture**, not a theorem here.
- The generic-group `Ω(√n)` lower bound constrains **black-box** algorithms only; it says
  nothing about non-generic attacks. It is **classical** — Shor breaks ECDLP quantumly.
- The protocol library is **verified protocol algebra** (algebraic identities, now also
  instantiated on the concrete curve group) — **not** proven security of any deployed
  protocol: no adversary, no hash/random oracle, no probability model.
- Legacy dispatch automation is bounded and produced **0 accepted** external-model
  proofs. Real progress came from the tactic ladder plus human/assistant formalization.
  Research Engine v0 now derives bounded questions from typed evidence cells
  and compiles adversarially reviewed proposals, but its creative proposer is
  untrusted and it is not a finished autonomous discovery system.
- Never claim more than the kernel verifies. When unsure, state the limit plainly.

## Highlights (for a Lean / formal-methods reader)

Selected formalized results, with theorem-specific scope and compiler-trust disclosures:

- **The exact curve cardinality `#E(𝔽_p) = n` — proved without Hasse or Schoof**
  (`CurveCardinalityExact.lean`): a curve-specific certificate (`n ∣ #E`,
  `#E ≤ 2p+1 < 3n`, and `E[2] = {O}` excludes `2n`). With it the whole point group is
  `E(𝔽_p) = ⟨G⟩ ≃+ ℤ/n` (`CurveFullGroup.lean`, `PointGroupEquiv.lean`) — cofactor 1 as
  a theorem, not an assumption.
- **Pratt primality certificates for `p = 2²⁵⁶ − 2³² − 977` and the group order `n`** —
  full recursive certificates discharging `Fact p.Prime` / `Fact n.Prime`; the most
  reusable artifacts in the repo (Mathlib lacks them).
- **Generic-group DLP lower bound — the combinatorial core** (`generic_dlog_query_bound`):
  the information-theoretic heart of Shoup/Nechaev `Ω(√p)` via affine collision counting,
  to be read alongside the classical BSGS/Pollard-rho baselines. The repository
  does not formalize the complete adaptive adversary/probability theorem, so this
  entry is not a machine-checked end-to-end asymptotic security theorem.
- **The GLV/CM endomorphism, complete**: `(x,y) ↦ (βx, y)` proved an additive
  endomorphism (`glvHom`) with full slope/branch analysis, and the eigenvalue
  `glvHom = [λ]` **unconditional on the whole point group**
  (`secp256k1_glvHom_eq_zsmul_unconditional`) via the cardinality keystone.
- **Lean formalizations of Semaev summation polynomials `S₃`/`S₄`**, plus a
  division-polynomial / torsion-disjointness ladder (`Ψ₂…Ψ₇` coprimality via explicit
  Bézout certificates) and the early Weil ladder (W1–W3).
- **Audited attack boundaries**: Pohlig–Hellman, anti-MOV/Frey–Rück (embedding degree
  > 100), anti-Smart/SSSA (non-anomalous, ordinary trace), quadratic-twist security —
  verified structural exclusions at their exact scopes. The detailed attack evidence,
  target applicability, and unresolved routes are separated in the attack registry and
  decision substrate; this is not a proof against every classical algorithm.

The rest of the ledger is verified engineering (Mathlib wrappers, protocol-algebra
identities, instantiations) — honestly ~10–15% substantive, ~85% routine; the split is
audited in `COVERAGE.md`.

**Trust base (precise).** No result depends on any *custom* axiom or `sorryAx` —
machine-enforced by the axiom-audit gate (the generated
`Ecdlp/LedgerAxiomAudit.lean` / `ResearchOS/LedgerAxiomAudit.lean` +
`scripts/check_axioms.py`). "0 axioms" means none beyond Lean/Mathlib's standard
`{propext, Classical.choice, Quot.sound}`. Results proved by `native_decide` (the
concrete 256-bit facts) **additionally trust the Lean compiler** via `Lean.ofReduceBool`
— a real extension of the trusted base, catalogued per-theorem in `TRUST_REPORT.md`.

## Layout

| Where | What |
|---|---|
| `Ecdlp/Proved/*.lean`, `Ecdlp/Secp256k1Verified.lean`, … | the built, gated proof base (see `VERIFIED.md` for the row-per-theorem ledger) |
| `Ecdlp/Targets/` + `targets/*.json` | open conjecture stems + the prover-loop registry (never imported/built) |
| `ResearchOS/` | second lake target: the non-ECC portability instance (elementary number theory) |
| `STATUS.md` · `VERIFIED_INDEX.md` · `data/` | canonical live snapshot plus generated cross-lane result navigation, frontier map, graph, and registries |
| `BARRIERS.md` · `TRUST_REPORT.md` · `ABSTRACT_SCOPE.md` | the no-go map and the exact trust/scope boundaries |
| `ROADMAP.md` | the one strategy document (position, north star, program) |
| `AGENTS.md` · `CLAUDE.md` · `tasks/` | agent orientation, conventions, queue router, separate research/product queues |
| `REPOSITORY_ARCHITECTURE.md` + `repo/ARTIFACTS.yaml` | exhaustive whole-repo ownership map |
| `repo/FORMAL_SUBSTRATE.json` | machine-readable result families, critical path, blockers, and release boundary |
| `repo/ECDLP_DECISION_SUBSTRATE.json` | exact target, threat models, route dispositions, evidence gates, and foundation priority |
| `repo/ECDLP_TYPED_EVIDENCE_V0.json` · `data/typed_evidence_state.json` | typed source claims, target properties, mechanisms, barriers, cost quantities, regenerated cells, and non-experimental desk decisions |
| `repo/RESEARCH_ENGINE_V0.json` · `repo/HYPOTHESIS_GENERATION_V0.json` · `data/research_engine_state.json` | bounded generation/selector policies and generated proposal, exploration, and outcome state |
| `repo/HYPOTHESIS_SPACE_V2.json` · `data/hypothesis_space_map.json` | million-cell typed screening policy and aggregate evidence-bounded hot/warm/cold map; cells are questions, not independent hypotheses |
| `repo/HYPOTHESIS_SPACE_CAMPAIGN_V1.json` / `data/hypothesis_space_campaign_state.json` | resumable unique-coverage protocol and immutable exhaustion memory; repeated roots are operational replay, not new research coverage |
| `repo/PRODUCT_MODEL.json` | product category, current stage, public claim boundary, and MVP evidence gate |
| `scripts/site_generator.py` | generates the homepage, verified-result browser, operator workspace, route explorer, and pilot surface |
| `experiments/framework/` · `experiments/engine/` | candidate-neutral validation, generated-proposal intake, adversarial reviews, and append-only outcomes |
| `experiments/` · `domains/` · `notes/` (`notes/INDEX.md`) | validated experiments, domain registry, curated research memory |
| `archive/` | frozen history: superseded docs, raw traces, the undeployed platform scaffold |

## Build

Core verified file (no Mathlib): `lean Ecdlp/Secp256k1Verified.lean`.
Full project: `lake exe cache get && lake build`.
Toolchain pinned in `lean-toolchain` (Lean v4.31.0); Mathlib rev pinned in `lakefile.toml`.
CI is the verifier of record: build + no-sorry gate + axiom audit + consistency gates
(counts are recounted from the ledger table, so prose cannot silently drift). See `SETUP.md`.

## Legacy proving automation (honest)

The scaffolded loop — discover → attempt → scoped PR — is
`.github/workflows/autonomous-engine.yml`, **dispatch-only and job-disabled in this candidate**.
Re-enabling it requires reviewed isolation and a separate publisher; a manual trigger
is not a sandbox. The zero-cost tactic ladder
plus human-in-loop promotion is what has landed every proof; the free Featherless prover
tier is dead from CI (Cloudflare bot-block of GitHub runners, verified 2026-07-15) and
external model-provers stand at 0 accepted. `notes/ENGINE.md` documents the historical loop;
its branch isolation and budget caps do not provide a secret-free execution sandbox.
The prover-tier protocol and promotion rules live in `AGENTS.md`.

## Authorship & AI disclosure

The human maintainer is the author and bears intellectual responsibility for every claim
of novelty and significance. Formal acceptance is relative to the stated hypotheses,
the audited trusted base, and the actual source/toolchain used. It is not a guarantee
that an informal scientific interpretation is correct. Literature priority is not
established merely by formalization. AI tooling (assistant models for formalization, code, and proof search) was used
as an aid — it is disclosed here and is not an author. CI-bot commits are git metadata,
not authorship. License and the final author list are set by the maintainer.

## Where to go deeper

`STATUS.md` (canonical snapshot) · `repo/ECDLP_DECISION_SUBSTRATE.json` (route decisions) ·
`repo/RESEARCH_ENGINE_V0.json` (bounded exploration policy) ·
`data/research_engine_state.json` (generated engine state) ·
`data/hypothesis_space_map.json` (aggregate million-cell screening map) ·
`ROADMAP.md` (strategy & program) · `VERIFIED_INDEX.md` (cross-lane navigation) · `VERIFIED.md`
(the ECDLP ledger) · `BARRIERS.md` (the no-go map) · `TRUST_REPORT.md` (what "verified" rests
on) · `PUBLISHABLE_UNITS.md` (the 3 standalone results) · `notes/INDEX.md` (research
memory) · `SETUP.md` (build + CI + regen) · `tasks/NEXT.md` (queue router).
