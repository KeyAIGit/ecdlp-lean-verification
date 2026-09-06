# ECDLP Lean formalization v0.2 candidate

Candidate: `0.2.0-rc.1`. **Not a published or accepted release.**
Reviewed base: `a67c7558f0a02cd96bd852a68b68ca8799143556`.
Integration: draft PR #432, branch `review/v0.2-assurance-20260905`.

This directory is isolated from `Ecdlp.lean`, `ResearchOS.lean`, and both
canonical ledgers. It adds **zero canonical results** to headline counts.

## Actual verification

The initial preparation environment did not have Lean. Subsequently, GitHub
Actions compiled all six declarations with **Lean 4.31.0** and passed their
exact-name and per-row axiom audit. Every declaration reported **no axioms**;
none extended the dependency base through `native_decide`.

The observed check completed at `2026-09-06T05:51:12Z` (September 5 in
America/Los_Angeles), on the PR merge of source commit
`084e0e5eafd95ec74cd8237c1c0e5aef174e1a81` into the reviewed base.
`verification.json` records the source digests, exact toolchain, run/job IDs,
observed axiom sets, and evidence limits. This is a maintained CI observation,
not an independently authenticated proof certificate or approval of the release.

The axiom checker passed 40 defensive fixtures. The additional release suite
passed 15 integration/failure-path fixtures, locally and in CI. Exact finite
controls and rational arithmetic were replayed, including optimized Python.
The original package applicator separately passed 26 local tests.

Full canonical-library audits, repository-wide CI, generated-artifact closure,
clean release rebuild, and statement/scope review remain separate acceptance
gates. Consult PR #432 checks for their current outcome. A passed candidate
job cannot make another failed or unfinished job successful.

## What is checked

| Declaration | Checked statement |
|---|---|
| `noExactDecoderOfCollision` | A feature collision between different labels prevents an exact decoder. |
| `complementaryPair` | A common binary prediction has exactly one success on complementary labels. |
| `pairedHits_eq_length` | A finite list of those equally weighted pairs has exactly half its observations correct. |
| `maskedEdgeIdentity` | A binary mask changes an edge discrepancy only through its endpoint masks. |
| `anchoredSequenceUnique` | An equal initial bit and exact alternating transitions determine equal sequences. |
| `rationalEnvelope` | One explicit integer inequality, not an analytic character-sum theorem. |

The finite paired-list theorem is not a completed elliptic-curve/probability
bridge. The mask identity is not a formalization of the entire finite
counterexample family. The integer inequality does not prove the subgroup
order premise or the analytic cycle-label bound. These are scoped building
blocks, not public parity evaluators, and literature novelty is not established.
`knowledge.json` retains positive, negative, and pending outcomes separately.

`replay.json` is the frozen output of a Python-only invocation, so its
`lean_status: not_run` is accurate for that invocation. The later Lean result is
in `verification.json`. The unchanged Lean source header records the initial
preparation stage; it is not the current integration status.

## Reproduce

```bash
python3 scripts/test_v02_assurance.py
python3 scripts/verify_v02.py --python-only
python3 scripts/verify_v02.py --candidate-only
```

The last command requires the pinned Lean/Lake toolchain. CI also compiles the
Init-only candidate directly with `lean` in an independent read-only job.
Missing tools, failed elaboration, malformed logs, and registry mismatches
are errors, never proof acceptance.

For final release preparation in a trusted checkout:

```bash
python3 scripts/verify_v02.py --full
```

This requests `lake clean`, `lake build`, both canonical ledger audits, and the
candidate audit. It does not replace the rest of CI, regenerate every derived
view, merge a branch, edit a ledger, or approve a release. Invocation reports
are local files under `_v02_validation/run-*`.

## Promotion and operational boundaries

Promotion requires successful complete CI, a clean project rebuild, scientific
scope review, and explicit import/ledger changes through the repository's
existing generators. Do not manually increment counters or merge stacked C55/C56
drafts. The pre-existing `release/v0.2-assurance` branch is not modified.
The separate parity laboratory is outside this work's repository scope.

The candidate disables only the reviewed legacy `autonomous-engine` job.
Re-enabling requires secret-free isolated execution and a separately reviewed
publisher. A manual trigger is not a sandbox. Other workflows, dependency
binaries, action pins, and cache provenance still need a broader review;
this targeted change is not a security certification.
