# ECDLP Lean formalization v0.2 candidate

Preparation date: 2026-09-05 (America/Los_Angeles).
Candidate label: `0.2.0-rc.1`. **Not a published or accepted release.**
Reviewed base: `a67c7558f0a02cd96bd852a68b68ca8799143556`.

This directory is an isolated release-assurance intake. It is not imported by
`Ecdlp.lean` or `ResearchOS.lean`, is not in either canonical ledger, and adds
**zero accepted results** to the project's headline counts.

## Preparation evidence

The supplied strict axiom-log checker was exercised against 40 defensive Python
fixtures. Exact synthetic scalar controls and integer/rational comparisons were
replayed in Python. These checks are reproducible without network access.

**The six Lean theorem candidates have not been compiled in the preparation
environment.** Lean/Lake was unavailable. No successful full-repository build,
full generated-artifact closure check, or GitHub publication is claimed.

`InformationLoss.lean` contains six elementary candidate declarations:

| Declaration | Exact intended scope |
|---|---|
| `noExactDecoderOfCollision` | A feature collision between different labels prevents an exact decoder. |
| `complementaryPair` | A common binary prediction has exactly one success on complementary labels. |
| `pairedHits_eq_length` | A finite list of such equally weighted pairs has exactly half its observations correct. |
| `maskedEdgeIdentity` | A binary mask changes local edge discrepancies only where its endpoint masks differ. |
| `anchoredSequenceUnique` | Two sequences with the same initial bit and the same exact alternating transition agree. |
| `rationalEnvelope` | One explicit cross-multiplied integer inequality; not an analytic character-sum theorem. |

These are scoped building blocks, not new public parity evaluators. The finite
paired-list lemma is not yet a formal bridge from arbitrary elliptic-curve
feature functions to a probability statement. The numerical inequality does not
establish the subgroup-order premise, the analytic cycle-label bound, or its
cryptographic applicability. Literature novelty is not established.

## Reproduce

```bash
python3 scripts/verify_v02.py --python-only
python3 scripts/verify_v02.py --candidate-only
```

The second command requires the repository's pinned Lean toolchain. It must
successfully elaborate the candidate and match all six names against the
candidate-only registry and the standard allowed axiom base. Missing tools,
unrecognized native-axiom formats, mismatched names, malformed logs, and failed
elaboration are errors, not skipped proof obligations.

For release preparation on a trusted local checkout:

```bash
python3 scripts/verify_v02.py --full
```

This requests `lake clean`, `lake build`, both canonical ledger axiom audits,
and the candidate audit. It does not replace the existing full CI, regenerate
all repository outputs, merge a branch, alter a ledger, or approve a release.
Local component reports are written to new `_v02_validation/run-*` directories;
they remain evidence for that specific invocation, not a release certificate.

## Promotion requirements

1. Compile the candidate and audit the exact declarations on the pinned toolchain.
   Check compatibility of the stricter checker with both complete real ledgers.
2. Review mathematical statements, hypotheses, and all claimed bridges. Leave
   the analytic cycle-label theorem pending until it is actually formalized.
3. For selected accepted statements, use the existing repository generators to
   update imports, the correct canonical ledger, registries, audit files, and
   generated views together. Do not manually increment counters.
4. Run every existing blocking CI gate, generated-artifact closure, and a clean
   project rebuild. Resolve any failures; do not disable checks to force green.
5. Complete review of the remaining workflows, dependency supply chain, cache
   provenance, and branch/ruleset protection. Review and sign off the release.

The existing `release/v0.2-assurance` branch is not owned or modified by this
package. C55/C56 and other stacked draft PRs are not merged automatically.
The separate parity laboratory is outside this package's permitted repository.

## Remaining operational boundaries

The patch disables the legacy `autonomous-engine` job, not every workflow.
Re-enabling it requires a reviewed execution architecture separating untrusted
candidate execution from secrets, network access, and publication authority.
A manual trigger is not an execution sandbox.

The core checkout and elan bootstrap script source are pinned in the proposed
patch. The elan-downloaded binary, Mathlib cache, and other actions/dependencies
still require supply-chain review. Do not interpret these local changes as a
complete security certification.
