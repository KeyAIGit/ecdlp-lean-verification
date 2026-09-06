# v0.2 assurance review

Status: targeted source review and prepared remediation, not a complete security audit.
Base: `a67c7558f0a02cd96bd852a68b68ca8799143556`.
No production secrets, hosts, wallets, or unknown private keys were accessed.
No exploitation or offensive testing was performed.

## Findings and exact remediation scope

### A1. Axiom log gate accepts structurally ambiguous evidence

Source: `scripts/check_axioms.py`, original blob
`3fb52747d599d447c5757af6297585e13629f2de`.

The old parser reduces observed declaration names to a set. It does not reject
duplicate declaration records or require every apparent record to parse. An
explicit but empty `axiom_base` map disables per-row mode; a partial map does not
have exact-key coverage validation. Broad substring recognition of native
auxiliary names is also weaker than a documented syntax plus owner membership.

Prepared change: strict records, duplicate rejection, exact declaration-set
matching, duplicate JSON-key rejection, complete trust-base maps when present,
closed native-auxiliary syntax, registry owner checking, bounded input reads,
and explicit legacy-mode disclosure. Tested on defensive synthetic fixtures.

Limit: names and text logs alone cannot authenticate proof terms or distinguish
all hand-declared axioms from compiler-generated ones. This is NOT a replacement
for source review, successful Lean execution, kernel checks, provenance, and the
existing no-custom-axiom source gates. The current project is not claimed to
contain an invalid theorem. Compatibility with all real logs remains untested.

### A2. Legacy model execution retains a secret-bearing execution context

Source: `.github/workflows/autonomous-engine.yml`, original blob
`47a4e465ff35c39cc15ddd4c9742503803816914`.

The manual workflow combines model-generated proof attempts, SSH credentials,
external-provider access, and a later publisher with repository-write authority.
Its own comments already acknowledge the isolation deficiency. Removing a
schedule does not isolate an execution environment.

Prepared change: the `engine` job has a constant false condition. Its inventory
entry remains parked and explicitly requires isolation and separate publication
before re-enabling. The historical workflow is retained for review.

Limit: other model/SSH workflows are not disabled or comprehensively assessed by
this patch. This is risk containment for one reviewed path, not a sandbox implementation.

### A3. Core verification workflow uses mutable dependencies and implicit permission defaults

Source: `.github/workflows/ci.yml`, original blob
`750b424fe0fb075aff4fe9708f461224aafbf72e`.

Prepared changes: explicit read-only repository permissions; checkout credential
persistence disabled; checkout pinned to its observed full commit; elan bootstrap
script source pinned; toolchain-mismatched broad project-cache fallback removed;
absolute cache-authenticity rhetoric corrected; release check requests a clean
project rebuild. Existing proof and consistency gates remain in place.

Limit: a pinned bootstrap script may still download a mutable binary; other
third-party action references remain; cache integrity is not certified by these
changes. A full dependency and workflow security review remains a release gate.

### A4. Public rhetoric can exceed actual formal assurance

Source: `README.md`, original blob `41ad3f25c9c72e8408d2d082a5cfac248c582d66`.

Prepared change: qualify build/kernel guarantees by the audited trusted base,
actual checked source, and hypotheses; remove the unsupported "first formalized"
priority claim; distinguish the combinatorial generic-group core from a fully
formal adaptive security theorem; correct the old repository slug; label the
whole update a release candidate rather than an accepted release.

Limit: this is not a complete rewrite of every historical note or generated site.
The existing semantic-drift and generated-artifact gates must still run.

### A5. Research integration status must not be inferred from PR descriptions

PR #430 was an open draft with base C55, not main, when read. Its head was
`db37d45e15fbe8e2ac8282973352e42fb24e15cb`; C55 base was
`7a7d91fe51b986c4c10102d539abc8d351e79537`. The main-branch request for
`Ecdlp/Proved/ScalarParity.lean` returned not found.

Prepared change: retain branch provenance and the pending integration decision.
Do not automatically merge the stacked research branches or count their claims
as new accepted release results.

## Authoritative implementation guidance

- GitHub Actions security reference:
  https://docs.github.com/en/actions/reference/security/secure-use
- Checkout credential behavior:
  https://github.com/actions/checkout
- Lean proof validation and trust boundary:
  https://lean-lang.org/doc/reference/latest/ValidatingProofs/
- Lean/Lake build configuration and dependency manifest:
  https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/

The exact project source revision and blob hashes, rather than a moving document
or badge, define what was inspected. No certification or finding of exploitation
is implied.

For unreviewed model-generated proof code, consider sandboxed proof-term export
and independent statement/proof checking as described in the Lean validation
manual. A stricter text-log parser cannot supply that guarantee.
