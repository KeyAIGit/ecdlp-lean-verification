# OSS readiness review, 2026-09-09

## Scope and decision

A maintenance and licensing-readiness pass, not a new mathematical result,
cryptographic assurance certificate, or completed open-source release.
Review base: `5cc58439f109aa22db06787a464ce72054e6502e` from draft PR #432.
Canonical main at the review start: `a67c7558f0a02cd96bd852a68b68ca8799143556`.
The new branch is stacked on #432; neither it nor the new work is accepted on
main merely by publication. Separate research branches and parity lab are outside
this change. No new experiments or external model calls are authorized here.

## Findings and remediation

| Finding | Action | Remaining boundary |
|---|---|---|
| No root license and no documented releasing rights holder | Add licensing decision checklist and proposal | Maintainer/rights-holder decision still required |
| Two attributed Apache-licensed source files | Supply license text and preserve upstream attribution | No blanket claim of original authorship |
| Two WOFF2 files without adjacent license texts | Supply matching OFL notices, pin binary/notice hashes | Exact binary build provenance not established |
| Existing #432 main build stopped at stale agent-bundle metadata | Regenerate through the original generator; move the cheap freshness check earlier | Actual canonical Lean build must still run |
| No concise contribution/security entry points | Add CONTRIBUTING and SECURITY with current limits | No claimed external adoption or reporting SLA |
| Optional dependency prose said correctness needed no Python libraries | Correct wording: full CI also uses pinned SymPy certificate checks | Do not conflate CAS checks with Lean proofs |

The previous failed proof run was `34015245058`. Its main job `101438087500`
stopped at `scripts/export_agent_bundle.py --check`, after the earlier metadata
and Python checks. Canonical Lean builds and both canonical axiom audits were
skipped, not failed mathematical proofs. The isolated six-candidate job succeeded.
The separate Docs sync run `34015245200` passed its regeneration and consistency
gates, then failed at the explicit derived-artifact drift step. Both runs
therefore require regenerated artifacts to be committed, not relaxed checks.

The local source snapshot and original Git objects were taken through temporary
read-only workflows on this review branch, with pinned actions and no persistent
Git credentials or model secrets. Original commit identities were restored for
provenance replay; an initial file-only snapshot could not pass history-bound
checks. The bootstrap workflows are removed from the final source tree.

The tested patch is transferred byte-for-byte through a hash-checked, one-time
branch-scoped apply workflow. It validates the expected base and exact changed
paths, runs cheap checks, and pushes only this review branch without force. The
apply workflow and payload remove themselves from the final source tree. This
does not authorize a merge to main or bypass the normal PR verification.

## What this pass does not do

It does not re-prove every declaration, audit every third-party dependency,
license unknown-rights content, promise an autonomous discovery system, or merge
other scientific branches. The new inventory/checker checks declared files and
pending blockers; it is not an automated legal opinion or exhaustive provenance
scanner. A green check explicitly does not mean OSS clearance.

A bounded current-tree scan for common GitHub/OpenAI/AWS token patterns and
private-key headers returned no matches. This is not a full history scan,
credential-validity test, or security audit. Git commit labels for AI tools and
bots are not evidence of legal ownership. No personal emails from the Git author
inventory are added to this report.

## Repository direction

Do not rewrite the verified mathematical library for the grant. Preserve the
proof surface, canonical ledgers, frozen corpus and evidence history. Prioritize:

1. A clean, fully verified release with explicit rights and scope.
2. A small reproducible contributor example with frozen statements and measured
   cost/review outcomes, then a larger Codex evaluation if funded.
3. Separation of reusable workflow infrastructure from domain-specific research
   only when another project actually needs it. Do not invent external adoption.

The six-month grant plan remains a proposal. Task counts are targets, not accepted
proof counts. No grant submission, award, new release or full OSS clearance is
claimed by this maintenance PR.

## Reproduction

See the PR for executed checks, exact remote commit and current CI status.
Local test reports distinguish the initial file-only snapshot from the later
replay with original Git objects. Full canonical Lean builds and compiled axiom
audits remain separate checks; passing Python or provenance checks is not their
replacement.
`STATUS.md` remains authoritative for canonical mathematical counts.

## Local validation performed

- New notice/readiness mutation suite: 32 tests passed; strict release-readiness
  mode correctly remains nonzero while rights are unconfirmed.
- Existing Python-only v0.2 controls, 15 additional assurance fixtures, 40 axiom
  parser tests, ledger-isolation checks/fixtures, registry freshness checks,
  count/scope checks, and public-site/product checks passed.
- All original generators completed with original Git provenance available.
  A direct repeat of the original generator order changed none of 38 outputs.
- The temporary-copy `check_generated_fixpoint.py --check` command exceeded the
  local execution limit. The direct repeat above is separately reported, not
  mislabelled as a passing execution of that CLI. Normal CI must still run it.
- No local Lean toolchain was available, so no new local kernel-build or compiled
  axiom-audit success is claimed. Those remain the canonical CI gates.
