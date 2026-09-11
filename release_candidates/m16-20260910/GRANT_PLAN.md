# Proposed Codex Open Source Fund work plan

**Prepared, not submitted by this session. Requested support: up to USD 25,000
in API credits, not cash. No award, receipt, external adoption or acceptance
probability is asserted.**

Official programme checked on September 10, 2026:
https://openai.com/form/codex-open-source-fund/
The form describes rolling review and grants up to $25,000 in API credits.
It does not promise an award for solving ECDLP. This plan preserves the budget
and six-month proposed scope of the September 9 prepared application.

## Project framing

KeyAI develops open-source verification and research-memory workflows for
human/AI formal research. The reference repository combines Lean/Mathlib
formalization, exact axiom audits, source-bound evidence and honest failure
retention. M16 is a concrete testbed for preventing unsupported claims: finite
checks, planted certificates, analytic arguments and complete solutions have
explicitly different assurance levels.

Funding is requested for maintainable tools and controlled Codex evaluations,
not for a promise to break secp256k1, solve P versus NP or target live assets.
No additional named collaborator is committed by this plan. AI assistance is
disclosed. External review is a planned requirement, not a delivered outcome.

## API-credit allocation (proposal, total $25,000)

| Workstream | API-credit allocation | Acceptance evidence |
|---|---:|---|
| Frozen maintenance/formalization evaluation tasks | $7,000 | Start with 20 fixed tasks; expand toward 100 only after protocol review. Exact statements, held-out tasks, bounded retries, all outcomes retained. |
| Declarative adapters on other public Lean projects | $6,000 | Explicitly scoped adapters and reproducibility reports; no portability claim until executed on those projects. |
| Provenance, CI and contributor workflow improvements | $5,000 | Reviewed code, clean-checkout replay, immutable hashes, failure handling and normal PR checks. |
| Adversarial and failure-path evaluations | $4,000 | Rejection tests for malformed evidence, stale bindings, omitted assumptions and unsupported scope promotion. |
| Replication, examples and documentation | $3,000 | Published scripts and reports with costs, limitations and independent-review status. |

API credits would pay only for eligible inference usage within the eventual
award terms and validity period. CPU/GPU rental, salaries, human reviewers,
hosting and other cash expenses are not represented as API-credit purchases.
These amounts are allocations, not measured expenditure or token forecasts.

## Proposed sequence, not completed milestones

Months 1-2: freeze the first 20 tasks, public evidence schema and adverse-input
suite; publish the source-only M16 example and close remaining packaging gaps.

Months 3-4: evaluate candidate generation and review with fixed context and
retry budgets; attempt the exact formalization targets and limited declarative
adapters. A failed proof attempt is retained, never weakened into success.

Months 5-6: perform replications, obtain external feedback where available,
and publish a portability and cost report. Expansion toward 100 tasks is
conditional on stable evaluation and the granted budget.

Report accepted-patch rate, actual API cost per accepted change, review effort,
verifier failures, false-acceptance findings and cross-project changes. Separate
engineering tasks from mathematical theorems. Avoid counting this research
node list as 100 benchmark tasks or 100 discoveries.

## Current evidence versus remaining gaps

The main repository already includes Apache-2.0 licensing and source-only
contributor handoff from PRs #433 and #435. This intake adds a standalone
5,043-polynomial replay and 17 regression tests; no new canonical Lean theorem
is claimed. Historical large-field checks used planted inputs. All four historical archives and the expanded latest snapshot are now public
in this feature branch; archival publication does not imply external replication.

Before making a strong application update, obtain the current PR's required
checks, preserve its exact accepted commit, and link the tested entry point.
Before claiming external reuse, record an actual outside user/reviewer and the
result. No external pilot, citation count, revenue or grant receipt is invented.

Private applicant contact details are intentionally excluded from this public
plan. Submission and any programme terms require their own explicit workflow;
this document is not an application receipt.
