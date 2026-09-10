# KeyAI: preliminary commercial readiness

Decision date: 2026-09-09. This is an execution plan and draft pilot offer, not a claim of completed product work, a customer agreement, or a funding award.

## One product decision

Start with an assisted, narrowly scoped research-workflow pilot for a team maintaining a public or sanitized Lean repository. Do not start by rebuilding the site, adding billing, or advertising an autonomous universal research service. Keep the reusable tooling open under the adopted project license. A later paid service would charge for agreed setup, support, review, and operations, not for exclusive ownership of upstream results.

The existing `repo/PRODUCT_MODEL.json`, `repo/PILOT_PROTOCOL.json`, and `tasks/KEYAI_PRODUCT.md` remain authoritative. This plan does not set customer hypotheses to validated, count a pilot, unlock blocked implementation work, or authorize new scientific experiments.

## What is actually available

The reference repository has source-linked result ledgers, exact proof-dependency checks, evidence and decision history, and generated views. `scripts/lean_portability.py` provides a declarative, read-only source inventory. `scripts/lean_compiled_probe.py` is a separate compiled-evidence path. The existing portability rehearsal covers a different public software domain, but is internal technical evidence, not customer adoption.

The rehearsal's recorded BUILD disposition is blocked by two execution gaps: no OS-enforced isolation on that historical host and no verification launcher/output authenticity independent of the inspected project. An environment allowlist is not an operating-system sandbox. Do not accept arbitrary untrusted repositories for execution on the strength of the source-inventory or unit tests.

## Preliminary offer: one reproducible research handoff

**Intended participant:** the lead or maintainer of a multi-session formal-research project whose contributors lose track of assumptions, failed attempts, or verification state.

**Discovery input:** one public repository or a participant-approved sanitized workflow description, a named decision owner, the current verification command, and a recurring coordination problem. Do not request credentials, personal data, private keys, unpublished confidential material, or production systems in a public issue.

**Discovery output:** a short workflow map, observed orientation time, one concrete repeated failure and its current workaround, and an explicit build/change/stop/pending decision. This first step does not execute a new candidate. The output should be useful even when the decision is not to build.

**Follow-on technical deliverable, only after the existing authorization gate:** a commit-pinned source manifest; a small statement/task/evidence map; a report distinguishing source inventory from actual compiled evidence; one bounded candidate replay where an adequate execution boundary is available; and a next-action handoff. Every report must identify inputs, tool versions, actual commands and exit results, scope, missing evidence, and the responsible review decision.

**Acceptance:** the participant can explain current state, the principal unresolved obligation, and the next action; an independent rerun reproduces the reported artifacts; and no result is promoted on model narration or a source scan alone. Orientation within ten minutes and a completed return session are existing proposed metrics, not observed outcomes. Record review effort, setup effort, and actual cost separately. Do not infer willingness to pay from interest, attendance, or a grant.

**Commercial boundary:** no fixed price, delivery promise, support SLA, legal entity representation, or acceptance of confidential data is made by this draft. Before a paid engagement, agree the exact deliverable, exclusions, data handling, fee, acceptance criteria, and responsible contracting party. Do not fabricate a contract or customer commitment.

## Ordered work packages

| Order | Deliverable | Acceptance evidence |
|---|---|---|
| P0 | Integrate the current assurance/licensing repair | Full canonical build, both exact axiom audits, generated-data consistency and all required checks pass on the exact head; normal reviewed merge; no bypass |
| P1 | Publish a small contributor and pilot path | A newcomer can find setup, one worked example, evidence scope, and public intake without reading the research archive |
| P1 | Provide one reproducible source-only example/report | Fixed revision and adapter; repeatable output digest; no target code executed; inventory explicitly not proof validation |
| P1 | Close the two execution trust gaps | Hostile fixtures cannot read host secrets, escape work/output paths, use forbidden network access, outlive limits, shadow the trusted probe, or forge an accepted result |
| P1 | Finish one real external discovery | Participant-approved sanitized observation and disposition recorded under the existing pilot protocol; no invented traction |
| P2 | Run a second-project adapter session | Allowed only after discovery and execution gates; no project-specific edits to the generic inspector/generator; exact evidence and return session recorded |
| P2 | Test a paid service hypothesis | An explicit scope and actual customer buying decision, with delivery and support effort measured; not a speculative revenue forecast |
| Later | Hosted workspaces, accounts and billing | Build only when repeated use demonstrates which shared operations need a service |

## Reuse without promising universality

Separate three levels. The common workflow stores source identity, task, candidate, validation, review decision, and history. A verifier adapter specifies module roots, excluded files, entrypoints, toolchain, declared trust, and evidence format. Mathematical or domain-specific statements keep their actual hypotheses and domain data; an adapter cannot make them universal.

Reuse the existing portability inspector and probe contracts. Do not create a second scheduler, second result ledger, or parallel research engine merely to make a new product folder. Demonstrate reuse on the current reference and a genuinely different public Lean project with one unchanged generic implementation. Report every required adapter field and every code change. That is evidence of portability on tested projects, not a theorem about arbitrary disciplines or a claim that all research methods transfer.

For future method discovery, store the method's required structure, accepted input/output types, proof or validation obligation, and a known failure case. A proposed transfer becomes accepted only after its own checks. Preserve negative transfer evidence. Keep theoretical results separate from implementation tests, finite measurements, and commercial evidence.

## Website: change the entry point, not the whole stack

Keep the existing static generator, responsive styles, results browser, and research workspace. The first screen should explain the intended user and useful deliverable before showing the full research machinery. Suggested copy for review, not yet deployed:

> Know what your AI-assisted research actually established.
>
> KeyAI connects claims, source commits, verification results, and unresolved work in one inspectable handoff. Explore the public Lean reference project or help test the workflow with your team.
>
> Primary action: Discuss a pilot workflow.
> Secondary action: Inspect verified results.
>
> Current stage: public reference deployment. Assisted discovery is open; hosted multi-project execution is not available.

Show one scoped sample report close to the primary action. Keep detailed route maps, theorem accounting, and operator controls on their existing secondary pages. The current public GitHub intake must continue to warn that submissions are public. Do not add a private-upload box without implementing its data handling.

Normalize references to the repository's current canonical name; the source contains older references with a leading hyphen. Check actual redirects before labeling any link broken. Verify the final generated pages at narrow and wide viewports, keyboard navigation, focus states, link targets and the actual intake path. Parsed page text and source tests alone are not a visual/browser acceptance test.

## Maintenance change exposed during this review

A one-line proof improvement changed a source digest used by typed evidence, then by generated research identities. The correct response is an explicit regenerated rebind with old/new hashes and unchanged historical decisions, not weakening the digest check. Diagnostic seed identities and samples may legitimately refresh while historical runs and accepted results remain unchanged. Do not count such a rebind as new research coverage.

Preserve this invariant when simplifying the repository. Reduce duplicated presentation and repeated work, not the evidence needed to distinguish a tested artifact from an unverified claim.

## Reproduction already available

These commands exercise the existing implementation without executing an external repository or spending model credits:

```sh
python3 -m unittest scripts.test_lean_portability scripts.test_lean_compiled_probe scripts.test_check_portability_rehearsal
python3 scripts/check_portability_rehearsal.py --require-final
python3 scripts/check_oss_readiness.py
```

The first suite was rerun during this review: 44 tests passed. Its success does not close the recorded execution-boundary gaps. Full acceptance of the current maintenance PR remains tied to its actual final CI, not this document.
