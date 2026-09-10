# Contributing

Original contributions are accepted under [Apache-2.0](LICENSE), the same
license as the project. By intentionally submitting work for inclusion, you
provide it under those terms unless you explicitly identify different terms for
review. Keep third-party attribution and explain the source and permission for
imported code or data. You retain your copyright; no assignment or automated
sign-off is imposed. See [LICENSING.md](LICENSING.md).

## First working example

Run `python3 scripts/source_handoff.py --demo` to produce a source-only handoff
from the existing internal snapshot without a model key, network or Lean install.
[The guide](docs/SOURCE_HANDOFF.md) covers JSON/Markdown export, reproducibility,
input hashes and the distinction between source inventory and compiled evidence.
This is contributor onboarding, not a completed external pilot.

## Choose a bounded task

Use `STATUS.md` for current evidence and `tasks/NEXT.md` for the appropriate
research or product queue. A missing theorem, open conjecture, or large corpus
is not itself an authorized experiment. Keep ECDLP, ResearchOS, and exploratory
Riemann-Hypothesis results separate. Do not run paid models, remote servers,
wallet targets, or new experiments merely because an agent can access them.

## Reviewable changes

1. Branch from the intended reviewed base and state it in the PR. Preserve other
   branches and unpublished work. Prefer a small change with explicit scope.
2. For a Lean change, freeze the intended statement, hypotheses and trust base
   before proof search. Never weaken it to make a build pass. Document which
   existing results are reused, and distinguish a new result from a wrapper.
3. Run the relevant checks, record the exact commands, environment and outcomes,
   and retain failures. A text scan or Python test is not a Lean kernel check.
4. Regenerate derived artifacts through their generators; do not patch generated
   counters, manifests or claims by hand. Describe AI assistance and human review.
5. Submit a PR with scope, provenance, tests, limitations and rollback. Merge only
   after all required checks and review pass. A candidate is not a release.

## Verification

The setup and full build commands are in [SETUP.md](SETUP.md). For changed
metadata, useful early checks include:

```sh
python3 scripts/check_oss_readiness.py
python3 scripts/test_check_oss_readiness.py
python3 scripts/export_agent_bundle.py --manifest
python3 scripts/export_agent_bundle.py --check
python3 scripts/check_repo_artifacts.py
python3 scripts/check_generated_fixpoint.py --check
```

The first check verifies the adopted license and notice metadata. It does not
certify legal ownership or replace a Lean build. No API key is needed for these
checks, and none of them spends model credits.

Formal acceptance additionally requires both canonical library builds and the
exact registry-bound axiom audits in CI. `native_decide` has additional compiler
trust; preserve the per-declaration disclosure. Do not import open target stems
or release candidates into the canonical proof base without explicit promotion.

A grant work plan, benchmark target, or proposed external pilot is not delivered
functionality. Claims in public documentation must reflect observed evidence.
