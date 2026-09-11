# M16 research evidence intake

**Status: unpromoted research candidate. Not a Lean result, release, secp256k1
solution, or global search-complexity claim.**

This public, AI-assisted intake recovers the research trail from four September
10, 2026 conversation archives. It is based on main at
`e887029e21a5b97c05372b63b53f2d341ad15bda`. It does not alter the canonical
ECDLP/ResearchOS ledgers, route decisions, generated counters, or research
execution authorization. `B-PKC-M16-COMPLETE-COST-BRIDGE` remains open.

## Read and reproduce

- [Progress and next decisions, in Russian](PROGRESS_RU.md)
- [Scoped mathematical statements and proofs](THEOREMS.md)
- [Machine-readable evidence and publication boundaries](EVIDENCE.json)
- [Proposed API-credit work plan](GRANT_PLAN.md)

From the repository root, without a model key, network or third-party package:

```sh
python3 release_candidates/m16-20260910/replay.py
python3 -m unittest discover -s release_candidates/m16-20260910 -p 'test_*.py' -v
```

The first command checks all 5,043 monic polynomials in the declared small-field
families. It cross-checks the derivative condition, modular exponentiation and
linear-factor removal, and verifies 57 nonzero Jacobian determinants. It also
checks the characteristic counterexample. The second runs 17 polynomial regression tests plus 2 archive-integrity tests,
including malformed inputs and omitted-assumption failures. Python 3.10+ is
required. The public modulus guard deliberately limits this small-field replay
to primes at most 10,000; it is not a secp256k1 primality test.

The existing read-only verification workflow now has a separate `M16 candidate evidence (not Lean)` job. It checks the manifest, compares the replay report byte-for-byte, and runs the regression suite. The job does not promote prose into Lean results.

`replay_result.json` is a deterministic expected report. Rerunning is evidence
of these finite checks only. Alternative algebraic checks share arithmetic and
AI authorship; this is not an independent human review or proof-kernel audit.

## Complete archival publication

All four original ZIP archives are now included in [archives/](archives/), with
exact original byte lengths and SHA-256 hashes recorded in `ARCHIVES.sha256`.
The [expanded latest snapshot](../../archive/m16-20260910/M16_derivative_continuation/)
contains 98 original files, including nested earlier inputs, all historical
scripts, fixture matrices, the research-node lists and the large finite-field
polynomial/root arrays. The separate first factor-base ZIP is preserved too.

```sh
python3 release_candidates/m16-20260910/audit_archives.py
```

The audit checks the four ZIP files, every embedded checksum manifest and all
98 expanded files against the original archive bytes. It requires only the
Python standard library. `ARCHIVE_AUDIT.json` is the expected deterministic
report. [Archival replay instructions](ARCHIVAL_REPLAY.md) explain how to run
historical numerical checks in a disposable working copy.

`RESTORE_REPORT.json` records a byte-identical archival restoration. During
transport, deterministic bulky data were regenerated and required to match the
original SHA-256 hashes. Original timing fields were restored as historical
metadata, not represented as new timings. No new-target search was launched.

Historical notes are frozen: statements in them such as "GitHub unchanged"
describe the time of the original research pass, not this publication. The
current publication status is this README and `EVIDENCE.json`. Publishing an
archive does not promote its mathematical assertions or grant status.

## Acceptance and attribution

Original session contributions are offered under the repository's Apache-2.0
policy. The classical squarefree-support criterion is attributed in
`THEOREMS.md`; no novelty or priority claim is made for that identity. AI
assistance is disclosed, and no external reviewer endorsement is claimed.

Before promoting any mathematical claim: fix the statement and hypotheses,
request adversarial review, and obtain the applicable Lean build and exact
axiom audit. Before promoting a speed claim: preregister matched-success cost,
include preprocessing, failed attempts, memory and recovery, and distinguish
planted certificates from independent targets. Rollback this intake by a normal
revert; never rewrite historical results or weaken the canonical checks.
