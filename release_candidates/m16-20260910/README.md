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
checks the characteristic counterexample. The second runs 17 regression tests,
including malformed inputs and omitted-assumption failures. Python 3.10+ is
required. The public modulus guard deliberately limits this small-field replay
to primes at most 10,000; it is not a secp256k1 primality test.

`replay_result.json` is a deterministic expected report. Rerunning is evidence
of these finite checks only. Alternative algebraic checks share arithmetic and
AI authorship; this is not an independent human review or proof-kernel audit.

## What is and is not published here

The standalone polynomial replay, reviewed summaries, source hashes and grant
work plan are in Git. Full original archives, all historical scripts, fixture
matrices, and large generated polynomial/root binaries are **not** included in
this compact intake. They remain the original conversation attachments named
in `ARCHIVES.sha256`; a checksum is not a public download endpoint. Exact
archival replay requires those bytes. Do not imply that this is a complete
public replication package for every previous claim.

During intake the original latest archive was recovered, all 97 manifest
entries matched, and its structural and independent tiny-answer validators
were rerun successfully. The original 24 large-field cases are planted
certificates. No independently supplied 256-bit target was solved. Retained
solver timeouts are censored observations, not proofs of failure or measured
speedup factors.

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
