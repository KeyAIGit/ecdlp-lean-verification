# M16 equation projection: unpromoted research candidate

Read [the statements, proofs and scope in Russian](README_RU.md).

A uniformly random one-dimensional kernel turns d+1 equations in d parameters
into d equations without losing any original solution. The expected number of
extra admissible base-field solutions is (|D|-|Z|)/(1+p+...+p^d), strictly less
than one. A full-column-rank original Jacobian stays full rank with probability
p^d/(1+p+...+p^d). These elementary statements do not bound geometric solution
count, solving degree, memory or time to find a root. No general-method novelty
is claimed. See the scope-limited primary reference in SOURCES.json.

The existing q4 fixture is exhaustively classified for validation, not presented
as a scalable solver. All real 256-bit targets solved: zero. No Lean acceptance,
external review, grant award or change of the canonical research route is claimed.
AI assistance and common authorship of the alternative checks are disclosed.

```
python projection_check.py --check
python -m unittest discover -p 'test_*.py' -v
```

Ten tests and the deterministic report were run locally on Python 3.13.5 with
NumPy 2.3.5. This is separate from the previous package's 19 tests. PLAN.json
was written before the census. RESULTS.json preserves a measured run; its time
is not an invariant or an ECDLP speed comparison. ATTEMPTS.json records the
serialization fault encountered during reproducibility checks.

The one real fixture witness is the previously easy repeated-point case 4P=R.
The original equation system is evaluated on all 912,673 coefficient assignments.
No attempt is made to enumerate the analogous 256-bit parameter space.

Original contributions follow the repository Apache-2.0 policy. Primary-source
ideas retain their attribution. Canonical proof ledgers and previous archives
are not modified by this package.

A separate matched representation probe on the same easy fixture did NOT
show a speedup: the square system's quotient-algebra dimension was 80 versus
1 for the original system; exhaustive base-field counts were 3 versus 1.
Both Groebner runs completed and the projected arm was slower in both observed
runs. See SYMBOLIC_PLAN.json and the raw diagnostic reports. This is not a
universal no-go theorem or an end-to-end algorithm benchmark.
