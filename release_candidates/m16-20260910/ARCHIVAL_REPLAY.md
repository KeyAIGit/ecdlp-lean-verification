# Archival replay

## Integrity checks (no numerical search)

From a clean checkout of the feature branch:

```sh
python3 release_candidates/m16-20260910/audit_archives.py
python3 release_candidates/m16-20260910/replay.py
python3 -m unittest discover -s release_candidates/m16-20260910 -p 'test_*.py' -v
```

These checks do not install dependencies or call model APIs. The four ZIP
hashes identify exact original artifacts; the public archive audit also checks
all embedded manifests and 98 expanded source files. Historical logs and their
labels are retained, including unsuccessful and time-limited attempts.

## Rerun historical numerical verification

Extract `archives/M16_derivative_continuation_2026-09-10.zip` into a new
working directory. Use a dedicated Python environment with SymPy 1.14.0.
From its `M16_derivative_continuation` directory, after reviewing the sources:

```sh
python check_derivative_structure.py
python validate_searches.py
```

These commands verify the historical structures and saved small answers; they
are not new searches against an unknown 256-bit target. Generated reports can
contain new timings and therefore need not have the historical report hashes.
Keep them outside the frozen repository snapshot.

The nested `input/M16_next_100_nodes/` directory contains the coefficient/root
arrays and their generator. Rebuilding the arrays with the original fast
multiplication helper requires GCC and GMP development headers on Linux:

```sh
gcc -O2 -fPIC -shared kronecker_gmp.c -lgmp -o kronecker_gmp.so
python build_usable_polynomial.py roots
python build_usable_polynomial.py build
```

The original reports document exact scope, failures, dependencies and timings.
Do not relabel planted inputs as independent targets or finite tests as Lean
proofs. The source-only intake scripts remain separate from canonical proofs.

## Transport provenance

`archive/m16-transfer-20260910/` retains the small lossless descriptor and the
bounded restore/install sources. These were only a transport mechanism. The
final ZIP files themselves are the authoritative original artifacts and can
be downloaded directly; no restoration step is required to read them. The
one-time publishing workflow is removed after successful publication. No
ongoing remote job, new solver campaign or paid inference is configured.
