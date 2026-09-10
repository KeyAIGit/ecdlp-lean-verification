# Try a reproducible source handoff

Turn an existing source inventory into a short Markdown report and structured
JSON. It answers: which source revision was inspected, where the entrypoints
are, what source signals need review, and which verification step is still needed.

## Run the working demo

From this repository, with Python 3.10 or newer:

```sh
python3 scripts/source_handoff.py --demo
```

No API key, model credits, Lean installation, external clone, or network is
needed. This re-renders the existing pinned internal rehearsal snapshot; it does
not freshly inspect, build, or endorse the external project represented there.

To save both formats, choose a directory that does not already exist:

```sh
python3 scripts/source_handoff.py --demo --output ./_source_handoff_demo
```

The output is `report.md` plus `report.json`. A second invocation must use another
new directory. The command refuses to replace an existing report or follow a
symlink output path. Report JSON contains full lists; the readable view caps long
lists at 20 entries and says when it does so.

## Interpret the result

The report records source-level file, module, declaration-heading, and marker
counts. It also checks their internal consistency. It is **not** a proof
certificate, a count of novel theorems, a fresh compiled audit, a customer pilot,
or authorization to run a candidate. In particular, zero recorded `sorry` tokens
does not establish that all relevant declarations were built or correctly parsed.

The next action is concrete: review the adapter's coverage and the recorded
findings, then obtain a separately authorized build and exact axiom audit with an
appropriate execution boundary. The current project-execution limitations remain
in `repo/PORTABILITY_REHEARSAL.json`; this presentation tool does not remove them.

## Use another existing snapshot

The input is the version 1.0 JSON format produced by the existing
`scripts/lean_portability.py`, not a new importer or a new research database.
Supply the expected SHA-256 of the complete input file from a reviewed source:

```sh
python3 scripts/source_handoff.py --snapshot /path/to/snapshot.json \
  --expected-sha256 <reviewed-64-character-sha256> --output ./new-report
```

The tool requires the supported internal-rehearsal evidence classification,
checks the file and embedded manifest hashes, recomputes summary counts from the
recorded rows, checks module/import associations, and escapes displayed text.
Invalid input fails with a nonzero exit before creating a report. The per-input
size limit is 16 MiB. It never imports or executes code from the target project.

Hashes identify bytes and detect changes against the chosen reference. A
producer can also hash fabricated records, so a matching hash does not establish
independent authenticity or prove anything about the cited repository.

## Reproduce and extend

```sh
python3 scripts/test_source_handoff.py
python3 -m unittest scripts.test_lean_portability scripts.test_lean_compiled_probe scripts.test_check_portability_rehearsal
```

For the same snapshot and tool source bytes, the JSON and Markdown are identical:
there is no timestamp, random identifier, or absolute local path in either report.
The report includes hashes of both the renderer and its serialization helper.
The dedicated workflow runs the tests and compares two generated report pairs.

The tests exercise different module layouts through the unchanged existing
snapshot builder and this renderer. This demonstrates the report format's reuse
on those fixtures, not general-purpose project intake or universal scientific
methods. No source statement, mathematical result, historical snapshot, or
customer-hypothesis status is changed by generating a report.

Original project code uses [Apache-2.0](../LICENSE). Input records retain their
applicable rights and attribution; the renderer does not assign a new license to
third-party material. Contributions start at [CONTRIBUTING.md](../CONTRIBUTING.md).
