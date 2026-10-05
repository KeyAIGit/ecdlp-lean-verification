# Discovery memory v2: source-only candidate

A working local retrieval prototype for the existing research library. This is
engineering evidence, not a new cryptographic algorithm, Lean result, external
peer review or a claim of exhaustive literature coverage.

## Self-contained regression replay

Python 3.10+ on Linux/WSL with SQLite FTS5; no network, model keys or third-party packages:

    python3 -m unittest discover -s release_candidates/discovery-memory-v2-20260911 -p 'test_memory*.py' -v

There are42 distinct engineering tests across the original14 and new28 tests.
The tests use temporary synthetic databases. The Russian-article fixture tests
language handling; it does not attest to newly downloaded Russian publications.

## Installed behavior and boundaries

English queries support transparent algebra-context expansion. Exact project IDs
prioritize research notes and registries. Explicit breadth=all retains broad,
interdisciplinary retrieval; there is no language exclusion. arXiv URLs, legacy
IDs and version suffixes are recognized. Requested revisions are not certified
from unrelated dataset metadata and are not silently substituted on a read.

Source access checks the exact stored metadata and text hashes, supports outlines
and contiguous line windows, and can reuse a verified source cache. Offline reads
are labelled as cached snapshots, not current original-source validation. Comment-only
TeX lines are omitted from heading/find selection; original bytes are preserved.

The local command driver supports search/read/outline/retain/history/packet/resume
and a consistent SQLite backup followed by hash-verified copying. No daemon,
paid model use, trading operation or new scientific experiment is introduced.

## Runtime dependencies and data not published

The complete local3,120,928-row metadata catalog, original corpora, article text,
private deployment configuration and large databases are intentionally not in Git.
This is not a self-contained distribution of that corpus. Uncached source reads
need the existing reader project and its pinned dependencies. build_project.py
also retains deployment-specific source discovery defaults from the working WSL
installation; it is not a universal installer. Copy and adapt config.example.json
only to a library to which you have access. Do not execute source TeX.

The local deployment used all147 metadata shards of its pinned manifest and the
previous476,636-address baseline table. These are separate overlapping counts,
not4 million unique papers. The public LOCAL_VALIDATION report states its scope.
A broad metadata hit is not proof of full article availability or relevance.
The existing published full-text engine is still separately accessible.

## Review and rollback

No canonical proof ledger, experiment authorization or route decision is changed.
Original research archives remain untouched. Roll back this additive package via
a normal revert. The live installation retained a pre-upgrade source backup and
separate source-bound memory snapshots. Source review and applicable CI are still
required before promoting this package beyond candidate status.
