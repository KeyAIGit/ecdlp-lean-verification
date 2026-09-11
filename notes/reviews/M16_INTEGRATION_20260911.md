# M16 archival integration: provenance refresh

Date: 2026-09-11. This is an engineering integration record, not new mathematics.
Starting publication: `31e0ac23b73d36ee7cc6d17295b3fc28d58688f5`.

## Cause and disposition

Adding cited research documentation changed the live source registry. Its hash
is an input to both the shadow intake and the 100,000-cell structural projection.
Refreshing only the registry therefore left dependent state stale. Refreshing
that projection also changed the instance expected by its million-cell child.

The full existing generator chain was executed under Linux. The child policy's
expected parent root was advanced to the root actually computed from the new
inputs. No validation function, decision gate or mathematical statement was
weakened. This is an explicit new live instance, not a rewritten historical run.

Old parent root: `f3a8307285b1efd765d03021998c4a0cc338b0c995bde1cfb71b915676de903e`.
New parent root: `54f96896f413777d617da2d563cdc6bae16875dc8f46de69a0208b750498e4c4`.

The original parent/child states, child policy and shadow state are preserved
byte-for-byte under `archive/m16-integration-20260911/`, with source-commit and
SHA-256 bindings. Existing operational run and campaign records are untouched.
Changing input identity is not new scientific coverage or a new benchmark run.

Full repository CI and review remain acceptance gates; this note alone does
not assert they passed. Original research archive bytes are unchanged.
