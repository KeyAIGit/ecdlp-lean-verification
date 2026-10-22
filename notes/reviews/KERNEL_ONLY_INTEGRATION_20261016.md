# Kernel-only group structure: derived-state integration

Date: 2026-10-16. This is an engineering integration record, not new mathematics.
Starting publication: `ef416bb2244b6ccee64a2ab5204efe356daecfa1`.

## Cause and disposition

Replacing compiler-trusted proofs of the secp256k1 group structure with
kernel-only proofs changed ledger method cells. Those cells feed the result
registry, the typed evidence state and the research engine state, whose hashes
are inputs to the 100,000-cell structural projection. Regenerating that
projection changed its Merkle root, so the million-cell child policy no longer
matched its expected parent instance.

The existing generator chain was executed in documented order. The child
policy's expected parent root was advanced to the root actually computed from
the new inputs. No validation function, decision gate or mathematical statement
was weakened. This is an explicit new live instance, not a rewritten historical
run.

Old parent root: `54f96896f413777d617da2d563cdc6bae16875dc8f46de69a0208b750498e4c4`.
New parent root: `0bc7078ef11b1eb39cd8854dd65ee2817d1ca807f00465fae3b937df87f0caea`.

The previous parent/child states and child policy remain recoverable from the
starting publication above; no archive copy was added. Existing operational run
and campaign records are untouched. Changing input identity is not new
scientific coverage or a new benchmark run.

Full repository CI and review remain acceptance gates; this note alone does
not assert they passed.

## Merge with `main` at `4a807acf` (2026-10-22)

`main` advanced to `4a807acfdb00810b364629e1aef47423305ccf86` (#449, #446, #444, #450,
#447), and its own child policy pinned the parent root
`f30f9341a963d4e611a22453728117db2e6ecd03348d4c067fc04f453622d686`. This branch had pinned
`0bc7078e…` above, which was already stale after commit `eb98377f` (that commit's
computed root was `543a31fe…`). Neither pin matches the merged inputs. After merging
`main` into this branch, the generator chain was rerun in the `docs-sync.yml` order up to
`hypothesis_funnel.py`, the child policy's expected parent root was set to the root it
computed, and the full chain was rerun:

Parent root on `main`: `f30f9341a963d4e611a22453728117db2e6ecd03348d4c067fc04f453622d686`.
Parent root after the merge: `11099f0760f6447deb112a58afc419d1654544c1a9c7b20e24471e278e103694`.

`repo/ECDLP_DECISION_SUBSTRATE.json` is byte-identical to `main`, so the drafter policy's
pinned decision digest stays
`c561d201f03021526dca413714afd355dd94d2515693c15b1260f4001585bb28`. As above, no validation
function, gate or statement was changed, and the previous states remain recoverable from
the two parent commits of the merge.
