# License adoption decision, 2026-09-09

The maintainer, Bekzod Dzhanpolatov (KeyAIGit), instructed continuation of the
proposed Apache-2.0 course, resolution and simplification of licensing, and
implementation of the necessary repository changes. This record documents that
instruction. It is not a signed ownership warranty, a DCO sign-off, a CLA, a
patent opinion, or an assignment to RFID INC. No such instrument is fabricated.

## Decision

Adopt the unmodified Apache License 2.0 for original project contributions and
preserve existing third-party terms. Use a single default, a short scope document,
and a component-notice inventory instead of a custom license. No additional
field-of-use restrictions are added. The scope is in `LICENSING.md`.

## Evidence reviewed

- Review source: `b51004536d60375631a0b10c7cc0f55226249e88`.
- Existing attributed Lean files already state Apache-2.0 and retain their authors.
- Both bundled fonts identify OFL-1.1 in embedded metadata; matching notices are
  retained. This is not an attestation of their exact original build commit.
- The frozen CSV's columns contain mathematical claims, project classifications
  and summaries. `data/README.md` identifies the project corpus and its checksum.
  The six source-claim JSON records use explicit `paraphrase`, locator, and
  boundary fields. They are not bundled publisher PDFs.
- Current-tree inventory found no PDF, book scan, or publication archive. This
  does not establish copyright clearance for every phrase or every historical
  revision. No full-history rights audit is claimed.

The grant covers the rights the project contributors can grant in their original
work. It does not override independent rights, relicense cited publications, or
claim that all files were written by the maintainer alone. Historical provenance
questions are scoped to their particular material rather than making the default
license for the original software perpetually pending.

## Operational effect

The root `LICENSE` now supplies an effective default license, with `NOTICE` and
`THIRD_PARTY_NOTICES.md` retaining attribution. The earlier pending-only checker
is replaced with a consistency check that accepts the adopted state, rejects
modified license text/missing attribution, and makes no release or legal-clearance
claim. The source, proof registry, frozen corpus, and archive are preserved.

Publication on a review branch does not imply merge to main, a verified v0.2
release, grant submission, or a funding decision. Those statuses are reported
separately in the pull request and CI.
