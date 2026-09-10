# Licensing status and proposed release policy

**Status: pending rights confirmation. There is no repository-wide license grant.**
The presence of license reference texts or a green metadata check does not license
otherwise unlicensed material. Existing third-party licenses remain in effect.
See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) and the bounded inventory in
[repo/OSS_READINESS.json](repo/OSS_READINESS.json).

## Proposed default: Apache-2.0

Apache-2.0 is proposed for original code, Lean formalizations, tests, and technical
documentation that the releasing rights holder can actually license. This proposal
is not adoption. The unmodified reference text is in
[LICENSES/Apache-2.0.txt](LICENSES/Apache-2.0.txt); it is also supplied for existing
Apache-licensed third-party source identified in the notices.

Apache-2.0 permits commercial reuse and modifications, subject to its conditions.
It includes an express, scoped contributor patent license and does not grant
trademark rights. Recipients need not publish all their modifications. Existing
grants are not revoked merely by changing a later release's license. The
maintainer should understand these tradeoffs before adopting it.

## What is not being relicensed

- The two attributed elliptic-sequence source files retain their upstream
  Apache-2.0 terms and authorship. Their source bytes are unchanged by this review.
- The two bundled font binaries retain OFL-1.1, not Apache-2.0. Their original
  copyright notices and full license texts are now provided alongside them.
- The imported claim corpus, excerpts, research archives, and brand artwork need
  their own provenance/rights review. Citation or a checksum is not permission.
- Dependencies keep their own terms. A Mathlib import does not establish ownership
  of this repository's other files, and Git author labels do not establish rights.

## Adoption checklist

The rights holder, not an agent, must supply a dated decision stating:

1. Who is granting the license: the individual maintainer, RFID INC, or another
   actual rights holder; which original contributions that party controls; and
   whether employment, contractor, coauthor, or assignment rights are involved.
2. Consent to Apache-2.0 for those contributions, including its commercial and
   scoped patent permissions. Do not forge a signature, DCO sign-off, or CLA.
3. For third-party material: the source and applicable permission, or a plan to
   exclude/replace it in a clearly scoped distributable. Do not erase provenance
   or silently delete archives to manufacture apparent clearance.
4. The release scope. Resolve the specific blockers in `repo/OSS_READINESS.json`
   rather than declaring the whole tree cleared because some files have licenses.

After that review: put the standard text in a root `LICENSE`, record the releasing
party and scope, retain all third-party notices, update contribution terms and
package metadata together, and verify a clean release build. Update the readiness
checker through review when the legal state changes; do not merely flip a flag.

Do not describe this repository as fully open-source licensed in a grant
application until this process is complete. A narrower licensed package is an
alternative if the imported research corpus cannot yet be cleared.

## Sources

- GitHub, Licensing a repository:
  https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/licensing-a-repository
- Apache License 2.0, sections 2-6:
  https://www.apache.org/licenses/LICENSE-2.0

This is a release checklist, not a legal opinion or a warranty of ownership.
