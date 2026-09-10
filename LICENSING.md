# Licensing

**Default license: Apache-2.0.** The unmodified license is in [LICENSE](LICENSE).
It applies to original project contributions: software, Lean formalizations,
tests, configuration, technical documentation, and project-authored annotations.
This includes those contributions wherever they occur in the repository; moving
an original file into an archive does not by itself change its license.

The maintainer requested adoption of this policy on 2026-09-09. The
[decision record](docs/LICENSE_ADOPTION_20260909.md) records that instruction,
not a transfer of ownership or a legal opinion. Existing contributor rights,
attribution, and separately stated licenses are preserved.

## Three rules for reuse

1. **Original project material:** use Apache-2.0. Commercial use and modifications
   are allowed subject to its terms. Keep the license and applicable notices.
2. **Third-party material:** keep its existing terms and attribution. The bundled
   fonts use OFL-1.1; the attributed elliptic-sequence code uses Apache-2.0.
   Details are in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
3. **Research sources:** our original summaries, metadata and annotations are
   covered by the default license. Citing a paper does not license the paper;
   quotations and independently owned material retain their applicable rights.
   No new permission over another party's work is asserted by this repository.

The frozen CSV is a project claim compilation, and the claim-extract JSON files
contain source locators, paraphrases, and scope notes. Their provenance remains
recorded in `data/README.md` and the files themselves; their bytes are not changed
by this licensing update. The original annotations are distinct from the cited
publications. Where the authorship or redistribution permission of a particular
imported passage cannot be established, check that passage's source before
redistributing it as separately licensed content. This is not a blanket clearance
of all historical imports.

Apache-2.0 includes a scoped contributor patent grant, permits proprietary
modifications, and grants no trademark rights. This policy does not add a
noncommercial, research-only, or acceptable-use restriction to that license.
Internal experiment/review controls govern this project's own workflow, not the
license rights of downstream users. Future contributors use the same default
terms unless a reviewed contribution explicitly states compatible other terms.

## Maintenance

For original work, no new license needs to be invented for each file. Preserve
third-party headers; record a new imported component's source, license and notices
in `repo/OSS_READINESS.json` and `THIRD_PARTY_NOTICES.md`. License texts belong in
`LICENSES/` or alongside the component. Run:

```sh
python3 scripts/check_oss_readiness.py
python3 scripts/test_check_oss_readiness.py
```

These commands check license/notice consistency, not legal ownership or the truth
of mathematics. Full build and axiom audits remain separate release requirements.
Older audit documents describe the state at their recorded commit; this document
and the root license are the current policy. There is no required registration,
custom-license approval step, or license fee introduced by this repository.

References: [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0),
[GitHub licensing guidance](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/licensing-a-repository).
