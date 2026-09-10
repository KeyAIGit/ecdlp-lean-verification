# Third-party attribution and license notices

Original project contributions use [Apache-2.0](LICENSE). This inventory preserves
the different or pre-existing terms of known third-party components. It is not
a full legal-clearance report. Source headers remain authoritative. See
[LICENSING.md](LICENSING.md).

## Elliptic divisibility sequences: Apache-2.0

Files:
- `Ecdlp/Proved/NormEDSIsElliptic.lean`
- `archive/scratch/pr13155_eds.lean`

Both carry: Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0. Authors: David Kurniadi Angdinata.

The port's existing documentation additionally credits Junyan Xu (`alreadydone`)
and David Angdinata, identifies Mathlib PR #13155, and describes adaptation to the
pinned Mathlib API. Those mathematical contributions are not claimed as original
KeyAI work. Upstream: https://github.com/leanprover-community/mathlib4/pull/13155
License copy: [LICENSES/Apache-2.0.txt](LICENSES/Apache-2.0.txt).

This review leaves both source files byte-for-byte unchanged. Their headers and
existing modification/provenance notices remain authoritative; this inventory
does not certify an exhaustive comparison with the upstream PR.

## Fonts: OFL-1.1

| Bundled file | Copyright notice | License text |
|---|---|---|
| `fonts/Nunito-Variable.woff2` | Copyright 2014 The Nunito Project Authors | [OFL-Nunito.txt](fonts/OFL-Nunito.txt) |
| `fonts/Baloo2-Variable.woff2` | Copyright 2019 The Baloo 2 Project Authors | [OFL-Baloo2.txt](fonts/OFL-Baloo2.txt) |

The copyright strings and OFL links were read from each existing binary's name
table. The full corresponding license notices were checked against Google Fonts:
https://github.com/google/fonts/blob/main/ofl/nunito/OFL.txt and
https://github.com/google/fonts/blob/main/ofl/baloo2/OFL.txt .

The inventory records upstream notice blob IDs and local SHA-256 digests.
Notice copies normalize a UTF-8 BOM/trailing whitespace only. No font binary was
modified or replaced. This matches embedded attribution to the font families;
it does not establish the precise upstream commit used to create each WOFF2 file.

## Dependencies and research references

Lean, Mathlib and optional Python/JavaScript dependencies are external components
with their own licenses. Consult the pinned dependency source and its notices
when distributing their code or build artifacts. This is not a complete SBOM.

Project-authored summaries, annotations and code follow the default license.
The claim CSV and source-extract records retain their provenance and citations;
these do not grant rights over the cited publications themselves. Any externally
owned quotation or imported material retains its applicable rights, not a newly
invented blanket license. New copied code, datasets, figures, or assets must
arrive with source and permission information. The root license grants no
trademark rights to the KeyAI name or marks.
