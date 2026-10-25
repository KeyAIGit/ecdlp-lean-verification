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

## pyca/verified-garbage: Apache-2.0 (upstream: Apache-2.0 OR BSD-3-Clause)

Two files reuse or adapt code from pyca/verified-garbage, both at commit
`38c744308fcd4d10fec525d975f6164fe9f8d6fe` (upstream: https://github.com/pyca/verified-garbage).
The upstream `LICENSE` makes the software available under *either* Apache-2.0
(`LICENSE.APACHE`) or BSD-3-Clause (`LICENSE.BSD`, "Copyright (c) Individual
contributors. All rights reserved."). This repository uses the code under Apache-2.0.
Neither upstream source file carries a per-file copyright header.
License copy: [LICENSES/Apache-2.0.txt](LICENSES/Apache-2.0.txt).

### Kernel modular exponentiation (`KernelPowMod.lean`)

File:
- `Ecdlp/Proved/KernelPowMod.lean` (the declarations `powMod`, `powMod_zero`,
  `powMod_succ` and `powMod_eq` only; the `ZMod` bridge lemmas in the same file are
  project-authored)

Source: `lean/VerifiedGarbage/Proof/Framework/Pratt.lean`
(https://github.com/pyca/verified-garbage/blob/38c744308fcd4d10fec525d975f6164fe9f8d6fe/lean/VerifiedGarbage/Proof/Framework/Pratt.lean).
Modifications: the namespace was changed from `VG.Proof.Pratt` to `Ecdlp.Kernel` and short
attribution/docstring text was added; the definitions and proofs are otherwise unchanged.
Use: the witness-power leaves of the generated Pratt certificates for the secp256k1 and
P-256 primes `p` and `n` (`scripts/pratt_certificate.py`), and field inversion in
`Ecdlp/Proved/KernelScalarMul.lean`. The source, commit and license files for this entry
were read from GitHub.

### Cubic no-root certificate (`CubicNoRootCertificate.lean`)

File:
- `Ecdlp/Proved/CubicNoRootCertificate.lean` (the definitions `Tri`, `mulT`, `powT`,
  `evalT` and the lemmas `evalT_mulT`, `evalT_powT`, `noRoot_of_cert`, and
  `cubic_ne_zero_of_cert` adapted from `noTwoTorsion_of_cert`)

Source: `lean/VerifiedGarbage/Proof/Weierstrass/Cubic.lean`.
Changes: namespace, docstrings and formatting; two rewrite steps in `evalT_powT`; and
the short-Weierstrass adapter restated for natural-number coefficients over `ZMod p`.
The module docstring records the provenance. The curve-generic counting argument in
`Ecdlp/Proved/PrimeOrderCardinality.lean` is the same argument as upstream
`VG.Proof.Weierstrass.primeOrder_of`, but its Lean code was written separately (it follows
this repository's secp256k1 proof); both count Mathlib's `WeierstrassCurve.Affine.Point`.

Prior results at the same upstream commit: verified-garbage already kernel-checks the
no-root (no rational 2-torsion) fact for the same nine curves as this file
(`VG.Proof.P256.noTwoTorsion`, and the `noTwoTorsion` field of `VG.Proof.<Curve>.good`
for the other eight). For P-256/P-384/P-521 it also establishes `#E = n`, inside the proof
of `VG.Proof.Weierstrass.primeOrder_of`, as `Nat.card (wcC C).Point = C.n`, where `wcC C` is
Mathlib's `WeierstrassCurve.Affine` over `ZMod C.p` built from the specification curve `C`.
At that commit the count is not exported (the exported `VG.Proof.<Curve>.primeOrder` states
that every point other than the identity has order `n`). Correction (2026-10-22): since
verified-garbage commit `702cf77ff2db` (PR #3102, merged 2026-10-22) the count is exported as
`VG.Proof.Weierstrass.card_eq_n` (`lean/VerifiedGarbage/Proof/Weierstrass/GroupOrder.lean`):
`Nat.card (wcC C).Point = C.n` for a specification curve `C` under `[Fact C.p.Prime]`,
`Good C`, `C.n` prime, `G` on the curve, `n • G = O` and `2p + 1 < 3n` (`wcC C` has
`a₁ = a₂ = a₃ = 0`). Within verified-garbage it is used by `primeOrder_of` and
`killedByN_of`, which its P-256/P-384/P-521 files apply; no per-curve count is exported.
This repository's counts are stated for its own Mathlib curves (`p256_card_point_eq_n` for
`Ecdlp.P256.P256`, `secp256k1_card_point_eq_n` for secp256k1), and its curve-generic
`natCard_point_eq_of_addOrderOf` is stated over any finite field with `2 ≠ 0`, for
`a₁ = a₃ = 0` and any `a₂`, and for a point with `addOrderOf G = n` where `n` need not be
prime. Certificates were regenerated independently (by
`scripts/certs/cubic_no_root_certs.py`; a certificate is unique, so the data coincide with
upstream's). `VERIFIED.md` therefore lists the nine per-curve instances in its
"Ported / upstream-derived" table, outside the headline count.

### Registration

Neither file is registered in `repo/OSS_READINESS.json`: that gate registers only files
whose source carries a `Copyright` header line, and neither file (nor its upstream source)
has one. No legal review is recorded for either entry.

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
