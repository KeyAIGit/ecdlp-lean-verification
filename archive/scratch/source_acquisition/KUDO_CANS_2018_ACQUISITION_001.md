# Kudo CANS 2018 acquisition audit

Audit ID: `KUDO-CANS2018-ACQ-001`

Date: 2026-08-11

Status: `unresolved_primary_full_text`

Target source: Momonari Kudo, Yuki Yokota, Yasushi Takahashi, and Masaya
Yasuda, *Acceleration of Index Calculus for Solving ECDLP over Prime Fields and
Its Limitation*, CANS 2018, LNCS 11124, pp. 377-393,
DOI `10.1007/978-3-030-00434-7_19`.

Endpoints checked:

- `https://link.springer.com/chapter/10.1007/978-3-030-00434-7_19`
- `https://link.springer.com/content/pdf/10.1007/978-3-030-00434-7_19.pdf`
- `https://kyushu-u.elsevierpure.com/en/publications/acceleration-of-index-calculus-for-solving-ecdlp-over-prime-field/`
- `https://api.unpaywall.org/v2/10.1007/978-3-030-00434-7_19`
- `https://api.openalex.org/works/https://doi.org/10.1007/978-3-030-00434-7_19`
- `https://dblp.org/rec/conf/cans/KudoYTY18`

## Acquisition results

| Endpoint | Observation | Disposition |
|---|---|---|
| Springer chapter and PDF endpoints | The DOI metadata page is reachable. The PDF endpoint redirects through Springer identity handling and returns an HTML chapter/access page, not PDF bytes. | No full text obtained. |
| Kyushu University Pure | HTTP 200 institutional metadata page with the published abstract. The 51,433-byte response contains no PDF or repository-file link. | Abstract and metadata only. |
| Unpaywall API | HTTP 200; `is_oa=false`; zero OA locations. | No lawful open copy identified. |
| OpenAlex API | HTTP 200; `open_access.is_oa=false`; zero locations with `pdf_url`. | No lawful open copy identified. |
| DBLP | Bibliographic record marks access closed and delegates open-copy lookup to Unpaywall. | Metadata only. |

Observed response digests are acquisition receipts, not source-artifact
digests and may change when provider metadata changes:

- Kyushu Pure HTML: SHA-256
  `43ed304e046f6626a4b22d3ebe8f06c3189acee8022b61158972ab512219c4a7`.
- Unpaywall JSON: SHA-256
  `077c17c336c81940dbcb370a549927127eb8c0e06a1594a9a93882a247823474`.
- OpenAlex JSON: SHA-256
  `9a052df73e252acd6d738ed88751c7a7cfba1c79e5c2de92d39017966766b820`.

No copyrighted chapter bytes were copied into the repository.

## Evidence boundary

The institutional abstract supports only that the paper studies an Amadori
prime-field index-calculus variant, uses a hybrid exhaustive-search/Groebner
method, uses summation-polynomial symmetries, reports experiments, and discusses
limitations. It does not expose the exact systems, symmetry action, assumptions,
algorithms, complexity derivation, experiment tables, or limitation theorem.

Therefore:

- `full_text_status` remains `full_text_unread`;
- no claim-level extract is created;
- absence from inspected open locations is not a novelty claim;
- the paper cannot yet clear or reject a mechanism, cost, or prior-art gate;
- research-question seed `RSI-2AD454D97023` remains non-executable;
- no route, hypothesis, candidate, calibration, recommendation, authorization,
  or secp256k1 experiment changes state.

## Reopening conditions

Any one of the following lawfully obtained artifacts reopens acquisition:

1. an author manuscript or institutional repository deposit;
2. a licensed Springer chapter supplied by the owner;
3. an author-provided copy with permission to inspect it.

On receipt, hash the exact bytes, record page count and edition, extract exact
section/algorithm/table anchors, and independently review the mechanism and
limitation before updating source status.
