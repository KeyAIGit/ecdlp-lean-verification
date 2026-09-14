# KeyAI public-site review, 2026-09-14

final result: passed

## Scope and visual sources

This is an intentional redesign of the existing research site, not a pixel-for-pixel clone. The maintainer requested a clearer research identity, readable result examples, organization and governance pages, and simpler collaboration. Existing Nunito typography, logo assets, navy/blue palette, proof ledgers and technical tools are retained.

The source visual truth is the live homepage, results and collaboration pages captured before this revision. Source and revised captures are combined in:

- [Homepage comparison](docs/site-review-20260914/home-comparison.jpg)
- [Collaboration comparison](docs/site-review-20260914/pilot-comparison.jpg)
- [Results comparison](docs/site-review-20260914/results-comparison.jpg)

The before/after composition and text changes are intended. Source captures are 1348 × 925 pixels; revised desktop captures are 1348 × 926 pixels. Comparison panels are padded to 1348 × 926 without changing their aspect ratio. The desktop browser uses a 1:1 CSS/pixel scale. The browser viewport includes its scrollbar.

## Browser-rendered evidence

- [Homepage](docs/site-review-20260914/home-desktop.jpg)
- [Results](docs/site-review-20260914/results-desktop.jpg)
- [Collaboration](docs/site-review-20260914/pilot-desktop.jpg)
- [Research OS](docs/site-review-20260914/research-os-desktop.jpg)
- [Governance](docs/site-review-20260914/governance-desktop.jpg)
- [Mobile and tablet homepage](docs/site-review-20260914/home-mobile.jpg)
- [Mobile and tablet collaboration](docs/site-review-20260914/pilot-mobile.jpg)

Responsive captures use same-origin browser iframes, 390 × 844 and 768 × 844 pixels, at 1:1 scale. Scrollbars leave 375 and 753 CSS pixels for document content. These are responsive browser checks, not native-device emulation. Mobile collaboration document scroll widths equal the available widths, with no page-level horizontal overflow.

## Comparison history and fixes

1. P2, mobile navigation: the first revision inherited horizontal navigation scrolling, hiding Governance and Collaborate. The mobile header now wraps all links. Recapture in `home-mobile.jpg` and `pilot-mobile.jpg` shows every link and the collaboration action.
2. P2, results masthead: the inherited narrow heading measure still produced four lines. The heading now uses two concise lines and a wider measure. `results-desktop.jpg` and the results comparison show the corrected hierarchy.
3. P1, Research OS scope note: an inherited `!important` color made the new scope note dark on navy. Its dark-surface override now uses the disclosed muted foreground. `research-os-desktop.jpg` confirms that the current-stage limitation is readable.

Final comparison: no unresolved P0, P1 or P2 visual findings in the inspected states. Individual desktop captures supplement the combined views so that small labels and scope copy can be read at original scale. No separate crops were needed after those focused page views.

## Required visual surfaces

- Typography: existing local Nunito and fallback stack retained; shorter display headings, readable body copy and explicit evidence labels.
- Layout: reduced first-screen density, consistent content grids, and responsive stacking; the technical Research OS page remains deliberately more detailed.
- Color: existing navy/blue tokens retained; corrected the scope-note contrast.
- Assets: original logo and font files reused, with no generated replacement artwork.
- Copy: research program separated from the developing workspace. Examples resolve to current ledger declarations and disclose trust and scope. No new scientific achievement, customer validation, provider approval or hosted capability is claimed.

## Interaction and integrity checks

Primary navigation, the pilot protocol disclosure, Research OS stage disclosure, result search and its empty state were exercised in the cloud browser. Searching `secp256k1_p_prime` returned one result; an unmatched query displayed the empty state. The pilot action resolves to the canonical GitHub issue template. No issue was submitted during testing.

Browser error logs were inspected: no errors from the preview origin were recorded; unrelated browser-extension metadata errors were excluded. Structural checks cover all nine pages, internal links/fragments, unique IDs, landmarks, shared assets, generated freshness and static evidence availability. Canonical counts, ledger isolation, licensing and public scope checks remain separate gates. Full Lean acceptance and publication are handled by the existing required CI and GitHub Pages deployment.
