import Ecdlp.Proved.ParityFourier.Statements
import Ecdlp.Proved.ParityFourier.StatementsK

/-!
# Frozen statements W (the window law; row W of the parity coverage map)

This file fixes the statements; proof files must not edit it.

Disclosure (process exception): two scratch proofs were compiled on
2026-10-22 (session 3eaafce7), before this file was written, in
`bv/paperlean/Window.lean` (scratch, not in the repository; sha256
65b6a7094b446f652b32a6b1d7ee86118e9b46c6bba5043d095aa174d8d982e4).
`windowAbstract`: for finite `W ⊆ E`, a map `ρ` sending `E \ W` into itself
with `ρ (ρ k) = k` there, and real `F`, `T` bounded by `1` with
`F ∘ ρ = F`, `T ∘ ρ = -T` on `E \ W`, `|∑_{k ∈ E} F(k) T(k)| ≤ |W|`.
`windowSigma`: for odd `n`, a natural number `c` with `2c < n`, real `F`
with `|F| ≤ 1` and `F(2c - k) = F(k)` for every `k`,
`|∑_{k ≠ 0} F(k) sgn(k)| ≤ 2c`; this follows from the W-law bound and the
window size in W-shape. Its proof very likely contains the `c > 0`
reflection facts of W-shape, and `windowAbstract` with `c` removed from `E`
and `W` then gives the real, `c > 0`, everywhere-symmetric case of
W-refined. The drafter saw only the statement lines (and two proof lines of
`windowSigma`); the auditor and the freeze agent only the statement lines.
No scratch proof existed of the W-law identity, of `c < 0`, of complex `F`,
of symmetry assumed only off the window, or of W-x. These statements were
written from the map, not from that file.

Process note: for W-shape, the W-law bound and W-refined, a scratch proof of
a special case or closely related form (natural `c`, real `F`) was found
before this file was written (session 3eaafce7, 2026-10-22); the statements
were audited against the paper claim (map row W, N2), not against that
proof. For the W-law identity and for W-x no proof existed at freeze time.

Source: `reports/research_os/PARITY_COVERAGE_MAP.md` at commit 6876f75:
row W (line 50) and note N2 (lines 71–88: the general form and instance
(a), x-windows).

Setting: `n` is odd, `c` is an integer with `2|c| < n`, `sgn k = (-1)^k.val`
(`Statements.lean`), and `xFeature W Φ c0` is the x-only feature of
`StatementsK.lean` (`Φ(x(P))`, value `c0` at `O`). The window `windowW n c`
is `{1, …, 2c}` for `c > 0` and `{2c, …, -1}` as residues, that is
`{n + 2c, …, n - 1}`, for `c < 0` (N2, first bullet); for `c = 0` it is
empty, which is row K.

Statements:
* W-shape `WindowShape` (N2, bullets 1–3): the window has exactly `2|c|`
  elements, none of them `0`, and contains `c` when `c ≠ 0`; the reflection
  `k ↦ 2c - k` maps every `k ≠ 0` outside the window to a residue `≠ 0`
  outside the window, and flips the sign: `sgn(2c - k) = -sgn(k)`.
* W-law `WindowLaw` (N2, general form): for every `F : ZMod n → ℂ`, the
  exact identity
  `∑_{k ≠ 0} F(k) sgn(k) = ∑_{k ∈ W} F(k) sgn(k)
     + (1/2) ∑_{k ≠ 0, k ∉ W} sgn(k) (F(k) - F(2c - k))`
  (each pair `{k, 2c - k}` of the note appears twice in the last sum, hence
  the `1/2`), and, when `|F| ≤ 1`, the bound
  `|∑_{k ≠ 0} F(k) sgn(k)| ≤ #{k ∈ W : F(k) ≠ 0}
     + (1/2) ∑_{k ≠ 0, k ∉ W} |F(k) - F(2c - k)|`.
* W-refined `WindowRefined` (N2, instance (a), abstract form): if `c ≠ 0`,
  `|F| ≤ 1`, `F(c) = 0` and `F(2c - k) = F(k)` for every `k ≠ 0` outside the
  window, then `|∑_{k ≠ 0} F(k) sgn(k)| ≤ 2|c| - 1`.
* W-x `WindowX` (row W, "any `Φ(x(Q + [r]G))` with `r ≠ 0`"): on any
  Weierstrass curve over any field, if `G` has odd order `n`, `r ≠ 0`,
  `2|r| < n` and `|Φ| ≤ 1`, then
  `|∑_{k ≠ 0} Φ(x([k]G + [r]G)) sgn(k)| ≤ 2|r| - 1`, with the map's
  convention `F := 0` where `[k]G + [r]G = O`. Dividing by `n - 1` gives the
  row's `|corr| ≤ (2|c| - 1)/(n - 1)` with reflection centre `c = -r`.

Deviations from the map:
* `F` is complex-valued with `|F| ≤ 1`; the map takes values in `[-1, 1]`.
* W-shape and W-law also allow `c = 0` (empty window, `k ↦ -k`), which N2
  sets aside as row K.
* The sum is not normalised by `n - 1`.
* `n` is only assumed odd (N2 uses nothing else); W-x assumes
  `addOrderOf G = n` with `n` odd, not prime.
* In W-refined the symmetry is assumed only off the window; x-windows
  satisfy it everywhere.

Not claimed here:
* Row Wc (chords through `[s]G`, bound `2|c|`) at curve level: the chord
  geometry (`F(k) = F(-s - k)` off the pair `{s, -2s}`, the zeros at `s` and
  `2c`) is not stated. W-law gives the abstract bound once those properties
  of `F` are known.
* N2 (c), vacuity for `|c|` near `n/2`; the curve-level exact zero for
  `χ(x(Q) x(Q+G) x(Q+2G))` (there `c = -1`, so `W = {c, 2c}` and it follows
  from W-law since `F(c) = F(2c) = 0`, but the curve instance is not
  stated); the `O(|c|)` window law for `g` (row W, numerical only) and its
  conjectured exact value `4|c| - 3` (`HYPOTHESIS_TREE_2026_10_RU.md`,
  D4.1.2).
* The figures `ε ≤ 2^-253` for `|r| ≤ 8`, and all empirical claims of the
  row (13 units, 1515 checks, `chord.py` on 40 curves).
* W-x with a nonzero value of `Φ` at `O`: then `F(c) ≠ 0` in general and
  W-law gives only `2|r|`; this case is not stated separately.
-/

namespace Ecdlp.ParityFourier

open Finset

/-- The N2 window: `{1, …, 2c}` for `c > 0`, and `{2c, …, -1}` (as residues
`{n + 2c, …, n - 1}`) for `c ≤ 0`, which is empty for `c = 0`. -/
noncomputable def windowW (n : ℕ) (c : ℤ) : Finset (ZMod n) :=
  if 0 < c then (Icc (1 : ℤ) (2 * c)).image (fun m : ℤ => (m : ZMod n))
  else (Icc (2 * c) (-1)).image (fun m : ℤ => (m : ZMod n))

/-- W-shape (N2, bullets 1–3). The window has `2|c|` nonzero elements and contains `c` when
`c ≠ 0`; the reflection `k ↦ 2c - k` maps nonzero residues outside the window to nonzero
residues outside the window and flips `sgn`. -/
def WindowShape : Prop :=
  ∀ (n : ℕ) [NeZero n], Odd n → ∀ c : ℤ, 2 * |c| < n →
    (windowW n c).card = 2 * c.natAbs ∧ (0 : ZMod n) ∉ windowW n c ∧
    (c ≠ 0 → (c : ZMod n) ∈ windowW n c) ∧
    ∀ k : ZMod n, k ≠ 0 → k ∉ windowW n c →
      ((2 * c : ℤ) : ZMod n) - k ≠ 0 ∧ ((2 * c : ℤ) : ZMod n) - k ∉ windowW n c ∧
        sgn (((2 * c : ℤ) : ZMod n) - k) = - sgn k

/-- W-law (N2, general form). Exact identity, and the bound for `|F| ≤ 1`. -/
def WindowLaw : Prop :=
  ∀ (n : ℕ) [NeZero n], Odd n → ∀ c : ℤ, 2 * |c| < n → ∀ F : ZMod n → ℂ,
    (∑ k ∈ univ.erase (0 : ZMod n), F k * (sgn k : ℂ) =
      ∑ k ∈ windowW n c, F k * (sgn k : ℂ) +
        (1 / 2 : ℂ) * ∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c,
          (sgn k : ℂ) * (F k - F (((2 * c : ℤ) : ZMod n) - k))) ∧
    ((∀ k, ‖F k‖ ≤ 1) →
      ‖∑ k ∈ univ.erase (0 : ZMod n), F k * (sgn k : ℂ)‖ ≤
        (((windowW n c).filter (fun k => F k ≠ 0)).card : ℝ) +
          (1 / 2 : ℝ) * ∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c,
            ‖F k - F (((2 * c : ℤ) : ZMod n) - k)‖)

/-- W-refined (N2, instance (a), abstract form). A bounded `F`, symmetric under `k ↦ 2c - k`
off the window and zero at the centre `c`, has correlation at most `2|c| - 1` with `sgn`. -/
def WindowRefined : Prop :=
  ∀ (n : ℕ) [NeZero n], Odd n → ∀ c : ℤ, c ≠ 0 → 2 * |c| < n → ∀ F : ZMod n → ℂ,
    (∀ k, ‖F k‖ ≤ 1) → F (c : ZMod n) = 0 →
    (∀ k : ZMod n, k ≠ 0 → k ∉ windowW n c → F (((2 * c : ℤ) : ZMod n) - k) = F k) →
      ‖∑ k ∈ univ.erase (0 : ZMod n), F k * (sgn k : ℂ)‖ ≤ 2 * |(c : ℝ)| - 1

/-- W-x (row W). An x-window `Φ(x(Q + [r]G))`, `Q = [k]G`, `r ≠ 0`, with value `0` at `O`, has
correlation at most `2|r| - 1` with `sgn` over `k ≠ 0`. -/
def WindowX : Prop :=
  ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (G : W.toAffine.Point)
    (n : ℕ) [NeZero n], Odd n → addOrderOf G = n → ∀ r : ℤ, r ≠ 0 → 2 * |r| < n →
    ∀ Φ : K → ℂ, (∀ t, ‖Φ t‖ ≤ 1) →
      ‖∑ k ∈ univ.erase (0 : ZMod n), xFeature W Φ 0 (k.val • G + r • G) * (sgn k : ℂ)‖ ≤
        2 * |(r : ℝ)| - 1

end Ecdlp.ParityFourier
