import Ecdlp.Proved.ParityFourier.Statements
import Ecdlp.Proved.ParityFourier.StatementsWT

/-!
# Frozen statements Z (the finite-field Weierstrass zeta ζ_E; ROWX_ZETA_WEIL_NOTE)

This file fixes the statements; proof files must not edit it. Disclosure: a
scratch proof of Z1, of the coboundary, uniqueness and Miller-sum parts of
Z2, and of the `sgn` part of Z4 was compiled on 2026-10-22 (`ZetaFull.lean`,
sha256 27ca545340a2620985fbbd5e9dc5e21ec3d02b2f49fab00f33a5d0ee5ac018d3,
with precursor fragments of the same proofs in `Dev.lean`, `DevE.lean`,
`DevZ.lean`, `curve_part*.lean`, `ec_part.lean` and `zeta_part.lean`; scratch
files of session 3eaafce7, not in the repository) before this file was
written. Z3, the `J` and `g` parts of Z4, and the conjuncts `ζ_E(O) = 0`,
oddness and `∑ ζ_E = 0` of Z2 had no scratch proof (the scratch did contain
`lam_neg`, the slope identity behind oddness). The audit checks these
statements against the note, not against that proof.

Process note: for Z1, the coboundary, uniqueness and Miller-sum parts of Z2,
and the `sgn` part of Z4, a scratch proof was found before this file was
written (session 3eaafce7, 2026-10-22); the statement was audited against the
paper claim, not against the proof.

Setting: `W` is a short Weierstrass curve `y^2 = x^3 + a₄ x + a₆`
(`W.IsShortNF`) with `Δ ≠ 0` (`W.IsElliptic`) over a field `F`. Points are
Mathlib's `W.toAffine.Point` with Mathlib's group law.

* `slopeCocycle W P R` is the note's `λ(P, R)` (§1.2): Mathlib's slope on two
  affine points (chord `(y₁ - y₂)/(x₁ - x₂)`, tangent `(3x² + a₄)/(2y)`, and
  `0` for a vertical pair, i.e. when `R = -P`), and `0` when `P` or `R` is `O`.
  Short normal form is the note's setting, and the restriction is not
  cosmetic: with `a₁ ≠ 0` the vertical value `0` is in general not a cocycle
  (audit numerics: it fails on most such curves over `F₃`, `F₅` and `F₇`).
  With `a₁ = 0` and `a₂` or `a₃` nonzero the audit found no failure, but that
  case is not stated here.
* `zetaE W P = -(1/n) ∑_R λ(P, R)` with `n = #W(F)` (§1.4). Lean's
  `0⁻¹ = 0` makes it `0` when `n = 0` in `F`; the statements use `zetaE` only
  when `n` is a unit in `F`.

* Z1 (note L2.2): `λ` is a normalised symmetric 2-cocycle on all points.
* Z2 (note L3.1(a)(b)(c) and P4.1 in Miller-sum form): if `n` is a unit in
  `F`, then `ζ_E(P + Q) = ζ_E(P) + ζ_E(Q) + λ(P, Q)`; `ζ_E` is the unique
  function with this property; `ζ_E(O) = 0`, `ζ_E(-P) = -ζ_E(P)`,
  `∑_P ζ_E(P) = 0`; and `ζ_E(Q) = -(1/n) ∑_{i < n} λ([i]Q, Q)`.
* Z3 (note L3.2, homomorphism part only): if `n = 0` in `F`, then
  `ν(P) = ∑_R λ(P, R)` is additive. The nontriviality `A_p(Q) ≠ 0` is not
  stated.
* Z4 (note C6, conditional): on a curve over `ZMod p` of prime order `n ≠ p`
  with `G ≠ O`, IF every twisted sum of `k ↦ ζ_E([k]G)` with `a ≠ 0` is at
  most `2 sqrt p` (this is the note's T5, which is NOT proved here and rests
  on the Weil bound for generalized Jacobians), THEN the lowest bit of
  `ζ_E([k]G)` has the stated correlation bounds against `sgn`, `J` and `g`.
  Z4 is WT-lsb (`StatementsWT.lean`) and WT-J, WT-g (`StatementsCT.lean`)
  instantiated at `V k = ζ_E([k]G)`: the implication uses none of the curve
  hypotheses, which only make its hypothesis the note's T5. Its constants
  `(2 + log p) (2 + log n) ^ j` are weaker than the note's C6 figures, and
  the note's `half` bit is not stated.

Not claimed here:
* T5 itself and Theorem W are not stated or proved; Z4 is conditional on T5.
  Z4 adds no Lean content about `ζ_E` beyond tying that hypothesis to the
  formal definition, so it is not independent evidence about `ζ_E`. With
  `n ≈ p ≈ 2^256` its bounds give `ε ≤ 2^-113.03` (`sgn`), `2^-105.54` (`J`)
  and `2^-98.05` (`g`) in the note's normalisation, against the note's C6
  figures `2^-114.34`, `2^-107.51` and `2^-112.74`. By the audits'
  computation the bounds are below the trivial bound `n - 1` only for
  `p ≈ n` above about `2^17` (`sgn`), `2^28.8` (`J`) and `2^41.6` (`g`); at toy
  sizes they are trivially true and are not evidence. General targets
  `T : ZMod n → [-1, 1]` are not stated.
* From L3.1, part (d) (`E_λ ≅ E × F_p` and the character list) is not stated.
  Of P4.1 only the case `m = n` in Miller-sum form is stated: neither the
  general `A_m(Q) = ζ_E([m]Q) - m ζ_E(Q)` nor the function-field meaning
  `a(f_{n,Q})` is formalized.
* From L3.2 only the homomorphism step is stated: `A_p(Q) ≠ 0`, the order
  `p^2` of `(Q, 0)` in `E_λ`, the non-existence of `ζ` and `ν = A_p` are not.
* Curves that are not in short normal form are not covered.
-/

namespace Ecdlp.ParityFourier

open Finset WeierstrassCurve

/-- The slope cocycle `λ(P, R)` on points of a Weierstrass curve. -/
def slopeCocycle {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) :
    W.toAffine.Point → W.toAffine.Point → F
  | .some x₁ y₁ _, .some x₂ y₂ _ => W.toAffine.slope x₁ x₂ y₁ y₂
  | _, _ => 0

/-- The finite-field Weierstrass zeta `ζ_E(P) = -(1/n) ∑_R λ(P, R)`, `n = #W(F)`.
Lean's `0⁻¹ = 0` makes this `0` when `n = 0` in `F`; the statements use `zetaE` only when
`n` is a unit. -/
noncomputable def zetaE {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    [Fintype W.toAffine.Point] (P : W.toAffine.Point) : F :=
  -(Fintype.card W.toAffine.Point : F)⁻¹ * ∑ R, slopeCocycle W P R

/-- Z1. `λ` is a normalised symmetric 2-cocycle. -/
def SlopeCocycle : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] [W.IsShortNF]
    (P Q R : W.toAffine.Point),
      slopeCocycle W P Q + slopeCocycle W (P + Q) R =
          slopeCocycle W Q R + slopeCocycle W P (Q + R) ∧
        slopeCocycle W P Q = slopeCocycle W Q P ∧ slopeCocycle W 0 Q = 0

/-- Z2. Coboundary, uniqueness, symmetries and the Miller-sum form of `ζ_E`. -/
def ZetaCoboundary : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] [W.IsShortNF]
    [Fintype W.toAffine.Point], (Fintype.card W.toAffine.Point : F) ≠ 0 →
      (∀ P Q, zetaE W (P + Q) = zetaE W P + zetaE W Q + slopeCocycle W P Q) ∧
      (∀ z : W.toAffine.Point → F,
        (∀ P Q, z (P + Q) = z P + z Q + slopeCocycle W P Q) → z = zetaE W) ∧
      zetaE W 0 = 0 ∧ (∀ P, zetaE W (-P) = -zetaE W P) ∧ (∑ P, zetaE W P) = 0 ∧
      (∀ Q, zetaE W Q = -(Fintype.card W.toAffine.Point : F)⁻¹ *
        ∑ i ∈ range (Fintype.card W.toAffine.Point), slopeCocycle W (i • Q) Q)

/-- Z3. Anomalous case: when `n = 0` in `F`, `P ↦ ∑_R λ(P, R)` is additive. -/
def AnomalousSumHom : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] [W.IsShortNF]
    [Fintype W.toAffine.Point], (Fintype.card W.toAffine.Point : F) = 0 →
      ∀ P Q : W.toAffine.Point,
        ∑ R, slopeCocycle W (P + Q) R = ∑ R, slopeCocycle W P R + ∑ R, slopeCocycle W Q R

/-- Z4. Conditional on T5: lowest bit of `ζ_E([k]G)` against `sgn`, `J` and `g`. -/
def ZetaLsbTransfer : Prop :=
  ∀ (p n : ℕ) [NeZero p] [NeZero n] [Fact p.Prime] [Fact n.Prime], p ≠ 2 → n ≠ 2 → p ≠ n →
    ∀ (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] [W.IsShortNF] [Fintype W.toAffine.Point],
      Fintype.card W.toAffine.Point = n → ∀ G : W.toAffine.Point, G ≠ 0 →
      (∀ a : ZMod p, a ≠ 0 → ∀ α : ZMod n,
        ‖twistedSum (fun k : ZMod n => zetaE W (k.val • G)) a α‖ ≤ 2 * Real.sqrt p) →
      ‖∑ k ∈ univ.erase (0 : ZMod n), sigmaC (zetaE W (k.val • G)) * sigmaC k‖ ≤
          2 * Real.sqrt p * (2 + Real.log p) * (2 + Real.log n) ∧
      (∀ lam : ZMod n,
        ‖∑ k ∈ univ.erase (0 : ZMod n), sigmaC (zetaE W (k.val • G)) * JC lam k‖ ≤
          ((n : ℝ) - 1) / p + 2 * Real.sqrt p * (2 + Real.log p) * (2 + Real.log n) ^ 2) ∧
      (∀ lam : ZMod n, lam ^ 2 + lam + 1 = 0 →
        ‖∑ k ∈ univ.erase (0 : ZMod n), sigmaC (zetaE W (k.val • G)) * (g lam k : ℂ)‖ ≤
          2 * Real.sqrt p * (2 + Real.log p) * (2 + Real.log n) ^ 3)

end Ecdlp.ParityFourier
