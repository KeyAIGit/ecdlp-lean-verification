import Ecdlp.Proved.ParityFourier.StatementsZeta
import Ecdlp.Proved.ParityFourier.ProofsWT
import Ecdlp.Proved.ParityFourier.ProofsCT

/-!
# Proofs of Z (the finite-field Weierstrass zeta; ROWX_ZETA_WEIL_NOTE)

Proves the frozen statements `Ecdlp.ParityFourier.SlopeCocycle`, `Ecdlp.ParityFourier.ZetaCoboundary`,
`Ecdlp.ParityFourier.AnomalousSumHom` and `Ecdlp.ParityFourier.ZetaLsbTransfer` from
`Ecdlp.Proved.ParityFourier.StatementsZeta`.

Outline (short normal form `y² = x³ + a₄ x + a₆`, `Δ ≠ 0`, so `2 ≠ 0`):
1. `uniform_core8`: a polynomial certificate (one `linear_combination`) shows that four
   slopes `l, m, r, s` characterised only by the chord-or-tangent relations satisfy
   `8 Δ' (l + r - m - s) = 0`, with `Δ' = 4 a₄³ + 27 a₆²`; `uniform` divides by `8 Δ'`;
2. Z1: symmetry of Mathlib's slope, the third-point identity `λ(A, B) = λ(A, -(A + B))`,
   `λ(-P, -Q) = -λ(P, Q)`, and a case split on which partial sums vanish reduce the
   cocycle identity to `uniform`;
3. Z2: summing the cocycle identity over `R` gives the coboundary formula for
   `ζ_E = -(1/n) ∑_R λ(·, R)` when `n` is a unit; two solutions differ by a homomorphism
   killed by `n`; telescoping gives the Miller sum; `ζ_E(O) = 0` by definition,
   oddness from `λ(-P, -R) = -λ(P, R)` and reindexing `R ↦ -R`, and `∑ ζ_E = 0` from
   oddness and `2 ≠ 0`;
4. Z3: the same summed identity with `n = 0` in `F` is additivity of `∑_R λ(·, R)`;
5. Z4: `ProofsWT.weilTransferLsb`, `ProofsCT.weilTransferLsbJ` and
   `ProofsCT.weilTransferLsbG` at `V k = ζ_E([k]G)`.

The certificate in `uniform_core8` needs a raised, finite heartbeat limit (it elaborates
at 1000000; the cap is 2000000).

Provenance: `uniform_core8`, `uniform`, the curve lemmas behind Z1, and the coboundary,
uniqueness and Miller-sum steps of Z2 are ported from the scratch file `ZetaFull.lean`
(session 3eaafce7, disclosed in `StatementsZeta.lean`), with `lam` renamed to the frozen
`slopeCocycle`. The `sgn` part of Z4 is the scratch one-liner. `ζ_E(O) = 0`, oddness,
`∑ ζ_E = 0`, Z3 and the `J` and `g` parts of Z4 are new here.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Ecdlp.ParityFourier.ProofsZeta

open Ecdlp.ParityFourier Finset WeierstrassCurve WeierstrassCurve.Affine

section Algebra

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
/-- Uniform (chord-or-tangent) cocycle core, short Weierstrass, after substituting
`y2`, `y3`, `b`. Slopes `l, m, r, s` are characterised by the U-relations only. -/
theorem uniform_core8 {F : Type*} [Field F] (a y1 x1 x2 x3 l m r s : F)
    (u2 : 2*l*y1 + l^2*(x2 - x1) = x1^2 + x1*x2 + x2^2 + a)
    (v2 : 2*m*(y1 + l*(x2 - x1)) + m^2*(x3 - x2) = x2^2 + x2*x3 + x3^2 + a)
    (w1 : (y1 + l*(x2 - x1)) + m*(x3 - x2)
        = (l*(x1 - (l^2 - x1 - x2)) - y1) + r*(x3 - (l^2 - x1 - x2)))
    (w2 : 2*r*(l*(x1 - (l^2 - x1 - x2)) - y1) + r^2*(x3 - (l^2 - x1 - x2))
        = (l^2 - x1 - x2)^2 + (l^2 - x1 - x2)*x3 + x3^2 + a)
    (z1 : m*(x2 - (m^2 - x2 - x3)) - (y1 + l*(x2 - x1)) = y1 + s*((m^2 - x2 - x3) - x1))
    (z2 : 2*s*y1 + s^2*((m^2 - x2 - x3) - x1) = x1^2 + x1*(m^2 - x2 - x3) + (m^2 - x2 - x3)^2 + a) :
    8 * (4*a^3 + 27*(y1^2 - x1^3 - a*x1)^2) * (l + r - m - s) = 0 := by
  linear_combination (-18*l^2*m*x1^3 - 18*l*m^2*x1^3 - 54*m^3*x1^3 - 54*l*m*r*x1^3 - 54*m^2*r*x1^3 - 18*l^2*s*x1^3 - 18*l*m*s*x1^3 - 54*m^2*s*x1^3 - 54*l*r*s*x1^3 - 54*m*r*s*x1^3 - 12*l^2*m^2*y1*x3 - 12*l*m^3*y1*x3 - 36*m^4*y1*x3 - 36*l*m^2*r*y1*x3 - 36*m^3*r*y1*x3 - 12*l^2*m*s*y1*x3 - 12*l*m^2*s*y1*x3 - 36*m^3*s*y1*x3 - 36*l*m*r*s*y1*x3 - 36*m^2*r*s*y1*x3 - 72*l^2*m*x1^2*x3 - 72*l*m^2*x1^2*x3 - 72*l^2*s*x1^2*x3 - 72*l*m*s*x1^2*x3 - 72*l^2*m*x1*x3^2 - 72*l*m^2*x1*x3^2 - 72*l^2*s*x1*x3^2 - 72*l*m*s*x1*x3^2 + 72*l^2*m*x2*x3^2 + 72*l*m^2*x2*x3^2 + 72*l^2*s*x2*x3^2 + 72*l*m*s*x2*x3^2 - 72*l^2*m*x3^3 - 72*l*m^2*x3^3 + 72*m^3*x3^3 + 72*l*m*r*x3^3 + 72*m^2*r*x3^3 - 72*l^2*s*x3^3 - 72*l*m*s*x3^3 + 72*m^2*s*x3^3 + 72*l*r*s*x3^3 + 72*m*r*s*x3^3 + 18*l^2*m*y1^2 + 18*l*m^2*y1^2 + 54*m^3*y1^2 + 54*l*m*r*y1^2 + 54*m^2*r*y1^2 + 18*l^2*s*y1^2 + 18*l*m*s*y1^2 + 54*m^2*s*y1^2 + 54*l*r*s*y1^2 + 54*m*r*s*y1^2 - 66*l^2*m*a*x1 - 66*l*m^2*a*x1 - 54*m^3*a*x1 - 54*l*m*r*a*x1 - 54*m^2*r*a*x1 - 66*l^2*s*a*x1 - 66*l*m*s*a*x1 - 54*m^2*s*a*x1 - 54*l*r*s*a*x1 - 54*m*r*s*a*x1 - 252*l*x1^4 + 90*m*x1^4 - 162*r*x1^4 + 144*s*x1^4 + 96*l^2*m*a*x2 + 96*l*m^2*a*x2 + 96*l^2*s*a*x2 + 96*l*m*s*a*x2 + 36*l*x1^3*x2 - 153*m*x1^3*x2 + 135*r*x1^3*x2 - 90*s*x1^3*x2 + 144*l*x1^2*x2^2 + 144*r*x1^2*x2^2 + 72*s*x1^2*x2^2 - 84*l^2*m*a*x3 - 84*l*m^2*a*x3 + 60*m^3*a*x3 + 60*l*m*r*a*x3 + 60*m^2*r*a*x3 - 84*l^2*s*a*x3 - 84*l*m*s*a*x3 + 60*m^2*s*a*x3 + 60*l*r*s*a*x3 + 60*m*r*s*a*x3 + 120*l*m*y1*x1*x3 + 252*m^2*y1*x1*x3 + 24*l*r*y1*x1*x3 + 36*m*r*y1*x1*x3 + 120*l*s*y1*x1*x3 + 288*m*s*y1*x1*x3 - 72*l*x1^3*x3 + 81*m*x1^3*x3 - 45*r*x1^3*x3 - 36*s*x1^3*x3 + 24*l^2*y1*x2*x3 - 72*l*m*y1*x2*x3 - 102*m^2*y1*x2*x3 + 24*l*r*y1*x2*x3 - 30*m*r*y1*x2*x3 - 24*l*s*y1*x2*x3 - 108*m*s*y1*x2*x3 + 72*l*x1^2*x2*x3 + 180*m*x1^2*x2*x3 - 108*r*x1^2*x2*x3 + 144*s*x1^2*x2*x3 - 72*l^2*y1*x3^2 - 42*m^2*y1*x3^2 - 96*l*r*y1*x3^2 - 6*m*r*y1*x3^2 - 48*l*s*y1*x3^2 - 72*m*s*y1*x3^2 + 240*l*x1^2*x3^2 + 228*m*x1^2*x3^2 + 12*r*x1^2*x3^2 + 192*s*x1^2*x3^2 + 120*l*x1*x2*x3^2 + 216*m*x1*x2*x3^2 - 96*r*x1*x2*x3^2 + 96*s*x1*x2*x3^2 - 360*l*x2^2*x3^2 - 108*m*x2^2*x3^2 - 252*r*x2^2*x3^2 - 288*s*x2^2*x3^2 + 120*l*x1*x3^3 - 96*m*x1*x3^3 + 72*r*x1*x3^3 - 48*s*x1*x3^3 - 120*l*x2*x3^3 - 180*m*x2*x3^3 + 132*r*x2*x3^3 - 24*s*x2*x3^3 - 240*m*x3^4 + 96*r*x3^4 - 144*s*x3^4 - 64*l^2*y1*a - 56*l*m*y1*a - 120*m^2*y1*a - 64*l*r*y1*a - 56*l*s*y1*a - 120*m*s*y1*a + 252*l*y1^2*x1 - 90*m*y1^2*x1 + 162*r*y1^2*x1 - 144*s*y1^2*x1 + 44*l*a*x1^2 + 370*m*a*x1^2 - 98*r*a*x1^2 + 424*s*a*x1^2 + 18*y1*x1^3 - 180*l*y1^2*x2 + 81*m*y1^2*x2 - 207*r*y1^2*x2 + 18*s*y1^2*x2 + 124*l*a*x1*x2 + 147*m*a*x1*x2 - 77*r*a*x1*x2 + 38*s*a*x1*x2 + 144*y1*x1^2*x2 - 288*l*a*x2^2 - 144*m*a*x2^2 - 144*r*a*x2^2 - 288*s*a*x2^2 - 165*m*y1^2*x3 + 45*r*y1^2*x3 - 36*s*y1^2*x3 + 88*l*a*x1*x3 + 49*m*a*x1*x3 + 27*r*a*x1*x3 + 44*s*a*x1*x3 + 96*y1*x1^2*x3 - 88*l*a*x2*x3 - 126*m*a*x2*x3 + 98*r*a*x2*x3 + 4*s*a*x2*x3 - 192*y1*x1*x2*x3 + 72*y1*x2^2*x3 - 194*m*a*x3^2 + 74*r*a*x3^2 - 120*s*a*x3^2 - 168*y1*x1*x3^2 - 384*y1*x2*x3^2 + 72*y1*x3^3 - 18*y1^3 - 32*l*a^2 + 32*m*a^2 - 32*r*a^2 + 32*s*a^2 - 254*y1*a*x1 - 360*y1*a*x2 + 68*y1*a*x3) * u2 + (-54*l^2*m*x1^3 - 54*l*m*r*x1^3 - 54*m^2*r*x1^3 + 54*l^2*s*x1^3 + 54*l*m*s*x1^3 + 54*l*r*s*x1^3 + 54*m*r*s*x1^3 - 72*l^2*m*x1^2*x2 - 72*l*m*r*x1^2*x2 + 12*l^2*m^2*y1*x3 + 12*l*m^2*r*y1*x3 - 36*m^3*r*y1*x3 + 36*l^2*m*s*y1*x3 + 36*l*m^2*s*y1*x3 + 36*l*m*r*s*y1*x3 + 36*m^2*r*s*y1*x3 - 24*l^2*m*x1*x3^2 - 24*l*m*r*x1*x3^2 + 144*l^2*m*x2*x3^2 + 144*l*m*r*x2*x3^2 - 192*l^2*m*x3^3 - 192*l*m*r*x3^3 + 72*m^2*r*x3^3 - 72*l^2*s*x3^3 - 72*l*m*s*x3^3 - 72*l*r*s*x3^3 - 72*m*r*s*x3^3 + 54*l^2*m*y1^2 + 54*l*m*r*y1^2 + 54*m^2*r*y1^2 - 54*l^2*s*y1^2 - 54*l*m*s*y1^2 - 54*l*r*s*y1^2 - 54*m*r*s*y1^2 + 10*l^2*m*a*x1 + 10*l*m*r*a*x1 - 54*m^2*r*a*x1 + 54*l^2*s*a*x1 + 54*l*m*s*a*x1 + 54*l*r*s*a*x1 + 54*m*r*s*a*x1 - 108*l*x1^4 - 54*r*x1^4 + 54*s*x1^4 + 96*l^2*m*a*x2 + 96*l*m*r*a*x2 - 117*l*x1^3*x2 + 162*m*x1^3*x2 - 63*r*x1^3*x2 + 72*s*x1^3*x2 - 72*l*x1^2*x2^2 - 72*r*x1^2*x2^2 - 72*s*x1^2*x2^2 - 172*l^2*m*a*x3 - 172*l*m*r*a*x3 + 60*m^2*r*a*x3 - 60*l^2*s*a*x3 - 60*l*m*s*a*x3 - 60*l*r*s*a*x3 - 60*m*r*s*a*x3 + 48*m^2*y1*x1*x3 + 36*m*r*y1*x1*x3 - 24*l*s*y1*x1*x3 - 108*m*s*y1*x1*x3 - 9*l*x1^3*x3 - 90*m*x1^3*x3 + 45*r*x1^3*x3 - 54*s*x1^3*x3 + 24*l^2*y1*x2*x3 + 42*l*m*y1*x2*x3 + 12*m^2*y1*x2*x3 + 24*l*r*y1*x2*x3 + 78*m*r*y1*x2*x3 + 24*l*s*y1*x2*x3 + 96*m*s*y1*x2*x3 - 36*l*x1^2*x2*x3 - 144*m*x1^2*x2*x3 - 36*r*x1^2*x2*x3 + 18*l*m*y1*x3^2 - 108*m^2*y1*x3^2 + 54*m*r*y1*x3^2 + 48*l*s*y1*x3^2 + 60*m*s*y1*x3^2 - 60*l*x1^2*x3^2 + 96*m*x1^2*x3^2 - 60*r*x1^2*x3^2 + 24*s*x1^2*x3^2 - 96*l*x1*x2*x3^2 - 288*m*x1*x2*x3^2 - 24*r*x1*x2*x3^2 - 168*s*x1*x2*x3^2 + 108*l*x2^2*x3^2 + 72*m*x2^2*x3^2 + 108*r*x2^2*x3^2 + 144*s*x2^2*x3^2 - 72*l*x1*x3^3 + 240*m*x1*x3^3 - 72*r*x1*x3^3 + 192*s*x1*x3^3 - 156*l*x2*x3^3 - 72*m*x2*x3^3 - 300*r*x2*x3^3 - 264*s*x2*x3^3 - 48*l*x3^4 - 48*m*x3^4 - 120*r*x3^4 + 72*s*x3^4 - 64*l^2*y1*a - 64*l*m*y1*a - 64*m^2*y1*a - 64*l*r*y1*a - 64*m*r*y1*a + 64*l*s*y1*a + 64*m*s*y1*a + 108*l*y1^2*x1 + 54*r*y1^2*x1 - 54*s*y1^2*x1 - 44*l*a*x1^2 - 64*m*a*x1^2 + 10*r*a*x1^2 - 10*s*a*x1^2 + 45*l*y1^2*x2 - 90*m*y1^2*x2 - 9*r*y1^2*x2 - 89*l*a*x1*x2 - 150*m*a*x1*x2 + 61*r*a*x1*x2 - 32*s*a*x1*x2 + 48*l*a*x2^2 + 96*m*a*x2^2 + 48*r*a*x2^2 + 96*s*a*x2^2 + 81*l*y1^2*x3 + 162*m*y1^2*x3 + 27*r*y1^2*x3 - 18*s*y1^2*x3 - 45*l*a*x1*x3 + 158*m*a*x1*x3 + 45*r*a*x1*x3 + 118*s*a*x1*x3 + 24*y1*x1^2*x3 - 118*l*a*x2*x3 - 108*m*a*x2*x3 - 274*r*a*x2*x3 - 232*s*a*x2*x3 - 144*y1*x1*x2*x3 + 48*y1*x2^2*x3 - 70*l*a*x3^2 - 52*m*a*x3^2 - 106*r*a*x3^2 + 60*s*a*x3^2 + 24*y1*x1*x3^2 + 192*y1*x2*x3^2 + 72*y1*x3^3 - 32*l*a^2 - 32*m*a^2 + 120*y1*a*x2 + 96*y1*a*x3) * v2 + (-36*l^3*m*x1^3 - 36*l^2*m^2*x1^3 - 36*l^2*m*r*x1^3 - 36*l*m^2*r*x1^3 - 36*l^3*s*x1^3 - 36*l^2*m*s*x1^3 - 36*l^2*r*s*x1^3 - 36*l*m*r*s*x1^3 - 24*l^3*m^2*y1*x3 - 24*l^2*m^3*y1*x3 - 24*l^2*m^2*r*y1*x3 - 24*l*m^3*r*y1*x3 - 24*l^3*m*s*y1*x3 - 24*l^2*m^2*s*y1*x3 - 24*l^2*m*r*s*y1*x3 - 24*l*m^2*r*s*y1*x3 + 72*l^3*m*x1^2*x3 + 72*l^2*m^2*x1^2*x3 + 72*l^2*m*r*x1^2*x3 + 72*l*m^2*r*x1^2*x3 + 72*l^3*s*x1^2*x3 + 72*l^2*m*s*x1^2*x3 + 72*l^2*r*s*x1^2*x3 + 72*l*m*r*s*x1^2*x3 + 72*l^3*m*x1*x3^2 + 72*l^2*m^2*x1*x3^2 + 72*l^2*m*r*x1*x3^2 + 72*l*m^2*r*x1*x3^2 + 72*l^3*s*x1*x3^2 + 72*l^2*m*s*x1*x3^2 + 72*l^2*r*s*x1*x3^2 + 72*l*m*r*s*x1*x3^2 - 72*l^3*m*x2*x3^2 - 72*l^2*m^2*x2*x3^2 - 72*l^2*m*r*x2*x3^2 - 72*l*m^2*r*x2*x3^2 - 72*l^3*s*x2*x3^2 - 72*l^2*m*s*x2*x3^2 - 72*l^2*r*s*x2*x3^2 - 72*l*m*r*s*x2*x3^2 + 144*l^3*m*x3^3 + 144*l^2*m^2*x3^3 + 144*l^2*m*r*x3^3 + 144*l*m^2*r*x3^3 + 144*l^3*s*x3^3 + 144*l^2*m*s*x3^3 + 144*l^2*r*s*x3^3 + 144*l*m*r*s*x3^3 + 36*l^3*m*y1^2 + 36*l^2*m^2*y1^2 + 36*l^2*m*r*y1^2 + 36*l*m^2*r*y1^2 + 36*l^3*s*y1^2 + 36*l^2*m*s*y1^2 + 36*l^2*r*s*y1^2 + 36*l*m*r*s*y1^2 + 12*l^3*m*a*x1 + 12*l^2*m^2*a*x1 + 12*l^2*m*r*a*x1 + 12*l*m^2*r*a*x1 + 12*l^3*s*a*x1 + 12*l^2*m*s*a*x1 + 12*l^2*r*s*a*x1 + 12*l*m*r*s*a*x1 + 90*l^2*x1^4 + 18*l*m*x1^4 - 54*m^2*x1^4 + 90*l*r*x1^4 + 72*m*r*x1^4 + 18*l*s*x1^4 - 54*m*s*x1^4 + 72*r*s*x1^4 - 96*l^3*m*a*x2 - 96*l^2*m^2*a*x2 - 96*l^2*m*r*a*x2 - 96*l*m^2*r*a*x2 - 96*l^3*s*a*x2 - 96*l^2*m*s*a*x2 - 96*l^2*r*s*a*x2 - 96*l*m*r*s*a*x2 + 99*l^2*x1^3*x2 + 207*l*m*x1^3*x2 - 18*m^2*x1^3*x2 + 99*l*r*x1^3*x2 + 117*m*r*x1^3*x2 + 90*l*s*x1^3*x2 - 18*m*s*x1^3*x2 + 72*m^2*x1^2*x2^2 - 72*l*s*x1^2*x2^2 + 72*m*s*x1^2*x2^2 - 72*r*s*x1^2*x2^2 + 144*l^3*m*a*x3 + 144*l^2*m^2*a*x3 + 144*l^2*m*r*a*x3 + 144*l*m^2*r*a*x3 + 144*l^3*s*a*x3 + 144*l^2*m*s*a*x3 + 144*l^2*r*s*a*x3 + 144*l*m*r*s*a*x3 + 24*l^3*y1*x1*x3 - 84*l^2*m*y1*x1*x3 - 156*l*m^2*y1*x1*x3 + 12*m^3*y1*x1*x3 + 24*l^2*r*y1*x1*x3 - 84*l*m*r*y1*x1*x3 - 120*m^2*r*y1*x1*x3 - 120*l^2*s*y1*x1*x3 - 156*l*m*s*y1*x1*x3 + 12*m^2*s*y1*x1*x3 - 120*l*r*s*y1*x1*x3 - 120*m*r*s*y1*x1*x3 + 27*l^2*x1^3*x3 - 81*l*m*x1^3*x3 + 27*l*r*x1^3*x3 - 45*m*r*x1^3*x3 + 36*l*s*x1^3*x3 + 72*r*s*x1^3*x3 + 42*l^2*m*y1*x2*x3 + 114*l*m^2*y1*x2*x3 - 12*m^3*y1*x2*x3 + 42*l*m*r*y1*x2*x3 + 54*m^2*r*y1*x2*x3 + 24*l^2*s*y1*x2*x3 + 84*l*m*s*y1*x2*x3 - 12*m^2*s*y1*x2*x3 + 24*l*r*s*y1*x2*x3 + 24*m*r*s*y1*x2*x3 - 180*l^2*x1^2*x2*x3 - 180*l*m*x1^2*x2*x3 - 180*l*r*x1^2*x2*x3 - 108*m*r*x1^2*x2*x3 - 144*l*s*x1^2*x2*x3 - 72*r*s*x1^2*x2*x3 - 24*l^3*y1*x3^2 - 6*l^2*m*y1*x3^2 - 6*l*m^2*y1*x3^2 - 24*l^2*r*y1*x3^2 - 6*l*m*r*y1*x3^2 + 18*m^2*r*y1*x3^2 + 48*l^2*s*y1*x3^2 + 24*l*m*s*y1*x3^2 + 48*l*r*s*y1*x3^2 + 48*m*r*s*y1*x3^2 - 228*l^2*x1^2*x3^2 - 228*l*m*x1^2*x3^2 - 24*m^2*x1^2*x3^2 - 228*l*r*x1^2*x3^2 - 300*m*r*x1^2*x3^2 - 192*l*s*x1^2*x3^2 - 24*m*s*x1^2*x3^2 - 264*r*s*x1^2*x3^2 - 216*l^2*x1*x2*x3^2 - 144*l*m*x1*x2*x3^2 + 168*m^2*x1*x2*x3^2 - 216*l*r*x1*x2*x3^2 - 72*m*r*x1*x2*x3^2 - 24*l*s*x1*x2*x3^2 + 168*m*s*x1*x2*x3^2 + 48*r*s*x1*x2*x3^2 + 108*l^2*x2^2*x3^2 + 108*l*m*x2^2*x3^2 - 144*m^2*x2^2*x3^2 + 108*l*r*x2^2*x3^2 + 36*m*r*x2^2*x3^2 + 288*l*s*x2^2*x3^2 - 144*m*s*x2^2*x3^2 + 216*r*s*x2^2*x3^2 - 48*l^2*x1*x3^3 + 24*l*m*x1*x3^3 - 192*m^2*x1*x3^3 - 48*l*r*x1*x3^3 - 120*m*r*x1*x3^3 - 96*l*s*x1*x3^3 - 192*m*s*x1*x3^3 - 240*r*s*x1*x3^3 + 252*l^2*x2*x3^3 + 36*l*m*x2*x3^3 + 192*m^2*x2*x3^3 + 252*l*r*x2*x3^3 + 324*m*r*x2*x3^3 - 48*l*s*x2*x3^3 + 192*m*s*x2*x3^3 + 240*r*s*x2*x3^3 + 96*l^2*x3^4 + 240*l*m*x3^4 + 96*l*r*x3^4 + 96*m*r*x3^4 + 144*l*s*x3^4 + 56*l^2*m*y1*a + 56*l*m^2*y1*a + 56*l*m*r*y1*a + 56*m^2*r*y1*a + 56*l^2*s*y1*a + 56*l*m*s*y1*a + 56*l*r*s*y1*a + 56*m*r*s*y1*a - 90*l^2*y1^2*x1 - 18*l*m*y1^2*x1 + 54*m^2*y1^2*x1 - 90*l*r*y1^2*x1 - 72*m*r*y1^2*x1 - 18*l*s*y1^2*x1 + 54*m*s*y1^2*x1 - 72*r*s*y1^2*x1 - 142*l^2*a*x1^2 - 262*l*m*a*x1^2 + 10*m^2*a*x1^2 - 142*l*r*a*x1^2 - 208*m*r*a*x1^2 - 262*l*s*a*x1^2 + 10*m*s*a*x1^2 - 208*r*s*a*x1^2 - 126*l*y1*x1^3 + 108*m*y1*x1^3 - 126*r*y1*x1^3 + 108*s*y1*x1^3 - 54*x1^5 - 27*l^2*y1^2*x2 - 135*l*m*y1^2*x2 - 54*m^2*y1^2*x2 - 27*l*r*y1^2*x2 - 45*m*r*y1^2*x2 - 18*l*s*y1^2*x2 - 54*m*s*y1^2*x2 + 72*r*s*y1^2*x2 - 201*l^2*a*x1*x2 + 3*l*m*a*x1*x2 + 86*m^2*a*x1*x2 - 201*l*r*a*x1*x2 - 39*m*r*a*x1*x2 + 58*l*s*a*x1*x2 + 86*m*s*a*x1*x2 + 16*r*s*a*x1*x2 - 144*l*y1*x1^2*x2 - 144*r*y1*x1^2*x2 + 81*x1^4*x2 + 144*l^2*a*x2^2 + 144*l*m*a*x2^2 - 96*m^2*a*x2^2 + 144*l*r*a*x2^2 + 48*m*r*a*x2^2 + 288*l*s*a*x2^2 - 96*m*s*a*x2^2 + 192*r*s*a*x2^2 - 144*x1^3*x2^2 - 72*x1^2*x2^3 + 45*l^2*y1^2*x3 + 93*l*m*y1^2*x3 + 72*m^2*y1^2*x3 + 45*l*r*y1^2*x3 + 57*m*r*y1^2*x3 + 36*l*s*y1^2*x3 + 72*m*s*y1^2*x3 - 61*l^2*a*x1*x3 - 73*l*m*a*x1*x3 - 172*m^2*a*x1*x3 - 61*l*r*a*x1*x3 - 145*m*r*a*x1*x3 - 128*l*s*a*x1*x3 - 172*m*s*a*x1*x3 - 200*r*s*a*x1*x3 - 96*l*y1*x1^2*x3 + 36*m*y1*x1^2*x3 - 120*r*y1*x1^2*x3 + 24*s*y1*x1^2*x3 + 27*x1^4*x3 + 186*l^2*a*x2*x3 - 30*l*m*a*x2*x3 + 172*m^2*a*x2*x3 + 186*l*r*a*x2*x3 + 270*m*r*a*x2*x3 - 100*l*s*a*x2*x3 + 172*m*s*a*x2*x3 + 200*r*s*a*x2*x3 + 144*l*y1*x1*x2*x3 + 54*m*y1*x1*x2*x3 + 168*r*y1*x1*x2*x3 + 120*s*y1*x1*x2*x3 + 99*x1^3*x2*x3 - 72*l*y1*x2^2*x3 - 24*m*y1*x2^2*x3 - 48*r*y1*x2^2*x3 - 48*s*y1*x2^2*x3 + 216*x1^2*x2^2*x3 + 74*l^2*a*x3^2 + 218*l*m*a*x3^2 + 74*l*r*a*x3^2 + 74*m*r*a*x3^2 + 144*l*s*a*x3^2 + 216*l*y1*x1*x3^2 - 102*m*y1*x1*x3^2 + 288*r*y1*x1*x3^2 - 144*s*y1*x1*x3^2 - 9*x1^3*x3^2 + 432*l*y1*x2*x3^2 + 18*m*y1*x2*x3^2 + 312*r*y1*x2*x3^2 - 108*x1^2*x2*x3^2 + 228*x1*x2^2*x3^2 + 72*x2^3*x3^2 + 24*l*y1*x3^3 - 126*m*y1*x3^3 + 48*r*y1*x3^3 - 96*s*y1*x3^3 - 108*x1^2*x3^3 - 132*x1*x2*x3^3 - 300*x2^2*x3^3 - 24*x1*x3^4 + 132*x2*x3^4 + 96*x3^5 + 126*l*y1^3 - 108*m*y1^3 + 126*r*y1^3 - 108*s*y1^3 + 146*l*y1*a*x1 + 44*m*y1*a*x1 + 210*r*y1*a*x1 + 44*s*y1*a*x1 + 54*y1^2*x1^2 - 54*a*x1^3 + 360*l*y1*a*x2 + 8*m*y1*a*x2 + 296*r*y1*a*x2 + 8*s*y1*a*x2 - 81*y1^2*x1*x2 + 45*a*x1^2*x2 + 144*y1^2*x2^2 + 208*a*x1*x2^2 + 52*l*y1*a*x3 - 64*m*y1*a*x3 + 52*r*y1*a*x3 - 64*s*y1*a*x3 - 75*y1^2*x1*x3 - 69*a*x1^2*x3 - 183*y1^2*x2*x3 - 47*a*x1*x2*x3 - 208*a*x2^2*x3 + 237*y1^2*x3^2 - 71*a*x1*x3^2 + 122*a*x2*x3^2 + 74*a*x3^3 + 128*y1^2*a - 32*a^2*x1 + 32*a^2*x2) * w1 + (-36*l^2*m*x1^3 - 36*l*m^2*x1^3 - 36*l^2*s*x1^3 - 36*l*m*s*x1^3 - 24*l^2*m^2*y1*x3 - 24*l*m^3*y1*x3 - 24*l^2*m*s*y1*x3 - 24*l*m^2*s*y1*x3 + 72*l^2*m*x1^2*x3 + 72*l*m^2*x1^2*x3 + 72*l^2*s*x1^2*x3 + 72*l*m*s*x1^2*x3 + 72*l^2*m*x1*x3^2 + 72*l*m^2*x1*x3^2 + 72*l^2*s*x1*x3^2 + 72*l*m*s*x1*x3^2 - 72*l^2*m*x2*x3^2 - 72*l*m^2*x2*x3^2 - 72*l^2*s*x2*x3^2 - 72*l*m*s*x2*x3^2 + 144*l^2*m*x3^3 + 144*l*m^2*x3^3 + 144*l^2*s*x3^3 + 144*l*m*s*x3^3 + 36*l^2*m*y1^2 + 36*l*m^2*y1^2 + 36*l^2*s*y1^2 + 36*l*m*s*y1^2 + 12*l^2*m*a*x1 + 12*l*m^2*a*x1 + 12*l^2*s*a*x1 + 12*l*m*s*a*x1 + 90*l*x1^4 + 72*m*x1^4 + 72*s*x1^4 - 96*l^2*m*a*x2 - 96*l*m^2*a*x2 - 96*l^2*s*a*x2 - 96*l*m*s*a*x2 + 99*l*x1^3*x2 + 117*m*x1^3*x2 - 72*s*x1^2*x2^2 + 144*l^2*m*a*x3 + 144*l*m^2*a*x3 + 144*l^2*s*a*x3 + 144*l*m*s*a*x3 + 24*l^2*y1*x1*x3 - 84*l*m*y1*x1*x3 - 120*m^2*y1*x1*x3 - 120*l*s*y1*x1*x3 - 120*m*s*y1*x1*x3 + 27*l*x1^3*x3 - 45*m*x1^3*x3 + 72*s*x1^3*x3 + 42*l*m*y1*x2*x3 + 54*m^2*y1*x2*x3 + 24*l*s*y1*x2*x3 + 24*m*s*y1*x2*x3 - 180*l*x1^2*x2*x3 - 108*m*x1^2*x2*x3 - 72*s*x1^2*x2*x3 - 24*l^2*y1*x3^2 - 6*l*m*y1*x3^2 + 18*m^2*y1*x3^2 + 48*l*s*y1*x3^2 + 48*m*s*y1*x3^2 - 228*l*x1^2*x3^2 - 300*m*x1^2*x3^2 - 264*s*x1^2*x3^2 - 216*l*x1*x2*x3^2 - 72*m*x1*x2*x3^2 + 48*s*x1*x2*x3^2 + 108*l*x2^2*x3^2 + 36*m*x2^2*x3^2 + 216*s*x2^2*x3^2 - 48*l*x1*x3^3 - 120*m*x1*x3^3 - 240*s*x1*x3^3 + 252*l*x2*x3^3 + 324*m*x2*x3^3 + 240*s*x2*x3^3 + 96*l*x3^4 + 96*m*x3^4 + 56*l*m*y1*a + 56*m^2*y1*a + 56*l*s*y1*a + 56*m*s*y1*a - 90*l*y1^2*x1 - 72*m*y1^2*x1 - 72*s*y1^2*x1 - 142*l*a*x1^2 - 208*m*a*x1^2 - 208*s*a*x1^2 - 126*y1*x1^3 - 27*l*y1^2*x2 - 45*m*y1^2*x2 + 72*s*y1^2*x2 - 201*l*a*x1*x2 - 39*m*a*x1*x2 + 16*s*a*x1*x2 - 144*y1*x1^2*x2 + 144*l*a*x2^2 + 48*m*a*x2^2 + 192*s*a*x2^2 + 45*l*y1^2*x3 + 57*m*y1^2*x3 - 61*l*a*x1*x3 - 145*m*a*x1*x3 - 200*s*a*x1*x3 - 120*y1*x1^2*x3 + 186*l*a*x2*x3 + 270*m*a*x2*x3 + 200*s*a*x2*x3 + 168*y1*x1*x2*x3 - 48*y1*x2^2*x3 + 74*l*a*x3^2 + 74*m*a*x3^2 + 288*y1*x1*x3^2 + 312*y1*x2*x3^2 + 48*y1*x3^3 + 126*y1^3 + 210*y1*a*x1 + 296*y1*a*x2 + 52*y1*a*x3) * w2 + (-108*l^2*m^2*x1^3 - 54*l*m^3*x1^3 - 108*l*m^2*r*x1^3 - 108*m^3*r*x1^3 + 108*l^2*m*s*x1^3 + 54*l*m^2*s*x1^3 + 108*l*m*r*s*x1^3 + 108*m^2*r*s*x1^3 - 72*l^2*m^2*x1^2*x2 - 72*l*m^2*r*x1^2*x2 + 72*l^2*m*s*x1^2*x2 + 72*l*m*r*s*x1^2*x2 - 24*l^2*m^3*y1*x3 - 36*l*m^4*y1*x3 - 24*l*m^3*r*y1*x3 - 72*m^4*r*y1*x3 + 24*l^2*m^2*s*y1*x3 + 36*l*m^3*s*y1*x3 + 24*l*m^2*r*s*y1*x3 + 72*m^3*r*s*y1*x3 - 24*l^2*m^2*x1*x3^2 - 24*l*m^2*r*x1*x3^2 + 24*l^2*m*s*x1*x3^2 + 24*l*m*r*s*x1*x3^2 + 144*l^2*m^2*x2*x3^2 + 144*l*m^2*r*x2*x3^2 - 144*l^2*m*s*x2*x3^2 - 144*l*m*r*s*x2*x3^2 - 120*l^2*m^2*x3^3 + 72*l*m^3*x3^3 - 120*l*m^2*r*x3^3 + 144*m^3*r*x3^3 + 120*l^2*m*s*x3^3 - 72*l*m^2*s*x3^3 + 120*l*m*r*s*x3^3 - 144*m^2*r*s*x3^3 + 108*l^2*m^2*y1^2 + 54*l*m^3*y1^2 + 108*l*m^2*r*y1^2 + 108*m^3*r*y1^2 - 108*l^2*m*s*y1^2 - 54*l*m^2*s*y1^2 - 108*l*m*r*s*y1^2 - 108*m^2*r*s*y1^2 - 44*l^2*m^2*a*x1 - 54*l*m^3*a*x1 - 44*l*m^2*r*a*x1 - 108*m^3*r*a*x1 + 44*l^2*m*s*a*x1 + 54*l*m^2*s*a*x1 + 44*l*m*r*s*a*x1 + 108*m^2*r*s*a*x1 - 108*l^2*x1^4 - 162*l*m*x1^4 - 54*m^2*x1^4 - 108*l*r*x1^4 - 108*m*r*x1^4 + 108*l*s*x1^4 + 54*m*s*x1^4 + 96*l^2*m^2*a*x2 + 96*l*m^2*r*a*x2 - 96*l^2*m*s*a*x2 - 96*l*m*r*s*a*x2 + 18*l^2*x1^3*x2 + 90*m^2*x1^3*x2 + 18*l*r*x1^3*x2 + 54*m*r*x1^3*x2 - 90*m*s*x1^3*x2 + 72*l^2*x1^2*x2^2 + 72*m^2*x1^2*x2^2 + 72*l*r*x1^2*x2^2 - 72*m*s*x1^2*x2^2 - 112*l^2*m^2*a*x3 + 60*l*m^3*a*x3 - 112*l*m^2*r*a*x3 + 120*m^3*r*a*x3 + 112*l^2*m*s*a*x3 - 60*l*m^2*s*a*x3 + 112*l*m*r*s*a*x3 - 120*m^2*r*s*a*x3 - 12*l*m^2*y1*x1*x3 + 156*m^3*y1*x1*x3 - 24*l^2*s*y1*x1*x3 - 24*l*m*s*y1*x1*x3 - 156*m^2*s*y1*x1*x3 - 24*l*r*s*y1*x1*x3 - 72*m*r*s*y1*x1*x3 + 18*l^2*x1^3*x3 - 72*l*m*x1^3*x3 - 36*m^2*x1^3*x3 + 18*l*r*x1^3*x3 - 18*m*r*x1^3*x3 + 126*l*s*x1^3*x3 + 36*m*s*x1^3*x3 + 72*r*s*x1^3*x3 + 36*l^2*m*y1*x2*x3 + 48*l*m^2*y1*x2*x3 - 84*m^3*y1*x2*x3 + 36*l*m*r*y1*x2*x3 + 108*m^2*r*y1*x2*x3 - 24*l^2*s*y1*x2*x3 - 48*l*m*s*y1*x2*x3 + 84*m^2*s*y1*x2*x3 - 24*l*r*s*y1*x2*x3 - 72*m*r*s*y1*x2*x3 - 72*l^2*x1^2*x2*x3 - 72*l*m*x1^2*x2*x3 - 144*m^2*x1^2*x2*x3 - 72*l*r*x1^2*x2*x3 - 72*m*r*x1^2*x2*x3 + 72*l*s*x1^2*x2*x3 + 144*m*s*x1^2*x2*x3 + 72*r*s*x1^2*x2*x3 - 12*l^2*m*y1*x3^2 - 24*l*m^2*y1*x3^2 - 168*m^3*y1*x3^2 - 12*l*m*r*y1*x3^2 + 60*m^2*r*y1*x3^2 + 24*l^2*s*y1*x3^2 + 60*l*m*s*y1*x3^2 + 168*m^2*s*y1*x3^2 + 24*l*r*s*y1*x3^2 - 24*m*r*s*y1*x3^2 + 48*l^2*x1^2*x3^2 - 96*l*m*x1^2*x3^2 + 72*m^2*x1^2*x3^2 + 48*l*r*x1^2*x3^2 - 96*m*r*x1^2*x3^2 + 96*l*s*x1^2*x3^2 - 72*m*s*x1^2*x3^2 + 96*r*s*x1^2*x3^2 + 96*l^2*x1*x2*x3^2 - 216*l*m*x1*x2*x3^2 - 120*m^2*x1*x2*x3^2 + 96*l*r*x1*x2*x3^2 - 144*m*r*x1*x2*x3^2 + 216*l*s*x1*x2*x3^2 + 120*m*s*x1*x2*x3^2 + 144*r*s*x1*x2*x3^2 - 72*l^2*x2^2*x3^2 - 72*l*m*x2^2*x3^2 - 72*m^2*x2^2*x3^2 - 72*l*r*x2^2*x3^2 - 72*m*r*x2^2*x3^2 + 72*l*s*x2^2*x3^2 + 72*m*s*x2^2*x3^2 + 72*r*s*x2^2*x3^2 - 48*l^2*x1*x3^3 + 120*l*m*x1*x3^3 + 48*m^2*x1*x3^3 - 48*l*r*x1*x3^3 + 120*m*r*x1*x3^3 - 48*l*s*x1*x3^3 - 48*m*s*x1*x3^3 + 24*r*s*x1*x3^3 - 24*l^2*x2*x3^3 - 72*l*m*x2*x3^3 + 192*m^2*x2*x3^3 - 24*l*r*x2*x3^3 - 216*m*r*x2*x3^3 + 72*l*s*x2*x3^3 - 192*m*s*x2*x3^3 + 144*r*s*x2*x3^3 + 72*l^2*x3^4 - 24*l*m*x3^4 - 120*m^2*x3^4 + 72*l*r*x3^4 - 96*m*r*x3^4 - 48*l*s*x3^4 + 120*m*s*x3^4 + 24*r*s*x3^4 - 64*l^2*m*y1*a - 128*l*m^2*y1*a - 128*m^3*y1*a - 64*l*m*r*y1*a - 64*m^2*r*y1*a + 64*l^2*s*y1*a + 128*l*m*s*y1*a + 128*m^2*s*y1*a + 64*l*r*s*y1*a + 64*m*r*s*y1*a + 108*l^2*y1^2*x1 + 162*l*m*y1^2*x1 + 54*m^2*y1^2*x1 + 108*l*r*y1^2*x1 + 108*m*r*y1^2*x1 - 108*l*s*y1^2*x1 - 54*m*s*y1^2*x1 - 44*l^2*a*x1^2 - 98*l*m*a*x1^2 - 54*m^2*a*x1^2 - 44*l*r*a*x1^2 - 44*m*r*a*x1^2 + 44*l*s*a*x1^2 + 54*m*s*a*x1^2 - 64*r*s*a*x1^2 + 108*r*y1*x1^3 - 90*l^2*y1^2*x2 - 72*l*m*y1^2*x2 - 90*m^2*y1^2*x2 - 90*l*r*y1^2*x2 - 126*m*r*y1^2*x2 + 72*l*s*y1^2*x2 + 90*m*s*y1^2*x2 + 72*r*s*y1^2*x2 + 74*l^2*a*x1*x2 - 144*l*m*a*x1*x2 - 118*m^2*a*x1*x2 + 74*l*r*a*x1*x2 + 6*m*r*a*x1*x2 + 144*l*s*a*x1*x2 + 118*m*s*a*x1*x2 + 48*r*s*a*x1*x2 + 198*x1^4*x2 - 96*l*m*a*x2^2 - 96*m*r*a*x2^2 + 96*l*s*a*x2^2 + 96*r*s*a*x2^2 - 18*x1^3*x2^2 - 72*x1^2*x2^3 - 18*l^2*y1^2*x3 + 72*l*m*y1^2*x3 + 180*m^2*y1^2*x3 - 18*l*r*y1^2*x3 + 90*m*r*y1^2*x3 - 126*l*s*y1^2*x3 - 180*m*s*y1^2*x3 - 72*r*s*y1^2*x3 - 46*l^2*a*x1*x3 + 124*l*m*a*x1*x3 + 40*m^2*a*x1*x3 - 46*l*r*a*x1*x3 + 214*m*r*a*x1*x3 - 10*l*s*a*x1*x3 - 40*m*s*a*x1*x3 - 40*r*s*a*x1*x3 + 48*l*y1*x1^2*x3 + 168*m*y1*x1^2*x3 + 24*r*y1*x1^2*x3 + 24*s*y1*x1^2*x3 - 36*x1^4*x3 - 68*l^2*a*x2*x3 - 48*l*m*a*x2*x3 + 124*m^2*a*x2*x3 - 68*l*r*a*x2*x3 - 204*m*r*a*x2*x3 + 48*l*s*a*x2*x3 - 124*m*s*a*x2*x3 + 144*r*s*a*x2*x3 + 96*l*y1*x1*x2*x3 - 228*m*y1*x1*x2*x3 + 120*r*y1*x1*x2*x3 + 120*s*y1*x1*x2*x3 - 48*l*y1*x2^2*x3 + 108*m*y1*x2^2*x3 - 48*r*y1*x2^2*x3 - 72*s*y1*x2^2*x3 + 144*x1^2*x2^2*x3 + 84*l^2*a*x3^2 - 56*l*m*a*x3^2 - 112*m^2*a*x3^2 + 84*l*r*a*x3^2 - 92*m*r*a*x3^2 - 4*l*s*a*x3^2 + 112*m*s*a*x3^2 + 32*r*s*a*x3^2 - 216*l*y1*x1*x3^2 - 120*m*y1*x1*x3^2 - 144*r*y1*x1*x3^2 - 144*s*y1*x1*x3^2 + 18*x1^3*x3^2 + 24*l*y1*x2*x3^2 + 264*m*y1*x2*x3^2 - 72*s*y1*x2*x3^2 - 192*x1^2*x2*x3^2 + 48*x1*x2^2*x3^2 + 72*x2^3*x3^2 + 96*l*y1*x3^3 + 132*m*y1*x3^3 - 96*r*y1*x3^3 - 72*s*y1*x3^3 - 24*x1^2*x3^3 + 72*x1*x2*x3^3 - 192*x2^2*x3^3 - 120*x1*x3^4 - 24*x2*x3^4 + 72*x3^5 - 108*r*y1^3 - 32*l*m*a^2 - 32*m^2*a^2 + 32*l*s*a^2 + 32*m*s*a^2 - 128*l*y1*a*x1 - 64*m*y1*a*x1 + 44*r*y1*a*x1 - 64*s*y1*a*x1 + 54*a*x1^3 + 8*l*y1*a*x2 + 120*m*y1*a*x2 + 8*r*y1*a*x2 - 56*s*y1*a*x2 - 198*y1^2*x1*x2 - 10*a*x1^2*x2 + 90*y1^2*x2^2 + 118*a*x1*x2^2 + 120*l*y1*a*x3 + 196*m*y1*a*x3 - 64*r*y1*a*x3 - 96*s*y1*a*x3 - 12*y1^2*x1*x3 - 20*a*x1^2*x3 - 120*y1^2*x2*x3 + 132*a*x1*x2*x3 - 124*a*x2^2*x3 + 174*y1^2*x3^2 - 166*a*x1*x3^2 - 8*a*x2*x3^2 - 12*a*x3^3 + 74*y1^2*a + 22*a^2*x1 + 32*a^2*x2 - 60*a^2*x3) * z1 + (108*l^2*m*x1^3 + 54*l*m^2*x1^3 + 108*l*m*r*x1^3 + 108*m^2*r*x1^3 + 72*l^2*m*x1^2*x2 + 72*l*m*r*x1^2*x2 + 24*l^2*m^2*y1*x3 + 36*l*m^3*y1*x3 + 24*l*m^2*r*y1*x3 + 72*m^3*r*y1*x3 + 24*l^2*m*x1*x3^2 + 24*l*m*r*x1*x3^2 - 144*l^2*m*x2*x3^2 - 144*l*m*r*x2*x3^2 + 120*l^2*m*x3^3 - 72*l*m^2*x3^3 + 120*l*m*r*x3^3 - 144*m^2*r*x3^3 - 108*l^2*m*y1^2 - 54*l*m^2*y1^2 - 108*l*m*r*y1^2 - 108*m^2*r*y1^2 + 44*l^2*m*a*x1 + 54*l*m^2*a*x1 + 44*l*m*r*a*x1 + 108*m^2*r*a*x1 + 108*l*x1^4 + 54*m*x1^4 - 96*l^2*m*a*x2 - 96*l*m*r*a*x2 - 90*m*x1^3*x2 - 72*m*x1^2*x2^2 + 112*l^2*m*a*x3 - 60*l*m^2*a*x3 + 112*l*m*r*a*x3 - 120*m^2*r*a*x3 - 24*l^2*y1*x1*x3 - 24*l*m*y1*x1*x3 - 156*m^2*y1*x1*x3 - 24*l*r*y1*x1*x3 - 72*m*r*y1*x1*x3 + 126*l*x1^3*x3 + 36*m*x1^3*x3 + 72*r*x1^3*x3 - 24*l^2*y1*x2*x3 - 48*l*m*y1*x2*x3 + 84*m^2*y1*x2*x3 - 24*l*r*y1*x2*x3 - 72*m*r*y1*x2*x3 + 72*l*x1^2*x2*x3 + 144*m*x1^2*x2*x3 + 72*r*x1^2*x2*x3 + 24*l^2*y1*x3^2 + 60*l*m*y1*x3^2 + 168*m^2*y1*x3^2 + 24*l*r*y1*x3^2 - 24*m*r*y1*x3^2 + 96*l*x1^2*x3^2 - 72*m*x1^2*x3^2 + 96*r*x1^2*x3^2 + 216*l*x1*x2*x3^2 + 120*m*x1*x2*x3^2 + 144*r*x1*x2*x3^2 + 72*l*x2^2*x3^2 + 72*m*x2^2*x3^2 + 72*r*x2^2*x3^2 - 48*l*x1*x3^3 - 48*m*x1*x3^3 + 24*r*x1*x3^3 + 72*l*x2*x3^3 - 192*m*x2*x3^3 + 144*r*x2*x3^3 - 48*l*x3^4 + 120*m*x3^4 + 24*r*x3^4 + 64*l^2*y1*a + 128*l*m*y1*a + 128*m^2*y1*a + 64*l*r*y1*a + 64*m*r*y1*a - 108*l*y1^2*x1 - 54*m*y1^2*x1 + 44*l*a*x1^2 + 54*m*a*x1^2 - 64*r*a*x1^2 + 72*l*y1^2*x2 + 90*m*y1^2*x2 + 72*r*y1^2*x2 + 144*l*a*x1*x2 + 118*m*a*x1*x2 + 48*r*a*x1*x2 + 96*l*a*x2^2 + 96*r*a*x2^2 - 126*l*y1^2*x3 - 180*m*y1^2*x3 - 72*r*y1^2*x3 - 10*l*a*x1*x3 - 40*m*a*x1*x3 - 40*r*a*x1*x3 + 24*y1*x1^2*x3 + 48*l*a*x2*x3 - 124*m*a*x2*x3 + 144*r*a*x2*x3 + 120*y1*x1*x2*x3 - 72*y1*x2^2*x3 - 4*l*a*x3^2 + 112*m*a*x3^2 + 32*r*a*x3^2 - 144*y1*x1*x3^2 - 72*y1*x2*x3^2 - 72*y1*x3^3 + 32*l*a^2 + 32*m*a^2 - 64*y1*a*x1 - 56*y1*a*x2 - 96*y1*a*x3) * z2

/-- Uniform cocycle identity with natural hypotheses (U-relations for four slopes). -/
theorem uniform {F : Type*} [Field F] (a b x1 y1 x2 y2 x3 y3 l m r s : F)
    (h2F : (2:F) ≠ 0) (hD : 4*a^3 + 27*b^2 ≠ 0)
    (h1 : y1^2 = x1^3 + a*x1 + b)
    (u1 : y2 = y1 + l*(x2 - x1)) (u2 : 2*l*y1 + l^2*(x2 - x1) = x1^2 + x1*x2 + x2^2 + a)
    (v1 : y3 = y2 + m*(x3 - x2)) (v2 : 2*m*y2 + m^2*(x3 - x2) = x2^2 + x2*x3 + x3^2 + a)
    (w1 : y3 = (l*(x1 - (l^2 - x1 - x2)) - y1) + r*(x3 - (l^2 - x1 - x2)))
    (w2 : 2*r*(l*(x1 - (l^2 - x1 - x2)) - y1) + r^2*(x3 - (l^2 - x1 - x2))
        = (l^2 - x1 - x2)^2 + (l^2 - x1 - x2)*x3 + x3^2 + a)
    (z1 : (m*(x2 - (m^2 - x2 - x3)) - y2) = y1 + s*((m^2 - x2 - x3) - x1))
    (z2 : 2*s*y1 + s^2*((m^2 - x2 - x3) - x1)
        = x1^2 + x1*(m^2 - x2 - x3) + (m^2 - x2 - x3)^2 + a) :
    l + r = m + s := by
  have hb : b = y1^2 - x1^3 - a*x1 := by linear_combination -h1
  subst hb; subst u1; subst v1
  have key := uniform_core8 a y1 x1 x2 x3 l m r s u2 v2 w1 w2 z1 z2
  have h8 : (8:F) ≠ 0 := by
    have : (8:F) = 2*2*2 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h2F h2F) h2F
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (mul_ne_zero h8 hD)
  · linear_combination h

end Algebra

section Curve

variable {F : Type*} [Field F] [DecidableEq F]

variable (W : WeierstrassCurve F)

@[simp] lemma lam_zero_left (Q : W.toAffine.Point) : slopeCocycle W 0 Q = 0 := by
  cases Q <;> rfl
@[simp] lemma lam_zero_right (P : W.toAffine.Point) : slopeCocycle W P 0 = 0 := by
  cases P <;> rfl
@[simp] lemma lam_some {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    slopeCocycle W (.some x₁ y₁ h₁) (.some x₂ y₂ h₂) = W.toAffine.slope x₁ x₂ y₁ y₂ := rfl

variable [W.IsShortNF]

lemma negY_short (x y : F) : W.toAffine.negY x y = -y := by
  simp [negY, W.a₁_of_isShortNF, W.a₃_of_isShortNF]

lemma equation_short {x y : F} (h : W.toAffine.Equation x y) : y^2 = x^3 + W.a₄*x + W.a₆ := by
  rw [equation_iff] at h
  simpa [W.a₁_of_isShortNF, W.a₂_of_isShortNF, W.a₃_of_isShortNF] using h

/-- U-relations for the Mathlib slope of a non-vertical pair. -/
lemma slope_U [Fact ((2:F) ≠ 0)] {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    y₂ = y₁ + W.toAffine.slope x₁ x₂ y₁ y₂ * (x₂ - x₁) ∧
    2 * W.toAffine.slope x₁ x₂ y₁ y₂ * y₁ + (W.toAffine.slope x₁ x₂ y₁ y₂)^2 * (x₂ - x₁)
      = x₁^2 + x₁*x₂ + x₂^2 + W.a₄ := by
  have e₁ := equation_short W h₁
  have e₂ := equation_short W h₂
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ W.toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    have hyy : y₁ = y₂ := Y_eq_of_Y_ne h₁ h₂ hx hy
    subst hx; subst hyy
    rw [slope_of_Y_ne rfl hy]
    rw [negY_short] at hy
    have h2y : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := by
      rw [negY_short]; intro h; apply hy; linear_combination h
    have h2y' : y₁ - W.toAffine.negY x₁ y₁ = 2 * y₁ := by rw [negY_short]; ring
    rw [h2y'] at h2y ⊢
    have hy0 : y₁ ≠ 0 := by intro h0; apply h2y; rw [h0]; ring
    have h2 : (2:F) ≠ 0 := Fact.out
    refine ⟨by ring, ?_⟩
    simp only [W.a₁_of_isShortNF, W.a₂_of_isShortNF]
    field_simp
    ring
  · rw [slope_of_X_ne hx]
    have hx' : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    refine ⟨by field_simp; ring, ?_⟩
    field_simp
    linear_combination (x₁ - x₂) * (e₁ - e₂)

/-- Coordinates of `P + Q` for a non-vertical pair. -/
lemma add_coords {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    ∃ h : W.toAffine.Nonsingular
        ((W.toAffine.slope x₁ x₂ y₁ y₂)^2 - x₁ - x₂)
        (W.toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - ((W.toAffine.slope x₁ x₂ y₁ y₂)^2 - x₁ - x₂)) - y₁),
      (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : W.toAffine.Point) = Point.some _ _ h := by
  have ex : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)
      = (W.toAffine.slope x₁ x₂ y₁ y₂)^2 - x₁ - x₂ := by
    simp [addX, W.a₁_of_isShortNF, W.a₂_of_isShortNF]
  have ey : W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)
      = W.toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - ((W.toAffine.slope x₁ x₂ y₁ y₂)^2 - x₁ - x₂)) - y₁ := by
    simp only [addY, negY_short, negAddY, ex]; ring
  have hns := nonsingular_add h₁ h₂ hxy
  rw [ex, ey] at hns
  refine ⟨hns, ?_⟩
  rw [Point.add_some hxy]
  simp only [Point.some.injEq]
  exact ⟨ex, ey⟩

lemma not_vert_of_add_ne_zero {x₁ y₁ x₂ y₂ : F} {h₁ : W.toAffine.Nonsingular x₁ y₁}
    {h₂ : W.toAffine.Nonsingular x₂ y₂}
    (h : (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : W.toAffine.Point) ≠ 0) :
    ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := fun hv => h (Point.add_of_Y_eq hv.1 hv.2)

lemma vert_of_add_eq_zero {x₁ y₁ x₂ y₂ : F} {h₁ : W.toAffine.Nonsingular x₁ y₁}
    {h₂ : W.toAffine.Nonsingular x₂ y₂}
    (h : (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : W.toAffine.Point) = 0) :
    x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂ := by
  by_contra hv
  rw [Point.add_some hv] at h
  exact Point.some_ne_zero _ h

lemma lam_eq_zero_of_add_eq_zero {P Q : W.toAffine.Point} (h : P + Q = 0) : slopeCocycle W P Q = 0 := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  have hv := vert_of_add_eq_zero W h
  simp only [lam_some]
  exact slope_of_Y_eq hv.1 hv.2

/-- Uniqueness of a slope satisfying the U-relations for a non-vertical pair. -/
lemma slope_unique [Fact ((2:F) ≠ 0)] {x₁ y₁ x₂ y₂ l l' c : F} (hv : ¬(x₁ = x₂ ∧ y₁ = -y₂))
    (U1 : y₂ = y₁ + l*(x₂ - x₁)) (U2 : 2*l*y₁ + l^2*(x₂ - x₁) = c)
    (U1' : y₂ = y₁ + l'*(x₂ - x₁)) (U2' : 2*l'*y₁ + l'^2*(x₂ - x₁) = c) : l = l' := by
  have h2 : (2:F) ≠ 0 := Fact.out
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₂ = y₁ := by linear_combination U1
    subst hy
    have hy0 : y₂ ≠ 0 := by
      intro h0; apply hv; refine ⟨rfl, ?_⟩; rw [h0]; ring
    have : (2*y₂) * (l - l') = 0 := by linear_combination U2 - U2'
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero h2 hy0)
    · linear_combination h
  · have hx' : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have : (x₂ - x₁) * (l - l') = 0 := by linear_combination U1' - U1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hx'
    · linear_combination h

lemma lam_comm (P Q : W.toAffine.Point) : slopeCocycle W P Q = slopeCocycle W Q P := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  simp only [lam_some]
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = W.toAffine.negY x₁ y₂
    · rw [slope_of_Y_eq rfl hy, slope_of_Y_eq rfl (by rw [hy, negY_negY])]
    · have hyy : y₁ = y₂ := Y_eq_of_Y_ne h₁.1 h₂.1 rfl hy
      subst hyy; rfl
  · rw [slope_of_X_ne hx, slope_of_X_ne (Ne.symm hx)]
    rw [← neg_sub y₂, ← neg_sub x₂, neg_div_neg_eq]

lemma neg_some_short {x y : F} (h : W.toAffine.Nonsingular x y) :
    ∃ h' : W.toAffine.Nonsingular x (-y),
      (-(Point.some x y h) : W.toAffine.Point) = Point.some x (-y) h' := by
  have h' := (nonsingular_neg x y).mpr h
  rw [negY_short] at h'
  refine ⟨h', ?_⟩
  rw [Point.neg_some]
  simp only [Point.some.injEq, true_and]
  exact negY_short W x y

lemma lam_neg [Fact ((2:F) ≠ 0)] (P Q : W.toAffine.Point) : slopeCocycle W (-P) (-Q) = -slopeCocycle W P Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · simp [← Point.zero_def]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · simp [← Point.zero_def]
  obtain ⟨h₁', e₁⟩ := neg_some_short W h₁
  obtain ⟨h₂', e₂⟩ := neg_some_short W h₂
  rw [e₁, e₂]
  simp only [lam_some]
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = W.toAffine.negY x₁ y₂
    · rw [slope_of_Y_eq rfl hy, slope_of_Y_eq rfl (by rw [negY_short] at hy ⊢; rw [hy]), neg_zero]
    · have hyy : y₁ = y₂ := Y_eq_of_Y_ne h₁.1 h₂.1 rfl hy
      subst hyy
      have hy' : -y₁ ≠ W.toAffine.negY x₁ (-y₁) := by
        rw [negY_short] at hy ⊢; intro h; apply hy; linear_combination -h
      rw [slope_of_Y_ne rfl hy, slope_of_Y_ne rfl hy']
      simp only [negY_short, W.a₁_of_isShortNF]
      rw [← neg_div_neg_eq]
      ring
  · rw [slope_of_X_ne hx, slope_of_X_ne hx]
    rw [← neg_div]; congr 1; ring

lemma two_ne [W.IsElliptic] : (2:F) ≠ 0 := by
  have h := W.isUnit_Δ.ne_zero
  rw [W.Δ_of_isShortNF] at h
  intro h2; apply h
  have : (16:F) = 2 * 8 := by norm_num
  rw [this, h2]; ring

lemma disc_ne [W.IsElliptic] : 4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 ≠ 0 := by
  have h := W.isUnit_Δ.ne_zero
  rw [W.Δ_of_isShortNF] at h
  exact right_ne_zero_of_mul h

/-- Third point on the line: `λ(A, B) = λ(A, -(A + B))`. -/
lemma lam_third [Fact ((2:F) ≠ 0)] (A B : W.toAffine.Point) : slopeCocycle W A B = slopeCocycle W A (-(A + B)) := by
  rcases A with _ | ⟨x₁, y₁, h₁⟩
  · simp [← Point.zero_def]
  rcases B with _ | ⟨x₂, y₂, h₂⟩
  · rw [← Point.zero_def, lam_zero_right, add_zero]
    symm; apply lam_eq_zero_of_add_eq_zero; exact add_neg_cancel _
  by_cases hAB : (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : W.toAffine.Point) = 0
  · rw [hAB, neg_zero, lam_zero_right]; exact lam_eq_zero_of_add_eq_zero W hAB
  have hv := not_vert_of_add_ne_zero W hAB
  have hAT : (Point.some x₁ y₁ h₁ + -(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) :
      W.toAffine.Point) ≠ 0 := by
    rw [show ∀ A B : W.toAffine.Point, A + -(A + B) = -B from fun A B => by abel]
    exact neg_ne_zero.mpr (Point.some_ne_zero _)
  obtain ⟨h₄, e₄⟩ := add_coords W h₁ h₂ hv
  rw [e₄] at hAT ⊢
  obtain ⟨h₄', e₄'⟩ := neg_some_short W h₄
  rw [e₄'] at hAT ⊢
  have hvT := not_vert_of_add_ne_zero W hAT
  rw [negY_short] at hvT
  simp only [lam_some]
  obtain ⟨U1, U2⟩ := slope_U W h₁.1 h₂.1 hv
  obtain ⟨T1, T2⟩ := slope_U W h₁.1 h₄'.1 (by rwa [negY_short])
  refine slope_unique hvT ?_ ?_ T1 T2
  · ring
  · linear_combination U2

theorem lam_cocycle [W.IsElliptic] (P Q R : W.toAffine.Point) :
    slopeCocycle W P Q + slopeCocycle W (P + Q) R = slopeCocycle W Q R + slopeCocycle W P (Q + R) := by
  haveI : Fact ((2:F) ≠ 0) := ⟨two_ne W⟩
  by_cases hP : P = 0
  · subst hP; simp
  by_cases hQ : Q = 0
  · subst hQ; simp
  by_cases hR : R = 0
  · subst hR; simp
  by_cases hPQ : P + Q = 0
  · have hQ' : Q = -P := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hPQ
    rw [hPQ, lam_zero_left, lam_eq_zero_of_add_eq_zero W hPQ, hQ']
    have e1 : slopeCocycle W (-P) R = -slopeCocycle W P (-R) := by simpa using lam_neg W P (-R)
    have e2 : slopeCocycle W P (-R) = slopeCocycle W P (-P + R) := by
      rw [lam_third W P (-R)]; congr 1; abel
    rw [e1, e2]; ring
  by_cases hQR : Q + R = 0
  · have hR' : R = -Q := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hQR
    rw [hQR, lam_zero_right, lam_eq_zero_of_add_eq_zero W hQR, hR']
    have e1 : slopeCocycle W (P + Q) (-Q) = -slopeCocycle W Q (-(P + Q)) := by
      rw [lam_comm]; simpa using lam_neg W Q (-(P + Q))
    have e2 : slopeCocycle W Q (-(P + Q)) = slopeCocycle W P Q := by
      rw [add_comm P Q, ← lam_third, lam_comm]
    rw [e1, e2]; ring
  by_cases hS : P + Q + R = 0
  · have hS' : P + (Q + R) = 0 := by rw [← add_assoc]; exact hS
    rw [lam_eq_zero_of_add_eq_zero W hS, lam_eq_zero_of_add_eq_zero W hS']
    have hR' : R = -(P + Q) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hS
    rw [hR', add_comm P Q, ← lam_third, lam_comm]
  have hS' : P + (Q + R) ≠ 0 := by rw [← add_assoc]; exact hS
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd rfl hP
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd rfl hQ
  rcases R with _ | ⟨x₃, y₃, h₃⟩
  · exact absurd rfl hR
  have v12 := not_vert_of_add_ne_zero W hPQ
  have v23 := not_vert_of_add_ne_zero W hQR
  obtain ⟨h₄, e₄⟩ := add_coords W h₁ h₂ v12
  obtain ⟨h₅, e₅⟩ := add_coords W h₂ h₃ v23
  rw [e₄] at hS ⊢
  rw [e₅] at hS' ⊢
  have v43 := not_vert_of_add_ne_zero W hS
  have v15 := not_vert_of_add_ne_zero W hS'
  simp only [lam_some]
  obtain ⟨U1, U2⟩ := slope_U W h₁.1 h₂.1 v12
  obtain ⟨V1, V2⟩ := slope_U W h₂.1 h₃.1 v23
  obtain ⟨W1, W2⟩ := slope_U W h₄.1 h₃.1 v43
  obtain ⟨Z1, Z2⟩ := slope_U W h₁.1 h₅.1 v15
  exact uniform W.a₄ W.a₆ x₁ y₁ x₂ y₂ x₃ y₃ _ _ _ _ (two_ne W) (disc_ne W)
    (equation_short W h₁.1) U1 U2 V1 V2 W1 W2 Z1 Z2

end Curve

section Coboundary

/-- Abstract coboundary step: averaging a normalised 2-cocycle over a finite group of
order invertible in `K` gives a function whose coboundary is the cocycle. -/
theorem coboundary_of_cocycle {G K : Type*} [AddCommGroup G] [Fintype G] [Field K]
    (c : G → G → K) (hc : ∀ P Q R, c P Q + c (P + Q) R = c Q R + c P (Q + R))
    (hn : (Fintype.card G : K) ≠ 0) (P Q : G) :
    -(Fintype.card G : K)⁻¹ * ∑ R, c (P + Q) R
      = -(Fintype.card G : K)⁻¹ * ∑ R, c P R + -(Fintype.card G : K)⁻¹ * ∑ R, c Q R
        + c P Q := by
  have hsum : ∑ R, (c P Q + c (P + Q) R) = ∑ R, (c Q R + c P (Q + R)) :=
    Finset.sum_congr rfl (fun R _ => hc P Q R)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hre : ∑ R, c P (Q + R) = ∑ R, c P R :=
    Fintype.sum_equiv (Equiv.addLeft Q) _ _ (fun R => rfl)
  rw [hre] at hsum
  field_simp
  linear_combination -hsum

/-- Uniqueness: two solutions of the coboundary equation agree when `|G|` is invertible. -/
theorem coboundary_unique {G K : Type*} [AddCommGroup G] [Fintype G] [Field K]
    (c : G → G → K) (hn : (Fintype.card G : K) ≠ 0) (z z' : G → K)
    (hz : ∀ P Q, z (P + Q) = z P + z Q + c P Q)
    (hz' : ∀ P Q, z' (P + Q) = z' P + z' Q + c P Q) :
    z = z' := by
  let h : G →+ K :=
    { toFun := fun P => z P - z' P
      map_zero' := by
        have a := hz 0 0
        have b := hz' 0 0
        simp only [add_zero] at a b
        linear_combination b - a
      map_add' := fun P Q => by simp only [hz, hz']; ring }
  funext P
  have h1 : h (Fintype.card G • P) = 0 := by rw [card_nsmul_eq_zero, map_zero]
  rw [map_nsmul, nsmul_eq_mul] at h1
  have h2 : h P = 0 := (mul_eq_zero.mp h1).resolve_left hn
  have : z P - z' P = 0 := h2
  linear_combination this

/-- Telescoping (Miller-sum form): `z(Q) = -(1/n) ∑_{i<n} c(iQ, Q)` for a normalised
cocycle. -/
theorem coboundary_miller {G K : Type*} [AddCommGroup G] [Fintype G] [Field K]
    (c : G → G → K) (hc0 : ∀ Q, c 0 Q = 0) (hn : (Fintype.card G : K) ≠ 0) (z : G → K)
    (hz : ∀ P Q, z (P + Q) = z P + z Q + c P Q) (Q : G) :
    z Q = -(Fintype.card G : K)⁻¹ * ∑ i ∈ range (Fintype.card G), c (i • Q) Q := by
  have z0 : z 0 = 0 := by
    have a := hz 0 0
    simp only [add_zero, hc0] at a
    linear_combination -a
  have tele : ∀ m : ℕ, z (m • Q) = m * z Q + ∑ i ∈ range m, c (i • Q) Q := by
    intro m
    induction m with
    | zero => simp [z0]
    | succ k ih =>
      rw [succ_nsmul, hz, ih, Finset.sum_range_succ]
      push_cast
      ring
  have hN := tele (Fintype.card G)
  rw [card_nsmul_eq_zero, z0] at hN
  field_simp
  linear_combination -hN

end Coboundary

section Zeta

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic] [W.IsShortNF] [Fintype W.toAffine.Point]

theorem zetaE_add (hn : (Fintype.card W.toAffine.Point : F) ≠ 0) (P Q : W.toAffine.Point) :
    zetaE W (P + Q) = zetaE W P + zetaE W Q + slopeCocycle W P Q :=
  coboundary_of_cocycle (slopeCocycle W) (lam_cocycle W) hn P Q

theorem zetaE_unique (hn : (Fintype.card W.toAffine.Point : F) ≠ 0)
    (z : W.toAffine.Point → F) (hz : ∀ P Q, z (P + Q) = z P + z Q + slopeCocycle W P Q) :
    z = zetaE W :=
  coboundary_unique (slopeCocycle W) hn z (zetaE W) hz (zetaE_add W hn)

theorem zetaE_miller (hn : (Fintype.card W.toAffine.Point : F) ≠ 0) (Q : W.toAffine.Point) :
    zetaE W Q = -(Fintype.card W.toAffine.Point : F)⁻¹ *
      ∑ i ∈ range (Fintype.card W.toAffine.Point), slopeCocycle W (i • Q) Q :=
  coboundary_miller (slopeCocycle W) (lam_zero_left W) hn (zetaE W) (zetaE_add W hn) Q

/-- `ζ_E(O) = 0` (by definition: `λ(O, R) = 0`). -/
theorem zetaE_zero : zetaE W 0 = 0 := by
  unfold zetaE
  simp

/-- `∑_R λ(-P, R) = -∑_R λ(P, R)`. -/
lemma sum_lam_neg (P : W.toAffine.Point) :
    ∑ R, slopeCocycle W (-P) R = -∑ R, slopeCocycle W P R := by
  haveI : Fact ((2 : F) ≠ 0) := ⟨two_ne W⟩
  have hre : ∑ R, slopeCocycle W (-P) (-R) = ∑ R, slopeCocycle W (-P) R :=
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun R => rfl)
  rw [← hre, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun R _ => lam_neg W P R

/-- `ζ_E` is odd. -/
theorem zetaE_neg (P : W.toAffine.Point) : zetaE W (-P) = -zetaE W P := by
  unfold zetaE
  rw [sum_lam_neg]
  ring

/-- `∑_P ζ_E(P) = 0`. -/
theorem zetaE_sum : ∑ P, zetaE W P = 0 := by
  have hre : ∑ P, zetaE W (-P) = ∑ P, zetaE W P :=
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun P => rfl)
  simp_rw [zetaE_neg] at hre
  rw [Finset.sum_neg_distrib] at hre
  have h2 : (2 : F) * ∑ P, zetaE W P = 0 := by linear_combination -hre
  exact (mul_eq_zero.mp h2).resolve_left (two_ne W)

end Zeta

/-- Z1. -/
theorem slopeCocycleLaw : Ecdlp.ParityFourier.SlopeCocycle := by
  intro F _ _ W _ _ P Q R
  exact ⟨lam_cocycle W P Q R, lam_comm W P Q, lam_zero_left W Q⟩

/-- Z2. -/
theorem zetaCoboundary : Ecdlp.ParityFourier.ZetaCoboundary := by
  intro F _ _ W _ _ _ hn
  exact ⟨zetaE_add W hn, fun z hz => zetaE_unique W hn z hz, zetaE_zero W, zetaE_neg W,
    zetaE_sum W, zetaE_miller W hn⟩

/-- Z3. -/
theorem anomalousSumHom : Ecdlp.ParityFourier.AnomalousSumHom := by
  intro F _ _ W _ _ _ hn P Q
  have hsum : ∑ R, (slopeCocycle W P Q + slopeCocycle W (P + Q) R)
      = ∑ R, (slopeCocycle W Q R + slopeCocycle W P (Q + R)) :=
    Finset.sum_congr rfl (fun R _ => lam_cocycle W P Q R)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hn, zero_mul, zero_add] at hsum
  have hre : ∑ R, slopeCocycle W P (Q + R) = ∑ R, slopeCocycle W P R :=
    Fintype.sum_equiv (Equiv.addLeft Q) _ _ (fun R => rfl)
  rw [hre] at hsum
  linear_combination hsum

/-- Z4. -/
theorem zetaLsbTransfer : Ecdlp.ParityFourier.ZetaLsbTransfer := by
  intro p n _ _ _ _ hp2 hn2 _ W _ _ _ _ G _ hT
  exact ⟨ProofsWT.weilTransferLsb n p hn2 hp2 _ hT,
    fun lam => ProofsCT.weilTransferLsbJ n p hn2 hp2 lam _ hT,
    fun lam hlam => ProofsCT.weilTransferLsbG n p hn2 hp2 lam hlam _ hT⟩

end Ecdlp.ParityFourier.ProofsZeta
