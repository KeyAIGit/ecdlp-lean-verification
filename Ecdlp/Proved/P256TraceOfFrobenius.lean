import Mathlib
import Ecdlp.Proved.P256Curve

/-!
# NIST P-256's trace of Frobenius: ordinary, non-anomalous, Hasse-consistent

The live P-256 domain's Smart/SSSA attack-boundary rung, mirroring secp256k1's
`Ecdlp/Proved/TraceOfFrobenius.lean`. For P-256 with group order `#E = n` (the published,
kernel-verified prime order; cofactor 1) the **trace of Frobenius** is `t = p + 1 − n`. Two
classical transfer attacks are governed by `t`:

* `t = 0` ⟺ supersingular ⟺ small embedding degree (feasible MOV/Frey–Rück);
* `t = 1` ⟺ `#E = p`, i.e. anomalous ⟺ the Smart / Semaev–Satoh–Araki (SSSA) `p`-adic
  elliptic-logarithm attack solves ECDLP in linear time.

This file machine-checks (over `ℤ`, from `#E = n`) that P-256 avoids both and is
Hasse-consistent: `t ≠ 0` (ordinary), `t ≠ 1` (not anomalous — SSSA inapplicable), and
`t² ≤ 4p` (the Hasse bound `|t| ≤ 2√p`; here `t` is a 127-bit number, well inside the
range, confirming cofactor 1). Together with `P256EmbeddingDegree.lean` these are the
verified boundary nodes: ECDLP on P-256 does not leak through MOV/FR or Smart/SSSA.

Scope note: the theorem below is arithmetic on `t = p + 1 − n`. Reading `t` as the trace of
Frobenius uses `#E(𝔽_p) = n` (cofactor 1), which is proved in `P256CardinalityExact.lean`
(`p256_card_point_eq_n`, with `native_decide` compiler trust inherited from `n • G = 0`, the
base point's equation and nonsingularity, and `Δ ≠ 0`; the Pratt certificates are
kernel-checked). The definition of the trace as `p + 1 − #E` is not itself formalized
here. What is verified in this file is the exact arithmetic that makes the attack boundary
hold *given* that order.
-/

namespace Ecdlp.P256

/-- **NIST P-256 is ordinary, non-anomalous, and Hasse-consistent.** With `#E = n`, the trace
`t = p + 1 − n` satisfies `t ≠ 0` (not supersingular), `t ≠ 1` (not anomalous — Smart/SSSA
does not apply), and `t² ≤ 4p` (the Hasse bound). -/
theorem p256_trace_ordinary_nonanomalous :
    ((p : ℤ) + 1 - n) ≠ 0 ∧
    ((p : ℤ) + 1 - n) ≠ 1 ∧
    ((p : ℤ) + 1 - n) ^ 2 ≤ 4 * (p : ℤ) := by
  native_decide

end Ecdlp.P256
