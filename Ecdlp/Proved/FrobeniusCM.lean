import Mathlib
import Ecdlp.Secp256k1Verified

/-!
# secp256k1: the CM-by-ℤ[ω] Frobenius arithmetic certificate

The curve `E : y² = x³ + 7` over `𝔽_p` has `j`-invariant `0`, so its endomorphism
algebra `End(E) ⊗ ℚ` is the imaginary quadratic field `ℚ(ω)` where `ω` is a
primitive cube root of unity (a root of `x² + x + 1`, i.e. `ω = (−1 + √−3)/2`).
Because `p ≡ 1 (mod 3)` the prime `p` **splits** in the ring of integers
`ℤ[ω]` (discriminant `−3`), so `p = N(π)` for a Frobenius element
`π = a + b·ω ∈ ℤ[ω]` with norm form `N(a + bω) = a² − a·b + b²` and trace form
`Tr(a + bω) = 2a − b`.

This file machine-checks the **integer CM data** for the concrete secp256k1
constants. With

* `a = 367917413016453100223835821029139468249`,
* `b = 303414439467246543595250775667605759171`,
* `t := p + 1 − n` (the trace of Frobenius, unconditional once `#E = n`),

the three identities below hold exactly over `ℤ`:

* `secp256k1_frobenius_norm`  — `a² − a·b + b² = p`  (`N(π) = p`; `p` splits in `ℤ[ω]`);
* `secp256k1_frobenius_trace` — `2a − b = p + 1 − n`  (`Tr(π) = t`);
* `secp256k1_four_p_eq_trace_sq` — `4p = t² + 3·b²`  (the CM discriminant relation).

## What this is, and is not

These are **arithmetic certificates**: they pin down the CM order and the
Frobenius conjugacy data purely as integer identities. Concretely they show that
the imaginary quadratic order attached to secp256k1 is `ℤ[ω]` of discriminant
`−3` — the maximal order of `ℚ(√−3)` — and NOT some larger conductor or a spurious
composite such as `−163` that earlier heuristics might suggest. Together with
the Hasse bound `t² ≤ 4p` (`TraceOfFrobenius.lean`) and `b ≠ 0` in `4p = t² + 3b²` — which
forces the strict `t² < 4p` here — the relation identifies `End(E) ⊗ ℚ = ℚ(√−3)` for the curve.

They are **not** a proof that the geometric Frobenius is an endomorphism of `E`,
nor that `a + b·ω` literally equals `π` as an element of `End(E)`: the elliptic
curve CM theory needed for that (endomorphism rings, complex multiplication over
finite fields) is a Mathlib foundation gap at v4.31. What is verified here is the
integer number theory that any such `π` must satisfy — the norm, the trace, and
the discriminant identity — compiler-trusted through `native_decide`
(`Lean.ofReduceBool`).
-/

namespace Ecdlp.Curve

/-- Frobenius CM coefficient `a` in `π = a + b·ω` for secp256k1 (integer literal). -/
private def frobA : ℤ := 367917413016453100223835821029139468249

/-- Frobenius CM coefficient `b` in `π = a + b·ω` for secp256k1 (integer literal). -/
private def frobB : ℤ := 303414439467246543595250775667605759171

/-- **`N(π) = p`.** The Frobenius norm form `a² − a·b + b²` on `ℤ[ω]` evaluated at
the secp256k1 CM coefficients equals `p`; i.e. `p` splits in `ℤ[ω]` as `N(a + bω)`. -/
theorem secp256k1_frobenius_norm :
    frobA ^ 2 - frobA * frobB + frobB ^ 2 = (Secp256k1.p : ℤ) := by
  native_decide

/-- **`Tr(π) = t`.** The Frobenius trace form `2a − b` on `ℤ[ω]` equals the trace
of Frobenius `t = p + 1 − n`. -/
theorem secp256k1_frobenius_trace :
    2 * frobA - frobB = (Secp256k1.p : ℤ) + 1 - Secp256k1.n := by
  native_decide

/-- **CM discriminant relation `4p = t² + 3b²`.** With `t = p + 1 − n` and `b` the
Frobenius CM coefficient, `4p = t² + 3·b²`, the norm identity for the order `ℤ[ω]`
of discriminant `−3`. -/
theorem secp256k1_four_p_eq_trace_sq :
    4 * (Secp256k1.p : ℤ) = ((Secp256k1.p : ℤ) + 1 - Secp256k1.n) ^ 2 + 3 * frobB ^ 2 := by
  native_decide

end Ecdlp.Curve
