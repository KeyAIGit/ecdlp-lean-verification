import Mathlib
import Ecdlp.Proved.Secp256k1Curve
import Ecdlp.Proved.CurveTorsion
import Ecdlp.Proved.CurveCardinalityExact

/-!
# ECDSA signature malleability — the algebraic core of BIP-146 low-`s`

Every ECDSA signature `(r, s)` has a *sibling* `(r, −s)` (i.e. `(r, n − s)` in `ZMod n`) that
verifies against the same message and public key. This non-uniqueness is **signature
malleability** — the reason Bitcoin's BIP-62 rule 5 / BIP-146 (and, as library policy,
implementations such as libsecp256k1) normalize to "low `s`": third parties could flip `s ↦ n − s` on any ECDSA signature and
obtain a *different* valid encoding of the same authorization (a source of transaction-ID
malleation before SegWit).

This file records the two machine-checkable halves of that fact, in the repo's established
identity-level style (`ABSTRACT_SCOPE.md`: no adversary, no hash, no probability space —
the *algebra* of the attack, not a protocol-security statement):

* **Signing side (abstract field).** The signing equation `s·k = z + r·x` is satisfied by
  the sibling pair `(−s, −k)`: `(−s)·(−k) = z + r·x` (`ecdsa_sibling_signing_equation`).
  The sibling signature is the one the signer *would* have produced with nonce `−k` — and
  `(−k)·G = −(k·G)` has the same `x`-coordinate, so `r` is unchanged.
* **Verifier side (concrete secp256k1).** The verifier accepts `(r, s)` iff
  `r = x((z/s)·G + (r/s)·P)`. Negating `s` negates both scalars (`a / (−s) = −(a / s)`,
  `ecdsa_sibling_scalars`), which negates the verification point
  (`secp256k1_pointX_neg_zsmul_add`) — and point negation on secp256k1 **fixes the
  `x`-coordinate** (`secp256k1_pointX_neg`: `−(x, y) = (x, −y)` since `a₁ = a₃ = 0`), so the
  sibling's verification point yields the same `r`.

The `x`-projection is `pointX : E(𝔽_p) → Option (ZMod p)` (`none` at infinity). What is
**not** claimed: no formalized `Verify` predicate, no statement about hash truncation, the
real verifier's `ZMod p → ZMod n` reduction of the `x`-coordinate before comparing with `r`,
DER/encoding-level malleability, or uniqueness after low-`s` normalization.

Trust note: no `native_decide` appears in this file, and the field-side lemmas are
pure-kernel. The curve-coordinate lemmas `secp256k1_pointX_neg` and
`secp256k1_pointX_neg_zsmul_add` are stated under
`[Fact (Nat.Prime Secp256k1.p)]` (the repo convention); discharging that fact downstream
uses the Pratt certificate (`Secp256k1PrimeP.lean`), whose arithmetic leaves are checked
by the kernel (`decide +kernel`). The concrete theorem `secp256k1_pointX_not_injective`
additionally invokes `secp256k1_no_nonzero_two_torsion`, whose certificate in
`CurveCardinalityExact.lean` is likewise kernel-checked. The ledger axiom audit shows
these results depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Ecdlp.Curve

open WeierstrassCurve.Affine

variable [Fact (Nat.Prime Secp256k1.p)]

/-- The affine `x`-coordinate projection on secp256k1 points (`none` at infinity). This is
the map the ECDSA verifier applies to the verification point to compare against `r`. -/
def pointX : secp256k1.toAffine.Point → Option (ZMod Secp256k1.p)
  | .zero => none
  | .some x _ _ => some x

@[simp] theorem pointX_zero : pointX (0 : secp256k1.toAffine.Point) = none := rfl

@[simp] theorem pointX_some (x y : ZMod Secp256k1.p)
    (h : secp256k1.toAffine.Nonsingular x y) :
    pointX (Point.some x y h) = some x := rfl

/-- **Point negation preserves the `x`-coordinate on secp256k1.** For `a₁ = a₃ = 0` curves,
`−(x, y) = (x, −y)`; the projective point at infinity is its own negative. This is the
geometric half of ECDSA malleability: the negated verification point reports the same `r`. -/
theorem secp256k1_pointX_neg (P : secp256k1.toAffine.Point) :
    pointX (-P) = pointX P := by
  cases P with
  | zero => rfl
  | some x y h => rw [Point.neg_some]; rfl

/-- **The secp256k1 `x`-coordinate projection is not injective.** The concrete
points `G` and `-G` have the same `pointX`, but they are distinct: equality
would make `G` a nonzero two-torsion point. This is a narrow representation
boundary, not an ECDLP algorithm or a claim that every structured generic-group
model must use `pointX` as its label map. -/
theorem secp256k1_pointX_not_injective :
    ¬ Function.Injective pointX := by
  intro hInjective
  have hneg : -secp256k1_G = secp256k1_G :=
    hInjective (secp256k1_pointX_neg secp256k1_G)
  have htwo : (2 : ℕ) • secp256k1_G = 0 := by
    calc
      (2 : ℕ) • secp256k1_G =
          secp256k1_G + secp256k1_G := two_nsmul secp256k1_G
      _ = secp256k1_G + (-secp256k1_G) :=
        congrArg
          (fun P : secp256k1.toAffine.Point => secp256k1_G + P)
          hneg.symm
      _ = 0 := add_neg_cancel secp256k1_G
  exact secp256k1_G_ne_zero
    (secp256k1_no_nonzero_two_torsion secp256k1_G htwo)

/-- **Negating both verification scalars negates the verification point — and keeps its
`x`-coordinate.** For any `c₁ c₂ : ℤ` and points `G P`:
`x((−c₁)·G + (−c₂)·P) = x(c₁·G + c₂·P)`. With `c₁ = z/s`, `c₂ = r/s` lifted to integers,
this is exactly the verifier-side step of the `(r, s) ↦ (r, −s)` malleation. -/
theorem secp256k1_pointX_neg_zsmul_add (c₁ c₂ : ℤ) (G P : secp256k1.toAffine.Point) :
    pointX ((-c₁) • G + (-c₂) • P) = pointX (c₁ • G + c₂ • P) := by
  rw [neg_zsmul, neg_zsmul, ← neg_add, secp256k1_pointX_neg]

end Ecdlp.Curve

namespace Ecdlp.Schnorr

variable {F : Type*} [Field F]

/-- **The sibling signature satisfies the signing equation.** If `s·k = z + r·x` (the ECDSA
signing identity for nonce `k`, hash `z`, private key `x`), then the sibling pair
`(−s, −k)` satisfies the *same* equation: `(−s)·(−k) = z + r·x`. Since `(−k)·G = −(k·G)`
has the same `x`-coordinate (`secp256k1_pointX_neg`), the sibling's `r` is unchanged —
so `(r, −s)` is a well-formed signature on the same message under the same key. -/
theorem ecdsa_sibling_signing_equation {k x r z s : F}
    (h : s * k = z + r * x) : (-s) * (-k) = z + r * x := by
  linear_combination h

/-- **Negating `s` negates both verification scalars.** The ECDSA verifier computes
`u₁ = z/s`, `u₂ = r/s`; for the sibling `−s` these become `−u₁`, `−u₂` — the scalars of
the negated verification point. (A division-ring identity; no `s ≠ 0` hypothesis needed,
as both sides are `0` when `s = 0`.) -/
theorem ecdsa_sibling_scalars (z r s : F) :
    z / (-s) = -(z / s) ∧ r / (-s) = -(r / s) :=
  ⟨div_neg z, div_neg r⟩

end Ecdlp.Schnorr
