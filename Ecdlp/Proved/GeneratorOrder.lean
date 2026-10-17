import Ecdlp.Proved.GlvEndomorphism
import Ecdlp.Proved.Secp256k1PrimeP
import Ecdlp.Proved.Secp256k1PrimeN
import Ecdlp.Proved.KernelScalarMul

/-!
# The secp256k1 base point: exact order `n` and the GLV eigenvalue at `G`

Two kernel-verified facts about the SEC2 generator `G = (Gx, Gy)`, realized as an element
of Mathlib's elliptic-curve point group `secp256k1.toAffine.Point`:

* `secp256k1_generator_addOrderOf : addOrderOf secp256k1G = Secp256k1.n` — `G` has *exact*
  order `n` (the published prime group order), so `⟨G⟩` is cyclic of order `n`. This is the
  **weak point-counting keystone**: it pins the cryptographic subgroup without computing
  `#E(𝔽_p)` (no Hasse/Schoof), which `notes/POINT_COUNTING_KEYSTONE.md` had billed as the
  multi-month-blocked node.
* `secp256k1_glvPoint_generator : glvPoint secp256k1G = (Secp256k1.lam : ℕ) • secp256k1G` —
  the GLV endomorphism acts as the scalar `[λ]` **at the generator** (the eigenvalue
  identity that `GlvEigenvalue.lean` could only state *conditional on* whole-group
  cyclicity). The other cube root `λ²` is ruled out (checked false).

Both are checked by the Lean kernel alone (no `Lean.ofReduceBool`): the scalar multiples
`[n]G` and `[λ]G` are evaluated by the kernel on reduced `ℕ` coordinates
(`Ecdlp.Kernel.mulN`, `decide +kernel`; `KernelScalarMul.lean`), and the kernel-checked
bridge `Ecdlp.Kernel.mulN_rep` transports the result to Mathlib's point group. On their own
they do **not** give the *strong* keystone `#E(𝔽_p) = n` (cofactor 1) — this is the
base-point subgroup `⟨G⟩`; the whole rational-point group is handled in
`CurveCardinalityExact.lean` (`secp256k1_card_point_eq_n`).
-/

open WeierstrassCurve.Affine

namespace Ecdlp.Curve

/-- The secp256k1 base point `G = (Gx, Gy)` as an element of the Mathlib point group. -/
def secp256k1G : secp256k1.toAffine.Point :=
  Point.some (Secp256k1.Gx : ZMod Secp256k1.p) (Secp256k1.Gy : ZMod Secp256k1.p)
    secp256k1_generator_nonsingular

/-- The base point `G0` on `ℕ` coordinates represents `secp256k1G`. -/
theorem secp256k1_rep_G0 : Ecdlp.Kernel.Rep Ecdlp.Kernel.G0 secp256k1G :=
  ⟨Nat.mod_lt _ (by decide +kernel), Nat.mod_lt _ (by decide +kernel),
    Ecdlp.Kernel.some_congr secp256k1_generator_nonsingular (ZMod.natCast_mod _ _).symm
      (ZMod.natCast_mod _ _).symm⟩

-- Keep the elaborator from unfolding the 256-bit chains; only the kernel evaluates them
-- (inside `Ecdlp.Kernel.mulN_G0_n` / `mulN_G0_lam`).
attribute [local irreducible] Ecdlp.Kernel.mulN Ecdlp.Kernel.addN Ecdlp.Kernel.G0

/-- `n • G = 0`: the published prime order annihilates the base point. Kernel-checked:
`[n]G` is evaluated by the kernel on `ℕ` coordinates (`Ecdlp.Kernel.mulN_G0_n`) and
transported by `Ecdlp.Kernel.mulN_rep`. -/
theorem secp256k1_generator_nsmul_n_eq_zero :
    (Secp256k1.n : ℕ) • secp256k1G = 0 :=
  (congrArg (fun R => Ecdlp.Kernel.Rep R ((Secp256k1.n : ℕ) • secp256k1G))
    Ecdlp.Kernel.mulN_G0_n).mp
    (Ecdlp.Kernel.mulN_rep secp256k1_rep_G0 256 Secp256k1.n Ecdlp.Kernel.n_lt_two_pow_256)

/-- The base point is not the group identity (it is an affine point). -/
theorem secp256k1_generator_ne_zero : secp256k1G ≠ 0 :=
  Point.some_ne_zero _

/-- **The secp256k1 base point has exact order `n`** (the published prime group order), so
`⟨G⟩` is cyclic of order `n` — the weak point-counting keystone (no Hasse / `#E` needed). -/
theorem secp256k1_generator_addOrderOf :
    addOrderOf secp256k1G = Secp256k1.n :=
  addOrderOf_eq_prime secp256k1_generator_nsmul_n_eq_zero secp256k1_generator_ne_zero

/-- **The GLV endomorphism acts as `[λ]` at the generator:** `glvPoint G = λ • G`.
Unlike `secp256k1_glvHom_eq_zsmul` (conditional on whole-group cyclicity) this is the
unconditional coordinate identity at `G` itself. Kernel-checked: `[λ]G = (β·Gx, Gy)` is
evaluated by the kernel on `ℕ` coordinates (`Ecdlp.Kernel.mulN_G0_lam`) and transported by
`Ecdlp.Kernel.mulN_rep`. -/
theorem secp256k1_glvPoint_generator :
    glvPoint secp256k1G = (Secp256k1.lam : ℕ) • secp256k1G := by
  have h := (congrArg (fun R => Ecdlp.Kernel.Rep R ((Secp256k1.lam : ℕ) • secp256k1G))
    Ecdlp.Kernel.mulN_G0_lam).mp
    (Ecdlp.Kernel.mulN_rep secp256k1_rep_G0 256 Secp256k1.lam Ecdlp.Kernel.lam_lt_two_pow_256)
  obtain ⟨-, -, hns, hA⟩ := h
  rw [hA, secp256k1G, glvPoint_some]
  congr 1

end Ecdlp.Curve
