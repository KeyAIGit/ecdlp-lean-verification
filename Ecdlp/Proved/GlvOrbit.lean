import Mathlib
import Ecdlp.Proved.Secp256k1Curve
import Ecdlp.Proved.GlvEndomorphism
import Ecdlp.Proved.GlvCubeRelation
import Ecdlp.Proved.GlvAutomorphism
import Ecdlp.Proved.GlvFixedLocus

/-!
# The orbit structure of the GLV automorphism of secp256k1

`glvPoint : (x, y) ↦ (β·x, y)` is a primitive cube root of unity in `End(E)`: it satisfies
`glvPoint² + glvPoint + 1 = 0` on every point (`secp256k1_glv_cube_relation`,
`Ecdlp/Proved/GlvCubeRelation.lean`). This file draws the group-theoretic consequence — the
map has order dividing 3 as a permutation of the point group, so its orbits have size
at most 3.

## What is proved here

Building on `glvPoint_cube_eq_id` (`glvPoint³ = id`, already proved in
`Ecdlp/Proved/GlvAutomorphism.lean` — the automorphism has order dividing 3, so its orbits
have size dividing 3), this file adds the **orbit structure**:

* `secp256k1_glvPoint_orbit_closed` : the three-element set `{P, glvPoint P,
  glvPoint (glvPoint P)}` is closed under `glvPoint` (membership is stated as a
  disjunction, so no `Finset`/`DecidableEq` machinery is needed). Applying `glvPoint`
  cycles `P ↦ glvPoint P ↦ glvPoint² P ↦ P`.

* `secp256k1_glvPoint_orbit_three_distinct` : for a non-fixed affine point `(x, y)` with
  `x ≠ 0`, the three orbit elements are pairwise distinct, so the orbit has exactly 3
  elements. Fixedness is controlled by `secp256k1_glvPoint_fixed_iff` (fixed iff `x = 0`).

## Honest scope — what this means for the ECDLP

This orbit structure is the **group root** of the measured `~3x` GLV constant in the
experiments P0 through P4 (HYP_GLV_SEMAEV_001). An orbit size of at most 3 means the
GLV automorphism partitions the group (away from its `x = 0` fixed locus) into orbits of
3 collinear points sharing a `Y`-coordinate. In a Semaev / index-calculus factor base one
can therefore keep one representative per orbit and recover the other two for free — at
most a `3x` compression of the factor base. That is a **constant factor**, never a change
of exponent: the asymptotic hardness of the ECDLP on secp256k1 is untouched. This is NOT
an ECDLP advantage. (Still no `λ`, no point counting; see `notes/GLV_LAMBDA.md`.)
-/

namespace Ecdlp.Curve

open WeierstrassCurve.Affine

variable [Fact (Nat.Prime Secp256k1.p)]

/-- **The orbit `{P, glvPoint P, glvPoint² P}` is closed under `glvPoint`.** If `Q` is one
of the three orbit points then so is `glvPoint Q`; concretely `glvPoint` cycles
`P ↦ glvPoint P ↦ glvPoint² P ↦ P` (the last step is `glvPoint_cube_eq_id`).
Membership is phrased as a disjunction, so no `Finset`/`DecidableEq` is required. -/
theorem secp256k1_glvPoint_orbit_closed (P Q : secp256k1.toAffine.Point)
    (hQ : Q = P ∨ Q = glvPoint P ∨ Q = glvPoint (glvPoint P)) :
    glvPoint Q = P ∨ glvPoint Q = glvPoint P
      ∨ glvPoint Q = glvPoint (glvPoint P) := by
  rcases hQ with rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl (glvPoint_cube_eq_id P)

/-- **A non-fixed orbit has exactly 3 distinct elements.** For an affine point `(x, y)`
with `x ≠ 0` (so it is not fixed, by `secp256k1_glvPoint_fixed_iff`), the three orbit
points `P`, `glvPoint P`, `glvPoint² P` are pairwise distinct. Hence orbits away from the
`x = 0` fixed locus all have size exactly 3 — the sharp form of the "orbit size ≤ 3"
statement, and the group root of the constant `~3x` GLV factor-base compression. -/
theorem secp256k1_glvPoint_orbit_three_distinct
    (x y : ZMod Secp256k1.p) (h : secp256k1.toAffine.Nonsingular x y)
    (hx0 : x ≠ 0) :
    glvPoint (Point.some x y h) ≠ Point.some x y h
    ∧ glvPoint (glvPoint (Point.some x y h)) ≠ glvPoint (Point.some x y h)
    ∧ glvPoint (glvPoint (Point.some x y h)) ≠ Point.some x y h := by
  -- β ≠ 0 in 𝔽_p (from β² + β + 1 = 0), lifted from the machine-checked Nat eigenvalue fact.
  have hβ0 : (Secp256k1.beta : ZMod Secp256k1.p) ≠ 0 := by
    have hβeig : (Secp256k1.beta : ZMod Secp256k1.p) ^ 2
        + (Secp256k1.beta : ZMod Secp256k1.p) + 1 = 0 := by
      have h0 : ((Secp256k1.beta ^ 2 + Secp256k1.beta + 1 : ℕ) : ZMod Secp256k1.p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact Nat.dvd_of_mod_eq_zero Secp256k1.beta_field_eigenvalue_kernel
      push_cast at h0; linear_combination h0
    intro hb; rw [hb] at hβeig; norm_num at hβeig
  have hβx0 : (Secp256k1.beta : ZMod Secp256k1.p) * x ≠ 0 := mul_ne_zero hβ0 hx0
  -- (1) glvPoint P ≠ P : P has x ≠ 0, so it is not fixed.
  have d1 : glvPoint (Point.some x y h) ≠ Point.some x y h :=
    fun heq => hx0 ((secp256k1_glvPoint_fixed_iff x y h).mp heq)
  -- (2) glvPoint² P ≠ glvPoint P : glvPoint P = (β·x, y) has x-coord β·x ≠ 0, not fixed.
  have d2 : glvPoint (glvPoint (Point.some x y h)) ≠ glvPoint (Point.some x y h) := by
    rw [glvPoint_some]
    intro heq
    exact hβx0 ((secp256k1_glvPoint_fixed_iff _ y _).mp heq)
  -- (3) glvPoint² P ≠ P : else apply glvPoint and use glvPoint³ = id to force glvPoint P = P.
  have d3 : glvPoint (glvPoint (Point.some x y h)) ≠ Point.some x y h := by
    intro heq
    apply d1
    have hcong := congrArg glvPoint heq
    rw [glvPoint_cube_eq_id] at hcong
    exact hcong.symm
  exact ⟨d1, d2, d3⟩

end Ecdlp.Curve
