import Mathlib
import Ecdlp.Proved.CubeRoot
import Ecdlp.Proved.GlvAutomorphism
import Ecdlp.Proved.GlvMonoidHom
import Ecdlp.Proved.SemaevFour
import Ecdlp.Proved.SevenNonResidue

/-!
# GLV covariance of the third and fourth Semaev polynomials

For a cube root of unity `β`, simultaneous scaling of every `x`-coordinate has the
following exact effect on the `a = 0` Semaev polynomials:

* `S₃(βx₁, βx₂, βx₃) = β S₃(x₁, x₂, x₃)`;
* `S₄(βx₁, βx₂, βx₃, βx₄) = S₄(x₁, x₂, x₃, x₄)`.

The `S₄` theorem uses the exact `resultant _ _ 2 2` normalization from
`SemaevFour.lean`, including degenerate quadratic slices. These identities establish
the diagonal action only; they do not classify the full coordinatewise polynomial
stabilizer. The fixed-target theorem and certificate discussion below is `S₄`-only;
no fixed-target `S₃` classification is claimed.
-/

namespace Ecdlp.Semaev

open Polynomial

variable {F : Type*} [CommRing F]

/-- The closed formula for the resultant of two quadratic coefficient triples. -/
private def quadraticResultant
    (f₂ f₁ f₀ g₂ g₁ g₀ : F) : F :=
  f₂ ^ 2 * g₀ ^ 2
    - f₂ * f₁ * g₁ * g₀
    - 2 * f₂ * f₀ * g₂ * g₀
    + f₂ * f₀ * g₁ ^ 2
    + f₁ ^ 2 * g₂ * g₀
    - f₁ * f₀ * g₂ * g₁
    + f₀ ^ 2 * g₂ ^ 2

/-- The fixed-size `2 × 2` resultant is the closed quadratic formula, even when an
actual polynomial degree drops below two. -/
private theorem resultant_quadratic
    (f₂ f₁ f₀ g₂ g₁ g₀ : F) :
    (C f₂ * X ^ 2 + C f₁ * X + C f₀).resultant
        (C g₂ * X ^ 2 + C g₁ * X + C g₀) 2 2
      = quadraticResultant f₂ f₁ f₀ g₂ g₁ g₀ := by
  let f : F[X] := C f₂ * X ^ 2 + C f₁ * X + C f₀
  let g : F[X] := C g₂ * X ^ 2 + C g₁ * X + C g₀
  have hsylvester :
      f.sylvester g 2 2 =
        !![g₀, 0, f₀, 0;
           g₁, g₀, f₁, f₀;
           g₂, g₁, f₂, f₁;
           0, g₂, 0, f₂] := by
    ext i j
    induction j using Fin.addCases with
    | left j =>
        fin_cases i <;> fin_cases j <;>
          norm_num [f, g, Polynomial.sylvester, Fin.addCases, Fin.castAdd, Fin.castLE,
            Fin.addNat, Polynomial.coeff_X]
    | right j =>
        fin_cases i <;> fin_cases j <;>
          norm_num [f, g, Polynomial.sylvester, Fin.addCases, Fin.castAdd, Fin.castLE,
            Fin.addNat, Polynomial.coeff_X]
  change f.resultant g 2 2 = quadraticResultant f₂ f₁ f₀ g₂ g₁ g₀
  rw [Polynomial.resultant, hsylvester, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, quadraticResultant, Fin.succAbove]
  ring_nf

/-- The exact fixed-size resultant definition of `S₄` reduced to its six quadratic
slice coefficients. -/
private theorem S₄_zero_a_explicit
    (b x₁ x₂ x₃ x₄ : F) :
    S₄ 0 b x₁ x₂ x₃ x₄ =
      quadraticResultant
        ((x₁ - x₂) ^ 2)
        (-(2 * ((x₁ + x₂) * (x₁ * x₂) + 2 * b)))
        ((x₁ * x₂) ^ 2 - 4 * b * (x₁ + x₂))
        ((x₃ - x₄) ^ 2)
        (-(2 * ((x₃ + x₄) * (x₃ * x₄) + 2 * b)))
        ((x₃ * x₄) ^ 2 - 4 * b * (x₃ + x₄)) := by
  have hslice (u v : F) :
      S₃poly 0 b u v =
        C ((u - v) ^ 2) * X ^ 2
          + C (-(2 * ((u + v) * (u * v) + 2 * b))) * X
          + C ((u * v) ^ 2 - 4 * b * (u + v)) := by
    simp only [S₃poly, add_zero, sub_zero]
  rw [S₄, hslice x₁ x₂, hslice x₃ x₄, resultant_quadratic]

/-- The quadratic resultant is invariant when both coefficient triples receive
the GLV weights `(β², 1, β)`. -/
private theorem quadraticResultant_weighted_invariant
    (β f₂ f₁ f₀ g₂ g₁ g₀ : F) (hβ : β ^ 3 = 1) :
    quadraticResultant
        (β ^ 2 * f₂) f₁ (β * f₀)
        (β ^ 2 * g₂) g₁ (β * g₀)
      = quadraticResultant f₂ f₁ f₀ g₂ g₁ g₀ := by
  simp only [quadraticResultant]
  linear_combination
    ((-f₂ * f₁ * g₁ * g₀ + f₂ * f₀ * g₁ ^ 2
        + f₁ ^ 2 * g₂ * g₀ - f₁ * f₀ * g₂ * g₁)
      + (β ^ 3 + 1)
        * (f₂ ^ 2 * g₀ ^ 2 - 2 * f₂ * f₀ * g₂ * g₀ + f₀ ^ 2 * g₂ ^ 2)) * hβ

/-- Diagonal cube covariance of `S₃` over an arbitrary commutative ring. -/
theorem S₃_diagonal_cube_covariance
    (b β x₁ x₂ x₃ : F) (hβ : β ^ 3 = 1) :
    S₃ 0 b (β * x₁) (β * x₂) (β * x₃)
      = β * S₃ 0 b x₁ x₂ x₃ := by
  simp only [S₃, zero_add, sub_zero]
  linear_combination
    (β * ((x₁ - x₂) ^ 2 * x₃ ^ 2
      - 2 * (x₁ + x₂) * (x₁ * x₂) * x₃
      + (x₁ * x₂) ^ 2)) * hβ

/-- Since `β³ = 1` makes `β` a unit, diagonal scaling preserves the zero condition
of `S₃` in both directions, without requiring a domain. -/
theorem S₃_diagonal_cube_zero_iff
    (b β x₁ x₂ x₃ : F) (hβ : β ^ 3 = 1) :
    S₃ 0 b (β * x₁) (β * x₂) (β * x₃) = 0
      ↔ S₃ 0 b x₁ x₂ x₃ = 0 := by
  rw [S₃_diagonal_cube_covariance b β x₁ x₂ x₃ hβ]
  have hβinv : β ^ 2 * β = 1 := by
    simpa [pow_succ] using hβ
  constructor
  · intro h
    calc
      S₃ 0 b x₁ x₂ x₃ = (β ^ 2 * β) * S₃ 0 b x₁ x₂ x₃ := by rw [hβinv, one_mul]
      _ = β ^ 2 * (β * S₃ 0 b x₁ x₂ x₃) := by ring
      _ = 0 := by rw [h, mul_zero]
  · intro h
    rw [h, mul_zero]

/-- Diagonal cube invariance of the exact fixed-size resultant definition of `S₄`. -/
theorem S₄_diagonal_cube_invariant
    (b β x₁ x₂ x₃ x₄ : F) (hβ : β ^ 3 = 1) :
    S₄ 0 b (β * x₁) (β * x₂) (β * x₃) (β * x₄)
      = S₄ 0 b x₁ x₂ x₃ x₄ := by
  rw [S₄_zero_a_explicit b (β * x₁) (β * x₂) (β * x₃) (β * x₄),
    S₄_zero_a_explicit b x₁ x₂ x₃ x₄]
  have h₂12 :
      (β * x₁ - β * x₂) ^ 2 = β ^ 2 * (x₁ - x₂) ^ 2 := by
    ring
  have h₁12 :
      -(2 * ((β * x₁ + β * x₂) * ((β * x₁) * (β * x₂)) + 2 * b))
        = -(2 * ((x₁ + x₂) * (x₁ * x₂) + 2 * b)) := by
    linear_combination (-2 * (x₁ + x₂) * (x₁ * x₂)) * hβ
  have h₀12 :
      ((β * x₁) * (β * x₂)) ^ 2 - 4 * b * (β * x₁ + β * x₂)
        = β * ((x₁ * x₂) ^ 2 - 4 * b * (x₁ + x₂)) := by
    linear_combination (β * (x₁ * x₂) ^ 2) * hβ
  have h₂34 :
      (β * x₃ - β * x₄) ^ 2 = β ^ 2 * (x₃ - x₄) ^ 2 := by
    ring
  have h₁34 :
      -(2 * ((β * x₃ + β * x₄) * ((β * x₃) * (β * x₄)) + 2 * b))
        = -(2 * ((x₃ + x₄) * (x₃ * x₄) + 2 * b)) := by
    linear_combination (-2 * (x₃ + x₄) * (x₃ * x₄)) * hβ
  have h₀34 :
      ((β * x₃) * (β * x₄)) ^ 2 - 4 * b * (β * x₃ + β * x₄)
        = β * ((x₃ * x₄) ^ 2 - 4 * b * (x₃ + x₄)) := by
    linear_combination (β * (x₃ * x₄) ^ 2) * hβ
  rw [h₂12, h₁12, h₀12, h₂34, h₁34, h₀34]
  exact quadraticResultant_weighted_invariant β
    ((x₁ - x₂) ^ 2)
    (-(2 * ((x₁ + x₂) * (x₁ * x₂) + 2 * b)))
    ((x₁ * x₂) ^ 2 - 4 * b * (x₁ + x₂))
    ((x₃ - x₄) ^ 2)
    (-(2 * ((x₃ + x₄) * (x₃ * x₄) + 2 * b)))
    ((x₃ * x₄) ^ 2 - 4 * b * (x₃ + x₄)) hβ

/-! ### Fixed-target transport

The identities above scale *every* coordinate. The relation-generation subproblem instead fixes
the target `x₄ = r` and scales only the factor-base coordinates. Two statements must be kept
apart, because they point in opposite directions:

* the **polynomial identity** `S₄(βx₁, βx₂, βx₃, r) = S₄(x₁, x₂, x₃, β²r)` — scaling the
  coordinates by `β` is the same as scaling the target by `β⁻¹ = β²`;
* the **induced map on solution fibres** `x ↦ βx`, which sends a solution at target `r` to a
  solution at target `βr` — i.e. it transports the problem for `R` to the problem for `φ(R)`,
  **not** `φ²(R)`.

Reading the exponent of the first statement as the direction of the second is a genuine error;
`S₄_glv_fibre_transport` below fixes the direction by deriving it from full diagonal invariance
rather than from the transport identity.

These theorems establish that a nonidentity diagonal scaling *moves* the target. They do **not**
classify the full coordinatewise stabilizer of an `S₄` fixed-target slice; that
classification remains certificate-backed (see `experiments/glv_semaev_symmetry/`), and the
blocker is recorded in the module docstring. -/

/-- **Target transport.** Scaling only the three factor-base coordinates by `β` is exactly the
same as scaling the target by `β²`. -/
theorem S₄_glv_target_transport
    (b β x₁ x₂ x₃ x₄ : F) (hβ : β ^ 3 = 1) :
    S₄ 0 b (β * x₁) (β * x₂) (β * x₃) x₄
      = S₄ 0 b x₁ x₂ x₃ (β ^ 2 * x₄) := by
  rw [S₄_zero_a_explicit b (β * x₁) (β * x₂) (β * x₃) x₄,
    S₄_zero_a_explicit b x₁ x₂ x₃ (β ^ 2 * x₄)]
  -- first slice: the pair `(x₁, x₂)` is fully scaled, exactly as in the diagonal case
  have h₂12 : (β * x₁ - β * x₂) ^ 2 = β ^ 2 * (x₁ - x₂) ^ 2 := by ring
  have h₁12 :
      -(2 * ((β * x₁ + β * x₂) * ((β * x₁) * (β * x₂)) + 2 * b))
        = -(2 * ((x₁ + x₂) * (x₁ * x₂) + 2 * b)) := by
    linear_combination (-2 * (x₁ + x₂) * (x₁ * x₂)) * hβ
  have h₀12 :
      ((β * x₁) * (β * x₂)) ^ 2 - 4 * b * (β * x₁ + β * x₂)
        = β * ((x₁ * x₂) ^ 2 - 4 * b * (x₁ + x₂)) := by
    linear_combination (β * (x₁ * x₂) ^ 2) * hβ
  -- second slice: `x₃` is scaled but the target is not; the same `(β², 1, β)` weights appear
  -- against the *transported* pair `(x₃, β²x₄)`
  have h₂34 :
      (β * x₃ - x₄) ^ 2 = β ^ 2 * (x₃ - β ^ 2 * x₄) ^ 2 := by
    linear_combination (-(β ^ 3) * x₄ ^ 2 + 2 * β * x₃ * x₄ - x₄ ^ 2) * hβ
  have h₁34 :
      -(2 * ((β * x₃ + x₄) * ((β * x₃) * x₄) + 2 * b))
        = -(2 * ((x₃ + β ^ 2 * x₄) * (x₃ * (β ^ 2 * x₄)) + 2 * b)) := by
    linear_combination (2 * β * x₃ * x₄ ^ 2) * hβ
  have h₀34 :
      ((β * x₃) * x₄) ^ 2 - 4 * b * (β * x₃ + x₄)
        = β * ((x₃ * (β ^ 2 * x₄)) ^ 2 - 4 * b * (x₃ + β ^ 2 * x₄)) := by
    linear_combination (-(β ^ 2) * x₃ ^ 2 * x₄ ^ 2 + 4 * b * x₄) * hβ
  rw [h₂12, h₁12, h₀12, h₂34, h₁34, h₀34]
  exact quadraticResultant_weighted_invariant β
    ((x₁ - x₂) ^ 2)
    (-(2 * ((x₁ + x₂) * (x₁ * x₂) + 2 * b)))
    ((x₁ * x₂) ^ 2 - 4 * b * (x₁ + x₂))
    ((x₃ - β ^ 2 * x₄) ^ 2)
    (-(2 * ((x₃ + β ^ 2 * x₄) * (x₃ * (β ^ 2 * x₄)) + 2 * b)))
    ((x₃ * (β ^ 2 * x₄)) ^ 2 - 4 * b * (x₃ + β ^ 2 * x₄)) hβ

/-- **Fibre transport, with the direction fixed.** A solution at target `r` maps to a solution at
target `βr` — the problem for `R` is carried to the problem for `φ(R)`. Derived from full
diagonal invariance, so the exponent of `S₄_glv_target_transport` cannot mislead here. -/
theorem S₄_glv_fibre_transport
    (b β x₁ x₂ x₃ r : F) (hβ : β ^ 3 = 1) :
    S₄ 0 b x₁ x₂ x₃ r = 0
      ↔ S₄ 0 b (β * x₁) (β * x₂) (β * x₃) (β * r) = 0 := by
  rw [S₄_diagonal_cube_invariant b β x₁ x₂ x₃ r hβ]

/-- A nonidentity scaling moves a nonzero target. Together with `S₄_glv_fibre_transport` this is
the precise sense in which the diagonal GLV action **transports** the fixed-target relation
problem instead of preserving it: the image fibre sits over `βr ≠ r`. -/
theorem glv_target_ne_self {F : Type*} [CommRing F] [NoZeroDivisors F]
    (β r : F) (hβ : β ≠ 1) (hr : r ≠ 0) :
    β * r ≠ r := by
  intro h
  refine hβ ?_
  have hfac : (β - 1) * r = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h₁ | h₂
  · linear_combination h₁
  · exact absurd h₂ hr

/-- The secp256k1 GLV field factor is a cube root of unity in its base field. -/
private theorem secp256k1_beta_cube :
    (Secp256k1.beta : ZMod Secp256k1.p) ^ 3 = 1 := by
  have hβeig : (Secp256k1.beta : ZMod Secp256k1.p) ^ 2
      + (Secp256k1.beta : ZMod Secp256k1.p) + 1 = 0 := by
    have h0 :
        ((Secp256k1.beta ^ 2 + Secp256k1.beta + 1 : ℕ) :
          ZMod Secp256k1.p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero Secp256k1.beta_field_eigenvalue
    push_cast at h0
    linear_combination h0
  exact Ecdlp.Proved.cube_root_of_eigenvalue _ hβeig

/-- Exact `S₃` GLV covariance for secp256k1 (`a = 0`, `b = 7`). -/
theorem secp256k1_S₃_glv_covariance
    (x₁ x₂ x₃ : ZMod Secp256k1.p) :
    S₃ 0 7
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₁)
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₂)
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₃)
      = (Secp256k1.beta : ZMod Secp256k1.p) * S₃ 0 7 x₁ x₂ x₃ :=
  S₃_diagonal_cube_covariance 7 _ x₁ x₂ x₃ secp256k1_beta_cube

/-- The corresponding secp256k1 `S₃ = 0` equivalence. -/
theorem secp256k1_S₃_glv_zero_iff
    (x₁ x₂ x₃ : ZMod Secp256k1.p) :
    S₃ 0 7
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₁)
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₂)
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₃) = 0
      ↔ S₃ 0 7 x₁ x₂ x₃ = 0 :=
  S₃_diagonal_cube_zero_iff 7 _ x₁ x₂ x₃ secp256k1_beta_cube

/-- Exact `S₄` diagonal GLV invariance for secp256k1 (`a = 0`, `b = 7`). -/
theorem secp256k1_S₄_glv_invariant
    (x₁ x₂ x₃ x₄ : ZMod Secp256k1.p) :
    S₄ 0 7
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₁)
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₂)
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₃)
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₄)
      = S₄ 0 7 x₁ x₂ x₃ x₄ :=
  S₄_diagonal_cube_invariant 7 _ x₁ x₂ x₃ x₄ secp256k1_beta_cube

/-- The secp256k1 GLV factor is a *primitive* cube root: `β = 1` would force `3 = 0` in `𝔽_p`. -/
private theorem secp256k1_beta_ne_one :
    (Secp256k1.beta : ZMod Secp256k1.p) ≠ 1 := by
  have hβeig : (Secp256k1.beta : ZMod Secp256k1.p) ^ 2
      + (Secp256k1.beta : ZMod Secp256k1.p) + 1 = 0 := by
    have h0 :
        ((Secp256k1.beta ^ 2 + Secp256k1.beta + 1 : ℕ) :
          ZMod Secp256k1.p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero Secp256k1.beta_field_eigenvalue
    push_cast at h0
    linear_combination h0
  have h3 : (3 : ZMod Secp256k1.p) ≠ 0 := by
    have h : ((3 : ℕ) : ZMod Secp256k1.p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; norm_num [Secp256k1.p]
    simpa using h
  intro h1
  exact h3 (by linear_combination hβeig - (Secp256k1.beta + 2 : ZMod Secp256k1.p) * h1)

/-- Exact secp256k1 target transport: scaling the three factor-base coordinates by `β` is the
same as scaling the target by `β²`. -/
theorem secp256k1_S₄_glv_target_transport
    (x₁ x₂ x₃ x₄ : ZMod Secp256k1.p) :
    S₄ 0 7
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₁)
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₂)
        ((Secp256k1.beta : ZMod Secp256k1.p) * x₃)
        x₄
      = S₄ 0 7 x₁ x₂ x₃ ((Secp256k1.beta : ZMod Secp256k1.p) ^ 2 * x₄) :=
  S₄_glv_target_transport 7 _ x₁ x₂ x₃ x₄ secp256k1_beta_cube

/-- Exact secp256k1 fibre transport, direction `r ↦ βr` (i.e. `R ↦ φ(R)`). -/
theorem secp256k1_S₄_glv_fibre_transport
    (x₁ x₂ x₃ r : ZMod Secp256k1.p) :
    S₄ 0 7 x₁ x₂ x₃ r = 0
      ↔ S₄ 0 7
          ((Secp256k1.beta : ZMod Secp256k1.p) * x₁)
          ((Secp256k1.beta : ZMod Secp256k1.p) * x₂)
          ((Secp256k1.beta : ZMod Secp256k1.p) * x₃)
          ((Secp256k1.beta : ZMod Secp256k1.p) * r) = 0 :=
  S₄_glv_fibre_transport 7 _ x₁ x₂ x₃ r secp256k1_beta_cube

/-- **The fixed-target scope statement for secp256k1.** For a nonzero target coordinate the
diagonal GLV scaling carries the relation problem to a *different* target, `βr ≠ r`. Combined
with `secp256k1_S₄_glv_fibre_transport`, the diagonal action transports the fixed-target problem
rather than preserving it.

Scope, stated exactly: `r` ranges over field elements, so this covers precisely the **affine**
targets (a target at the point at infinity has no `x`-coordinate and is outside the statement).
The hypothesis `r ≠ 0` is the `r = 0` exceptional locus of the certificate.
`secp256k1_glv_affine_target_moves` below discharges it for every affine
`𝔽_p`-rational secp256k1 target. -/
theorem secp256k1_glv_fixed_target_moves
    [Fact (Nat.Prime Secp256k1.p)]
    (r : ZMod Secp256k1.p) (hr : r ≠ 0) :
    (Secp256k1.beta : ZMod Secp256k1.p) * r ≠ r :=
  glv_target_ne_self _ r secp256k1_beta_ne_one hr

/-- Every affine secp256k1 target over the base field has nonzero `x`-coordinate,
so the nonidentity diagonal GLV scaling moves it to a different target.

This is an arithmetic corollary about the diagonal action. The exhaustive
fixed-target `S₄` coordinate-scaling classification remains certificate-backed;
this theorem does not cover the point at infinity, extension-field targets, or
non-scalar and birational automorphisms. -/
theorem secp256k1_glv_affine_target_moves
    [Fact (Nat.Prime Secp256k1.p)]
    {x y : ZMod Secp256k1.p}
    (h : Ecdlp.Curve.secp256k1.toAffine.Nonsingular x y) :
    (Secp256k1.beta : ZMod Secp256k1.p) * x ≠ x :=
  secp256k1_glv_fixed_target_moves x
    (Ecdlp.Curve.secp256k1_x_ne_zero h)

end Ecdlp.Semaev

namespace Ecdlp.Curve

open WeierstrassCurve.Affine

variable [Fact (Nat.Prime Secp256k1.p)]

/-- Applying the GLV automorphism to every point gives an equivalent finite relation.
This is a bijective transport of a relation, not a reduction in relation count. -/
theorem secp256k1_glv_list_sum_eq_iff
    (points : List secp256k1.toAffine.Point)
    (R : secp256k1.toAffine.Point) :
    points.sum = R ↔ (points.map glvHom).sum = glvHom R := by
  have hmap : (points.map glvHom).sum = glvHom points.sum := by
    induction points with
    | nil =>
        simp only [List.map_nil, List.sum_nil, map_zero]
    | cons P points ih =>
        simp only [List.map_cons, List.sum_cons, ih, map_add]
  rw [hmap]
  constructor
  · exact congrArg glvHom
  · intro h
    apply glvPoint_bijective.1
    simpa only [glvHom_apply] using h

/-- Three-point specialization of `secp256k1_glv_list_sum_eq_iff`. -/
theorem secp256k1_glv_three_point_sum_eq_iff
    (P₁ P₂ P₃ R : secp256k1.toAffine.Point) :
    P₁ + P₂ + P₃ = R
      ↔ glvPoint P₁ + glvPoint P₂ + glvPoint P₃ = glvPoint R := by
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    add_assoc, glvHom_apply] using
    (secp256k1_glv_list_sum_eq_iff [P₁, P₂, P₃] R)

end Ecdlp.Curve
