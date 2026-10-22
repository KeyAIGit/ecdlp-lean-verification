import Mathlib
import Ecdlp.Proved.SemaevFour

/-!
# The general Semaev tower `Sₘ`: definition, low levels, degree bound, forward direction

Semaev's summation polynomials for `y² = x³ + a·x + b` satisfy the resultant recursion
`Sₘ(x₀,…,x_{m−1}) = Res_T(S_{m−1}(x₀,…,x_{m−3},T), S₃(x_{m−2},x_{m−1},T))`.
This module defines the whole family over an arbitrary commutative ring by that recursion, with
explicit fixed Sylvester sizes:

* `semaevSlice a b x s` is `S_{s+3}(x 0, …, x (s+1), Y)` as a polynomial in its last
  variable `Y`. Level `0` is `S₃poly a b (x 0) (x 1)`; level `s+1` is the resultant, in an
  auxiliary variable `T`, of the previous slice (as a polynomial in `T`) and `S₃(x (s+2), Y, T)`
  (`stepPoly`), with Sylvester sizes `(2^(s+1), 2)`.
* `Sm a b m x = (semaevSlice a b x (m−3)).eval (x (m−1))`, meaningful for `m ≥ 3`. For
  `m < 3` the truncated subtraction makes it the level-0 slice evaluated at `x (m−1)`; the
  statements below are true there too but say nothing about Semaev polynomials.

Proved here:
* `semaevSlice_succ_eval`: evaluating the new variable gives the scalar resultant step;
* `Sm_three`, `Sm_four`: agreement with `S₃` (`SemaevThree.lean`) and with `S₄`
  (`SemaevFour.lean`), argument order kept;
* `semaevSlice_natDegree_le`: `deg_Y ≤ 2^(s+1)`, i.e. `deg ≤ 2^(m−2)` in the last variable
  of `Sₘ`, over any commutative ring (a column-weight bound on the Sylvester determinant,
  `natDegree_det_le_sum_col`);
* `semaevSlice_eval_eq_zero_of_chain`, `Sm_eq_zero_of_chain`: the forward direction at every
  level: a chain of `S₃` witnesses forces the slice, and `Sₘ`, to vanish. Each step is an
  instance of `resultant_eq_zero_of_common_root`, which needs the degree bound above.

Not proved here: the exact degree for `m ≥ 5`, the reverse direction, symmetry for `m ≥ 5`,
and any statement about curve points. The secp256k1-specific projective family in
`FrozenRecursiveProjectiveSemaev.lean` is a separate construction and is not connected to
this one here.

Reuse and precedents. `S₃`, `S₃poly`, `S₃poly_eval`, `S₃poly_natDegree_le`, `S₄` and
`resultant_eq_zero_of_common_root` are reused from `SemaevThree.lean`/`SemaevFour.lean`. Two
lemmas here have close precedents in `FrozenRecursiveProjectiveSemaev.lean`, which this module
does not import: `natDegree_det_le_sum_col` is the column-weight, commutative-ring version of
`Ecdlp.FrozenProjectiveSemaev.natDegree_det_le_sum_row` (row weights, over a field), and
`semaevSlice_natDegree_le` is the general-`(a,b)` affine analogue of the secp256k1 frozen-family
bound `Ecdlp.FrozenProjectiveSemaev.previousSliceAtOver_frozenC_natDegree_le` (the same bound
`2^(s+1)`, proved there through `taskSylvester_natDegree_le_two_mul_left`).
-/

namespace Ecdlp.Semaev

open Polynomial

variable {F : Type*} [CommRing F]

/-- `S₃poly` commutes with mapping the coefficients along a ring homomorphism. -/
theorem S₃poly_map {G : Type*} [CommRing G] (φ : F →+* G) (a b x₁ x₂ : F) :
    (S₃poly a b x₁ x₂).map φ = S₃poly (φ a) (φ b) (φ x₁) (φ x₂) := by
  simp [S₃poly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_ofNat]

/-- The right operand of one tower step: `S₃(x, Y, T)` as a polynomial in the outer variable
`T` with coefficients in `F[Y]` (the inner variable `Y` is the new last argument). -/
noncomputable def stepPoly (a b x : F) : F[X][X] :=
  S₃poly (C a) (C b) (C x) X

/-- `semaevSlice a b x s = S_{s+3}(x 0, …, x (s+1), Y)` as a polynomial in `Y`. -/
noncomputable def semaevSlice (a b : F) (x : ℕ → F) : ℕ → F[X]
  | 0 => S₃poly a b (x 0) (x 1)
  | s + 1 => ((semaevSlice a b x s).map C).resultant (stepPoly a b (x (s + 2))) (2 ^ (s + 1)) 2

/-- `Sₘ(x 0, …, x (m−1))`, meaningful for `m ≥ 3` (for `m < 3` it is the level-0 slice
evaluated at `x (m−1)`, not a Semaev polynomial). -/
noncomputable def Sm (a b : F) (m : ℕ) (x : ℕ → F) : F :=
  (semaevSlice a b x (m - 3)).eval (x (m - 1))

/-- One tower step after evaluating the new last variable at `y`. -/
theorem semaevSlice_succ_eval (a b : F) (x : ℕ → F) (s : ℕ) (y : F) :
    (semaevSlice a b x (s + 1)).eval y
      = (semaevSlice a b x s).resultant (S₃poly a b (x (s + 2)) y) (2 ^ (s + 1)) 2 := by
  rw [semaevSlice, ← coe_evalRingHom, ← resultant_map_map, Polynomial.map_map]
  have h1 : (evalRingHom y).comp (C : F →+* F[X]) = RingHom.id F := by ext; simp
  rw [h1, Polynomial.map_id, stepPoly, S₃poly_map]
  have e : ∀ c : F, (evalRingHom y) (C c) = c := fun c => eval_C
  have eX : (evalRingHom y) (X : F[X]) = y := eval_X
  rw [e, e, e, eX]

/-- Level `3` is `S₃`. -/
theorem Sm_three (a b : F) (x : ℕ → F) : Sm a b 3 x = S₃ a b (x 0) (x 1) (x 2) := by
  simp only [Sm, Nat.sub_self, semaevSlice, S₃poly_eval]

/-- Level `4` is the existing `S₄` (`Ecdlp/Proved/SemaevFour.lean`), argument order kept. -/
theorem Sm_four (a b : F) (x : ℕ → F) : Sm a b 4 x = S₄ a b (x 0) (x 1) (x 2) (x 3) := by
  simp only [Sm, show (4 - 3 : ℕ) = 0 + 1 from rfl, semaevSlice_succ_eval]
  rfl

/-- Determinant degree bound by column weights: if every entry of column `j` has degree at
most `w j`, the determinant has degree at most `∑ j, w j`. This is the column-weight,
commutative-ring version of `Ecdlp.FrozenProjectiveSemaev.natDegree_det_le_sum_row`
(`FrozenRecursiveProjectiveSemaev.lean`, row weights over a field), proved here by transposing
and repeating the same `Matrix.det_apply` argument. -/
theorem natDegree_det_le_sum_col {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F[X]) (w : ι → ℕ) (hA : ∀ i j, (A i j).natDegree ≤ w j) :
    A.det.natDegree ≤ ∑ j, w j := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  calc (Equiv.Perm.sign σ • ∏ i, (Matrix.transpose A) (σ i) i).natDegree
        ≤ (∏ i, (Matrix.transpose A) (σ i) i).natDegree := natDegree_smul_le _ _
    _ ≤ ∑ i, w (σ i) := (natDegree_prod_le _ _).trans
        (Finset.sum_le_sum fun i _ => hA i (σ i))
    _ = ∑ j, w j := Equiv.sum_comp σ w

/-- Every coefficient (in `T`) of `stepPoly` has degree at most `2` in `Y`. -/
theorem stepPoly_coeff_natDegree_le (a b x : F) (i : ℕ) :
    ((stepPoly a b x).coeff i).natDegree ≤ 2 := by
  simp only [stepPoly, S₃poly, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  split_ifs <;> simp <;> compute_degree

/-- **Degree upper bound:** `deg_Y S_{s+3}(x 0, …, x (s+1), Y) ≤ 2^(s+1)`, over any
commutative ring. The general-`(a,b)` affine analogue of the secp256k1 frozen-family bound
`Ecdlp.FrozenProjectiveSemaev.previousSliceAtOver_frozenC_natDegree_le` (same `2^(s+1)`). -/
theorem semaevSlice_natDegree_le (a b : F) (x : ℕ → F) (s : ℕ) :
    (semaevSlice a b x s).natDegree ≤ 2 ^ (s + 1) := by
  cases s with
  | zero => exact S₃poly_natDegree_le _ _ _ _
  | succ s =>
    rw [semaevSlice, resultant]
    refine (natDegree_det_le_sum_col _
      (fun j : Fin (2 ^ (s + 1) + 2) => if (j : ℕ) < 2 ^ (s + 1) then 2 else 0) ?_).trans ?_
    · intro i j
      refine Fin.addCases (fun j₁ => ?_) (fun j₁ => ?_) j
      · simp only [sylvester, Matrix.of_apply, Fin.addCases_left, Fin.val_castAdd, j₁.isLt,
          if_true]
        split_ifs
        · exact stepPoly_coeff_natDegree_le _ _ _ _
        · simp
      · simp only [sylvester, Matrix.of_apply, Fin.addCases_right, Fin.val_natAdd]
        split_ifs <;> simp [coeff_map]
    · rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < 2 ^ (s + 1) then 2 else 0),
        Finset.sum_range_add]
      have h1 : ∑ i ∈ Finset.range (2 ^ (s + 1)), (if i < 2 ^ (s + 1) then 2 else 0)
          = ∑ _i ∈ Finset.range (2 ^ (s + 1)), 2 :=
        Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_range.mp hi)
      have h2 : ∑ i ∈ Finset.range 2, (if 2 ^ (s + 1) + i < 2 ^ (s + 1) then 2 else 0) = 0 :=
        Finset.sum_eq_zero fun i _ => if_neg (by omega)
      rw [h1, h2, Finset.sum_const, Finset.card_range, smul_eq_mul, pow_succ 2 (s + 1)]
      omega

/-- **Forward direction at every level**, over any commutative ring: if
`S₃(x 0, x 1, z 0) = 0` and `S₃(z i, x (i+2), z (i+1)) = 0` for every `i < s`, the slice at
level `s` vanishes at `z s`. (Geometrically `z i` plays the role of `x(P₀ + ⋯ + P_{i+1})`.)
Each step is `resultant_eq_zero_of_common_root` with common root `z s`. -/
theorem semaevSlice_eval_eq_zero_of_chain (a b : F) (x z : ℕ → F) (s : ℕ)
    (h0 : S₃ a b (x 0) (x 1) (z 0) = 0)
    (hstep : ∀ i < s, S₃ a b (z i) (x (i + 2)) (z (i + 1)) = 0) :
    (semaevSlice a b x s).eval (z s) = 0 := by
  induction s with
  | zero => simpa [semaevSlice] using h0
  | succ s ih =>
    rw [semaevSlice_succ_eval]
    refine resultant_eq_zero_of_common_root _ _ (z s) (semaevSlice_natDegree_le a b x s)
      (S₃poly_natDegree_le _ _ _ _) (Or.inr (by norm_num))
      (ih fun i hi => hstep i (by omega)) ?_
    have h := hstep s (by omega)
    rw [S₃poly_eval]
    simp only [S₃] at h ⊢
    linear_combination h

/-- **Forward direction for `Sₘ`:** a chain of `S₃` witnesses ending at the last coordinate
`x (m−1)` forces `Sₘ(x 0, …, x (m−1)) = 0`. Stated without `m ≥ 3`; for `m < 3` it is a
statement about the truncated level-0 value and says nothing about Semaev polynomials. -/
theorem Sm_eq_zero_of_chain (a b : F) (m : ℕ) (x z : ℕ → F)
    (h0 : S₃ a b (x 0) (x 1) (z 0) = 0)
    (hstep : ∀ i, i + 3 < m → S₃ a b (z i) (x (i + 2)) (z (i + 1)) = 0)
    (hlast : z (m - 3) = x (m - 1)) :
    Sm a b m x = 0 := by
  rw [Sm, ← hlast]
  exact semaevSlice_eval_eq_zero_of_chain a b x z (m - 3) h0
    fun i hi => hstep i (by omega)

end Ecdlp.Semaev
