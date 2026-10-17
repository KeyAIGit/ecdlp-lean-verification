import Mathlib
import Ecdlp.Proved.SemaevFour

/-!
# OPEN TARGET — the general Semaev tower `Sₘ`: definition, `S₄` agreement, degree bound,
# forward direction at every level

Frozen statements for the recursive Semaev family over an arbitrary commutative ring, for the
short Weierstrass parameters `(a, b)`:

* `semaevSlice a b x s` is `S_{s+3}(x 0, …, x (s+1), Y)` as a polynomial in its last
  variable `Y`. Level `0` is `S₃poly a b (x 0) (x 1)`; level `s+1` is the resultant, in an
  auxiliary variable `T`, of the previous slice (in `T`) and `S₃(x (s+2), Y, T)`, with the
  fixed Sylvester sizes `(2^(s+1), 2)`.
* `Sm a b m x = S_m(x 0, …, x (m−1))`, meaningful for `m ≥ 3`.

Statements: one-step evaluation formula, agreement with `S₃` (`m = 3`) and with the existing
`S₄` (`m = 4`), the degree upper bound `deg_Y ≤ 2^(s+1) = 2^(m−2)`, and the forward direction
at every level (a chain of `S₃` witnesses forces the slice, and `Sₘ`, to vanish).

Not claimed here: the exact degree for `m ≥ 5`, the reverse direction, symmetry for `m ≥ 5`,
and any point-level statement. This stem is **not imported and not built**; every `sorry`
below is an open obligation.
-/

namespace Ecdlp.Semaev

open Polynomial

variable {F : Type*} [CommRing F]

/-- The right operand of one tower step: `S₃(x, Y, T)` as a polynomial in the outer variable
`T` with coefficients in `F[Y]` (the inner variable `Y` is the new last argument). -/
noncomputable def stepPoly (a b x : F) : F[X][X] :=
  S₃poly (C a) (C b) (C x) X

/-- `semaevSlice a b x s = S_{s+3}(x 0, …, x (s+1), Y)` as a polynomial in `Y`. -/
noncomputable def semaevSlice (a b : F) (x : ℕ → F) : ℕ → F[X]
  | 0 => S₃poly a b (x 0) (x 1)
  | s + 1 => ((semaevSlice a b x s).map C).resultant (stepPoly a b (x (s + 2))) (2 ^ (s + 1)) 2

/-- `Sₘ(x 0, …, x (m−1))`, meaningful for `m ≥ 3`. -/
noncomputable def Sm (a b : F) (m : ℕ) (x : ℕ → F) : F :=
  (semaevSlice a b x (m - 3)).eval (x (m - 1))

/-- One tower step after evaluating the new last variable at `y`. -/
theorem semaevSlice_succ_eval (a b : F) (x : ℕ → F) (s : ℕ) (y : F) :
    (semaevSlice a b x (s + 1)).eval y
      = (semaevSlice a b x s).resultant (S₃poly a b (x (s + 2)) y) (2 ^ (s + 1)) 2 := by
  sorry

/-- Level `3` is `S₃`. -/
theorem Sm_three (a b : F) (x : ℕ → F) : Sm a b 3 x = S₃ a b (x 0) (x 1) (x 2) := by
  sorry

/-- Level `4` is the existing `S₄` (`Ecdlp/Proved/SemaevFour.lean`), argument order kept. -/
theorem Sm_four (a b : F) (x : ℕ → F) : Sm a b 4 x = S₄ a b (x 0) (x 1) (x 2) (x 3) := by
  sorry

/-- **Degree upper bound:** `deg_Y S_{s+3}(x 0, …, x (s+1), Y) ≤ 2^(s+1)`, over any
commutative ring. -/
theorem semaevSlice_natDegree_le (a b : F) (x : ℕ → F) (s : ℕ) :
    (semaevSlice a b x s).natDegree ≤ 2 ^ (s + 1) := by
  sorry

/-- **Forward direction at every level**, over any commutative ring: if
`S₃(x 0, x 1, z 0) = 0` and `S₃(z i, x (i+2), z (i+1)) = 0` for every `i < s`, the slice at
level `s` vanishes at `z s`. (Geometrically `z i` plays the role of `x(P₀ + ⋯ + P_{i+1})`.) -/
theorem semaevSlice_eval_eq_zero_of_chain (a b : F) (x z : ℕ → F) (s : ℕ)
    (h0 : S₃ a b (x 0) (x 1) (z 0) = 0)
    (hstep : ∀ i < s, S₃ a b (z i) (x (i + 2)) (z (i + 1)) = 0) :
    (semaevSlice a b x s).eval (z s) = 0 := by
  sorry

/-- **Forward direction for `Sₘ`:** a chain of `S₃` witnesses ending at the last coordinate
`x (m−1)` forces `Sₘ(x 0, …, x (m−1)) = 0`. -/
theorem Sm_eq_zero_of_chain (a b : F) (m : ℕ) (x z : ℕ → F)
    (h0 : S₃ a b (x 0) (x 1) (z 0) = 0)
    (hstep : ∀ i, i + 3 < m → S₃ a b (z i) (x (i + 2)) (z (i + 1)) = 0)
    (hlast : z (m - 3) = x (m - 1)) :
    Sm a b m x = 0 := by
  sorry

end Ecdlp.Semaev
