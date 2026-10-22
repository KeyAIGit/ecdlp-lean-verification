import Mathlib
import Ecdlp.Proved.AffinePointFinite

/-!
# Exact point count `#E(𝔽) = n` from a point of order `n` with `2·#𝔽 + 1 < 3n`

A curve-generic form of the argument behind `secp256k1_card_point_eq_n`
(`CurveCardinalityExact.lean`). It avoids the Hasse bound and Schoof's algorithm.

Let `W` be a Weierstrass curve with `[W.IsElliptic]` (Δ ≠ 0) over a finite field `F`, with
`a₁ = a₃ = 0` and `2 ≠ 0` in `F`. Suppose the cubic `x³ + a₂x² + a₄x + a₆` has no root in `F`,
and some point `G` has `addOrderOf G = n` with `2·#F + 1 < 3n`. Then `#W(F) = n`.

The instance `[W.IsElliptic]` is a hypothesis of `natCard_point_eq_of_addOrderOf` and
`card_eq_of_prime_order_point` (part of their frozen statements). The ingredients
`natCard_point_le`, `exists_cubic_root_of_two_nsmul_eq_zero` and
`natCard_eq_of_dvd_of_lt_three_mul` do not take it.

## Route

1. **`n ∣ #E`**: Lagrange (`addOrderOf_dvd_natCard`).
2. **`#E ≤ 2·#F + 1`** (`natCard_point_le`): for every `x` the affine points `(x, y)` have
   `y` among the at most two roots of the monic quadratic
   `Y² + (a₁x + a₃)Y − (x³ + a₂x² + a₄x + a₆)`. Summing over `x` and adding the point at
   infinity gives the bound. This holds for every Weierstrass curve over a finite field.
3. **No nonzero 2-torsion** (`exists_cubic_root_of_two_nsmul_eq_zero`): when `a₁ = a₃ = 0`
   and `2 ≠ 0`, a point `P ≠ 0` with `2 • P = 0` has `y = 0`, so its `x` is a root of the
   cubic. The no-root hypothesis excludes this.
4. **Group theory** (`natCard_eq_of_dvd_of_lt_three_mul`): if `n ∣ #A ≤ N < 3n` and `A` has
   no element of order 2, then `#A = n`. A multiple `kn` below `3n` has `k ∈ {1, 2}`, and
   `k = 2` would give an element of order 2 by additive Cauchy.

Neither `n` nor `#F` needs to be prime. The no-root hypothesis is discharged for concrete
curves by the kernel-checked certificate in `CubicNoRootCertificate.lean`.

## Scope

The bound `#E ≤ 2·#F + 1` leaves room for about `2h` multiples of `n` when `n ≈ #F / h`.
So this argument reaches cofactor-1 curves only; a curve with cofactor `h ≥ 2` needs the
Hasse bound, which Mathlib v4.31 does not provide.

## Provenance

The same argument (prime point order, `#E ≤ 2p + 1`, no rational 2-torsion) is formalized for
the specification curves of pyca/verified-garbage (`VG.Proof.Weierstrass.primeOrder_of`,
Apache-2.0 OR BSD-3-Clause; see `THIRD_PARTY_NOTICES.md`). verified-garbage proves `#E = n`
for P-256/P-384/P-521 for its own specification curve type; this repository's result is for
`Ecdlp.P256.P256` over Mathlib's `WeierstrassCurve`. The code here is written against
Mathlib's `WeierstrassCurve.Affine.Point` and reuses this repository's
`instFinitePoint`; it generalizes the secp256k1-specific steps of
`CurveCardinalityExact.lean`.
-/

namespace Ecdlp.Weierstrass

open Polynomial WeierstrassCurve.Affine

/-- **Group-theoretic core.** In a finite additive group `A` with no element of order 2, if
`n ∣ #A` and `#A ≤ N < 3n`, then `#A = n`. No primality of `n` is needed. -/
theorem natCard_eq_of_dvd_of_lt_three_mul {A : Type*} [AddGroup A] [Finite A]
    {n N : ℕ} (hdvd : n ∣ Nat.card A) (hle : Nat.card A ≤ N) (hlt : N < 3 * n)
    (h2 : ∀ Q : A, (2 : ℕ) • Q = 0 → Q = 0) : Nat.card A = n := by
  haveI : Nonempty A := ⟨0⟩
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hk3 : k < 3 := by
    by_contra h
    push Not at h
    have : n * 3 ≤ n * k := Nat.mul_le_mul_left n h
    omega
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with h | h | h
  · subst h; omega
  · rw [hk, h, mul_one]
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨Q, hQ⟩ := exists_prime_addOrderOf_dvd_card' (G := A) 2 ⟨n, by rw [hk, h, mul_comm]⟩
    have hQ0 : Q ≠ 0 := by
      rintro rfl
      rw [addOrderOf_zero] at hQ
      omega
    exact hQ0 (h2 Q (addOrderOf_dvd_iff_nsmul_eq_zero.mp hQ.dvd))

/-- **`#E(F) ≤ 2·#F + 1`** for every Weierstrass curve over a finite field. Each `x ∈ F`
carries at most two affine points, because their `y`-coordinates are roots of the monic
quadratic `Y² + (a₁x + a₃)Y − (x³ + a₂x² + a₄x + a₆)`. The `+ 1` is the point at infinity. -/
theorem natCard_point_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) :
    Nat.card W.Point ≤ 2 * Fintype.card F + 1 := by
  classical
  let f : W.Point → Option (F × F) := fun P => match P with
    | .zero => none
    | .some x y _ => some (x, y)
  have hf : Function.Injective f := by
    intro P Q h
    match P, Q, h with
    | .zero, .zero, _ => rfl
    | .some x y _, .some x' y' _, h =>
      simp only [f, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  -- The set `S` of solutions `(x, y)` of the curve equation has at most 2 elements per `x`.
  let S : Finset (F × F) := Finset.univ.filter (fun xy => W.Equation xy.1 xy.2)
  have hS : S.card ≤ 2 * Fintype.card F := by
    have hfib : ∀ a ∈ S.image Prod.fst, (S.filter (fun xy => xy.1 = a)).card ≤ 2 := by
      intro a _
      let q : F[X] :=
        X ^ 2 + C (W.a₁ * a + W.a₃) * X - C (a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆)
      have hq : q.Monic := by
        simp only [q]
        monicity!
      have hqdeg : q.natDegree ≤ 2 := by
        simp only [q]
        compute_degree
      calc (S.filter (fun xy => xy.1 = a)).card
          ≤ q.roots.toFinset.card := by
            apply Finset.card_le_card_of_injOn Prod.snd
            · intro xy hxy
              simp only [Finset.mem_coe, Finset.mem_filter, S, Finset.mem_univ,
                true_and] at hxy
              obtain ⟨heq, rfl⟩ := hxy
              rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hq.ne_zero, IsRoot.def]
              rw [WeierstrassCurve.Affine.equation_iff] at heq
              simp only [q, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
              linear_combination heq
            · intro u hu v hv huv
              simp only [Finset.mem_coe, Finset.mem_filter] at hu hv
              exact Prod.ext (hu.2.trans hv.2.symm) huv
        _ ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
        _ ≤ 2 := (card_roots' q).trans hqdeg
    calc S.card ≤ 2 * (S.image Prod.fst).card := Finset.card_le_mul_card_image _ _ hfib
      _ ≤ 2 * Fintype.card F := Nat.mul_le_mul_left _ (Finset.card_le_univ _)
  -- `f` lands in `{none} ∪ some '' S`.
  have hrange : Set.range f ⊆ (insert none (Option.some '' (S : Set (F × F)))) := by
    rintro _ ⟨P, rfl⟩
    match P with
    | .zero => exact Set.mem_insert _ _
    | .some x y h =>
      refine Set.mem_insert_of_mem _ ⟨(x, y), ?_, rfl⟩
      simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact h.1
  calc Nat.card W.Point = (Set.range f).ncard := (Set.ncard_range_of_injective hf).symm
    _ ≤ (insert none (Option.some '' (S : Set (F × F)))).ncard :=
        Set.ncard_le_ncard hrange (Set.toFinite _)
    _ ≤ (Option.some '' (S : Set (F × F))).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ (S : Set (F × F)).ncard + 1 := by
        gcongr
        exact Set.ncard_image_le (Finset.finite_toSet S)
    _ = S.card + 1 := by rw [Set.ncard_coe_finset]
    _ ≤ 2 * Fintype.card F + 1 := by omega

/-- **A nonzero 2-torsion point gives a root of the cubic.** On a Weierstrass curve with
`a₁ = a₃ = 0` over a field with `2 ≠ 0`, a point `P ≠ 0` with `2 • P = 0` is affine with
`y = 0`, so its `x`-coordinate solves `x³ + a₂x² + a₄x + a₆ = 0`. -/
theorem exists_cubic_root_of_two_nsmul_eq_zero {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (h2 : (2 : F) ≠ 0)
    {P : W.toAffine.Point} (hP : (2 : ℕ) • P = 0) (hP0 : P ≠ 0) :
    ∃ x : F, x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ = 0 := by
  match P, hP, hP0 with
  | .zero, _, h => exact absurd rfl h
  | .some x y h, hP, _ =>
    refine ⟨x, ?_⟩
    rw [two_nsmul, add_eq_zero_iff_eq_neg, Point.neg_some] at hP
    obtain ⟨-, hy⟩ := Point.some.inj hP
    have hneg : W.toAffine.negY x y = -y := by
      simp [WeierstrassCurve.Affine.negY, h₁, h₃]
    rw [hneg] at hy
    have hy0 : y = 0 := by
      have : (2 : F) * y = 0 := by linear_combination hy
      exact (mul_eq_zero.mp this).resolve_left h2
    have he := h.1
    rw [WeierstrassCurve.Affine.equation_iff, h₁, h₃, hy0] at he
    linear_combination -he

/-- **Exact point count from a point of order `n`.** Let `W` have `[W.IsElliptic]` (Δ ≠ 0) and
`a₁ = a₃ = 0` over a finite field with `2 ≠ 0`, and suppose `x³ + a₂x² + a₄x + a₆` has no root.
If some point has additive order `n` and `2·#F + 1 < 3n`, then `#W(F) = n`. -/
theorem natCard_point_eq_of_addOrderOf {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (h2 : (2 : F) ≠ 0)
    (hcubic : ∀ x : F, x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ ≠ 0)
    {G : W.toAffine.Point} {n : ℕ} (hG : addOrderOf G = n)
    (hlt : 2 * Fintype.card F + 1 < 3 * n) :
    Nat.card W.toAffine.Point = n :=
  natCard_eq_of_dvd_of_lt_three_mul (hG ▸ addOrderOf_dvd_natCard G)
    (natCard_point_le W.toAffine) hlt
    (fun Q hQ => by
      by_contra hQ0
      obtain ⟨x, hx⟩ := exists_cubic_root_of_two_nsmul_eq_zero W h₁ h₃ h2 hQ hQ0
      exact hcubic x hx)

/-- **Prime-order form.** The same count, also under `[W.IsElliptic]` (Δ ≠ 0), when the input
is a prime `n` (`[Fact n.Prime]`) with `n • G = 0` and `G ≠ 0` (so `addOrderOf G = n`). -/
theorem card_eq_of_prime_order_point {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (h2 : (2 : F) ≠ 0)
    (hcubic : ∀ x : F, x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ ≠ 0)
    {n : ℕ} [Fact n.Prime] (G : W.toAffine.Point) (hGn : n • G = 0) (hG0 : G ≠ 0)
    (hlt : 2 * Fintype.card F + 1 < 3 * n) :
    Nat.card W.toAffine.Point = n :=
  natCard_point_eq_of_addOrderOf W h₁ h₃ h2 hcubic (addOrderOf_eq_prime hGn hG0) hlt

end Ecdlp.Weierstrass
