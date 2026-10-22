import Mathlib
import Ecdlp.Proved.CurveCardinality
import Ecdlp.Proved.TwoTorsionPoint
import Ecdlp.Proved.TorsionPointCount
import Ecdlp.Proved.Secp256k1PrimeP
import Ecdlp.Proved.KernelPowMod

/-!
# The exact secp256k1 curve cardinality: `#E(𝔽_p) = n`

The strong keystone. Upgrades `secp256k1_n_dvd_card_point` (`n ∣ #E`) to the exact
count `Nat.card secp256k1.toAffine.Point = Secp256k1.n`, WITHOUT the Hasse bound or
Schoof's algorithm — by a curve-specific five-step argument that exploits the special
structure of `E : Y² = X³ + 7` over `𝔽_p` with `p ≡ 1 (mod 3)`.

## Route (five steps)

1. **`n ∣ #E`** — reused verbatim: `secp256k1_n_dvd_card_point` (Lagrange on `⟨G⟩`).
2. **`#E ≤ 2p + 1`** — at most two `y` per `x` (the fiber `{y // y² = x³+7}` injects into
   the ≤ 2 roots of `X² - C (x³+7)`), summed over the `p` values of `x`, plus the point
   at infinity `O`. Built here as `secp256k1_card_point_le`, mirroring the in-repo
   fiber counter `secp256k1_torsion_ncard_le` but over ALL `x` (image bounded by
   `Fintype.card (ZMod p) = p`); the identity `O` is added via `univ = insert 0 {P | P ≠ 0}`
   and the unconditional `Set.ncard_insert_le`.
3. **`#E ∈ {n, 2n}`** — combine (1)+(2) with the kernel-checked literal fact
   `2p+1 < 3n` (`decide +kernel`): a positive multiple `n·k` of `n` that is `≤ 2p+1 < 3n` forces
   `k ∈ {1, 2}` (an explicit `omega` split).
4. **No nonzero 2-torsion** — if `2 • P = 0` for `P = (x, y)` then `y = 0`
   (`secp256k1_two_nsmul_eq_zero_iff`), so `x³ = -7`; but `-7` is not a cube in `𝔽_p`
   (`(-7)^((p-1)/3) ≠ 1`, a kernel-evaluated 256-bit power, and `(x³)^((p-1)/3) = x^(p-1) = 1` by
   Fermat, using `3 ∣ p-1`), a contradiction. Hence `E[2] = {O}`.
5. **Exclude `2n`** — `2n` is even, so `2 ∣ #E`; additive Cauchy
   (`exists_prime_addOrderOf_dvd_card`) then yields a point `Q` of additive order exactly
   `2`; via `Eq.dvd` and the repo-confirmed `addOrderOf_dvd_iff_nsmul_eq_zero` this gives
   a nonzero point with `2 • Q = 0` — impossible by (4). Therefore `#E = n`.

No new axioms and no compiler trust: the closed Nat-literal facts are checked by the
Lean kernel (`decide +kernel`), and the 256-bit modular exponentiation is evaluated by the
kernel on `Nat` (`Ecdlp.Kernel.powMod`, `KernelPowMod.lean`) and transferred to `ZMod p`
— the same method as the witness leaves of the primality certificates.
-/

namespace Ecdlp.Curve

open Polynomial WeierstrassCurve.Affine

/-- **`−7` is not a cube in `𝔽_p`** (the Euler cubic-residue witness `(−7)^((p−1)/3) ≠ 1`,
`p ≡ 1 mod 3`). Kernel-only: `-7` is rewritten as the cast of `p - 7`, the 256-bit power is
evaluated by the kernel on `Nat` (`Ecdlp.Kernel.powMod`, `decide +kernel`), and the result is
transferred to `ZMod p` (`Ecdlp.Kernel.zmod_pow_natCast`), exactly as the witness leaves of
the primality certificate in `Secp256k1PrimeP.lean`. -/
theorem secp256k1_neg7_pow_ne_one :
    (-7 : ZMod Secp256k1.p) ^ ((Secp256k1.p - 1) / 3) ≠ 1 := by
  have h7 : (-7 : ZMod Secp256k1.p) = ((Secp256k1.p - 7 : ℕ) : ZMod Secp256k1.p) := by
    rw [Nat.cast_sub (by decide +kernel), ZMod.natCast_self]; simp
  rw [h7, Ecdlp.Kernel.zmod_pow_natCast _ (by decide +kernel) 256 _ _ (by decide +kernel)]
  exact Ecdlp.Kernel.natCast_ne_one_of_mod _ _ (by decide +kernel)

variable [Fact (Nat.Prime Secp256k1.p)]

/-! ### Step 2: the affine point-count bound `#E ≤ 2p + 1` -/

/-- **`#E(𝔽_p) ≤ 2p + 1`.** Each `x ∈ 𝔽_p` carries at most two curve points `(x, ±y)`
(the fiber injects into the ≤ 2 roots of `X² - C (x³+7)`); summed over the `p` values of
`x` that is `≤ 2p` affine points, plus the point at infinity `O`. -/
theorem secp256k1_card_point_le :
    Nat.card secp256k1.toAffine.Point ≤ 2 * Secp256k1.p + 1 := by
  classical
  haveI : NeZero Secp256k1.p := ⟨(Fact.out : Nat.Prime Secp256k1.p).pos.ne'⟩
  -- `N` = the affine (nonzero) points.
  set N := {P : secp256k1.toAffine.Point | P ≠ 0} with hN
  haveI : Fintype ↥N := Fintype.ofFinite _
  have hNcard : N.ncard = N.toFinset.card := Set.ncard_eq_toFinset_card' N
  -- Each `x`-fiber has at most 2 points (`≤ 2` roots of `X² - C (x³+7)`).
  have hfib : ∀ a ∈ N.toFinset.image px,
      (N.toFinset.filter (fun P => px P = a)).card ≤ 2 := by
    intro a _
    have hpoly_ne : (X ^ 2 - C (a ^ 3 + 7) : (ZMod Secp256k1.p)[X]) ≠ 0 :=
      X_pow_sub_C_ne_zero (by norm_num) (a ^ 3 + 7)
    have hpoly_deg : (X ^ 2 - C (a ^ 3 + 7) : (ZMod Secp256k1.p)[X]).natDegree ≤ 2 := by
      compute_degree
    have hroots_card :
        (X ^ 2 - C (a ^ 3 + 7) : (ZMod Secp256k1.p)[X]).roots.toFinset.card ≤ 2 :=
      (Multiset.toFinset_card_le _).trans ((card_roots' _).trans hpoly_deg)
    refine le_trans ?_ hroots_card
    apply Finset.card_le_card_of_injOn py
    · intro P hP
      rw [Finset.mem_coe, Finset.mem_filter, Set.mem_toFinset] at hP
      obtain ⟨hPN, hPa⟩ := hP
      rcases P with _ | ⟨x, y, h⟩
      · exact absurd rfl hPN
      · simp only [px] at hPa
        subst hPa
        have hcurve : y ^ 2 = x ^ 3 + 7 := secp256k1_curve_of_nonsingular x y h
        simp only [py, Finset.mem_coe, Multiset.mem_toFinset, mem_roots', IsRoot.def, eval_sub,
          eval_pow, eval_X, eval_C]
        exact ⟨hpoly_ne, by linear_combination hcurve⟩
    · intro P hP Q hQ hPQ
      rw [Finset.mem_coe, Finset.mem_filter, Set.mem_toFinset] at hP hQ
      rcases P with _ | ⟨x1, y1, h1⟩
      · exact absurd rfl hP.1
      rcases Q with _ | ⟨x2, y2, h2⟩
      · exact absurd rfl hQ.1
      · simp only [px] at hP hQ
        simp only [py] at hPQ
        have hxx : x1 = x2 := hP.2.trans hQ.2.symm
        subst hxx; subst hPQ; rfl
  -- Bound `N.ncard ≤ 2 * p` via the ≤2-to-1 fiber counter and `#(ZMod p) = p`.
  have hN_le : N.ncard ≤ 2 * Secp256k1.p := by
    rw [hNcard]
    calc N.toFinset.card
        ≤ 2 * (N.toFinset.image px).card := by
          apply Finset.card_le_mul_card_image
          exact hfib
      _ ≤ 2 * (Finset.univ : Finset (ZMod Secp256k1.p)).card :=
          Nat.mul_le_mul_left 2 (Finset.card_le_card (Finset.subset_univ _))
      _ = 2 * Secp256k1.p := by rw [Finset.card_univ, ZMod.card]
  -- `univ = insert 0 N`, so `#E = univ.ncard ≤ N.ncard + 1 ≤ 2p + 1`.
  have hins : (Set.univ : Set secp256k1.toAffine.Point) = insert 0 N := by
    apply Set.Subset.antisymm
    · intro P _
      by_cases h : P = 0
      · rw [h]; exact Set.mem_insert 0 N
      · apply Set.mem_insert_of_mem
        rw [hN]; exact h
    · intro P _
      exact Set.mem_univ P
  have hcarduniv :
      Nat.card secp256k1.toAffine.Point
        = (Set.univ : Set secp256k1.toAffine.Point).ncard := (Set.ncard_univ _).symm
  rw [hcarduniv, hins]
  calc (insert 0 N).ncard
      ≤ N.ncard + 1 := Set.ncard_insert_le 0 N
    _ ≤ 2 * Secp256k1.p + 1 := Nat.add_le_add_right hN_le 1

/-! ### Step 4: secp256k1 has no nonzero 2-torsion point (`E[2] = {O}`) -/

/-- **`E[2] = {O}`.** The only 2-torsion point of secp256k1 is the identity. If
`2 • P = 0` with `P = (x, y)` then `y = 0` (`secp256k1_two_nsmul_eq_zero_iff`), so the
curve equation gives `x³ = -7`; but `-7` is not a cube in `𝔽_p`: from `x³ = -7` we would
get `(-7)^((p-1)/3) = (x³)^((p-1)/3) = x^(p-1) = 1` (Fermat, using `3 ∣ p-1`), contradicting
the machine-checked fact `(-7)^((p-1)/3) ≠ 1`. -/
theorem secp256k1_no_nonzero_two_torsion (P : secp256k1.toAffine.Point)
    (hP : (2 : ℕ) • P = 0) : P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · exfalso
    have hy : y = 0 := (secp256k1_two_nsmul_eq_zero_iff x y h).mp hP
    have hcurve : y ^ 2 = x ^ 3 + 7 := secp256k1_curve_of_nonsingular x y h
    rw [hy] at hcurve
    -- `x³ = -7`.
    have hx3 : x ^ 3 = -7 := by linear_combination -hcurve
    -- `7 ≠ 0` in `𝔽_p`, hence `x ≠ 0`.
    have h7ne : (7 : ZMod Secp256k1.p) ≠ 0 := by
      have h7 : ((7 : ℕ) : ZMod Secp256k1.p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]; decide +kernel
      simpa using h7
    have hxne : x ≠ 0 := by
      intro hx0
      rw [hx0] at hx3
      exact h7ne (by linear_combination hx3)
    -- Exponent identity `3 * ((p-1)/3) = p - 1` from `3 ∣ p-1`.
    have h3dvd : 3 ∣ Secp256k1.p - 1 := by decide +kernel
    have hexp : 3 * ((Secp256k1.p - 1) / 3) = Secp256k1.p - 1 := Nat.mul_div_cancel' h3dvd
    -- Fermat: `(-7)^((p-1)/3) = (x³)^((p-1)/3) = x^(p-1) = 1`.
    have key : ((-7 : ZMod Secp256k1.p)) ^ ((Secp256k1.p - 1) / 3) = 1 := by
      rw [← hx3, ← pow_mul, hexp]
      exact ZMod.pow_card_sub_one_eq_one hxne
    -- But `-7` is a non-cube: `(-7)^((p-1)/3) ≠ 1` (proved above, kernel-evaluated).
    exact secp256k1_neg7_pow_ne_one key

/-! ### Steps 1 + 3 + 5: assemble `#E = n` -/

/-- **The exact secp256k1 curve cardinality: `#E(𝔽_p) = n`.** No Hasse bound, no Schoof:
`n ∣ #E` (Lagrange) and `#E ≤ 2p+1 < 3n` force `#E ∈ {n, 2n}`; the value `2n` (even) is
excluded because it would produce, by additive Cauchy, a point of order exactly 2 — a
nonzero 2-torsion point, which `secp256k1_no_nonzero_two_torsion` forbids. Hence `#E = n`,
so secp256k1 has cofactor 1. -/
theorem secp256k1_card_point_eq_n :
    Nat.card secp256k1.toAffine.Point = Secp256k1.n := by
  classical
  haveI : Nonempty secp256k1.toAffine.Point := ⟨0⟩
  -- Step 1 (reused): `n ∣ #E`.
  have hdvd : Secp256k1.n ∣ Nat.card secp256k1.toAffine.Point := secp256k1_n_dvd_card_point
  -- Step 2: `#E ≤ 2p + 1`.
  have hle : Nat.card secp256k1.toAffine.Point ≤ 2 * Secp256k1.p + 1 := secp256k1_card_point_le
  have hpos : 0 < Nat.card secp256k1.toAffine.Point := Nat.card_pos
  -- Step 3: pin `#E = n·k` with `k ∈ {1, 2}`.
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hk; omega
    · exact h0
  have hbound : 2 * Secp256k1.p + 1 < 3 * Secp256k1.n := by decide +kernel
  have hklt : k < 3 := by
    by_contra hge
    push_neg at hge
    have hstep : 3 * Secp256k1.n ≤ Nat.card secp256k1.toAffine.Point := by
      rw [hk]
      calc 3 * Secp256k1.n = Secp256k1.n * 3 := Nat.mul_comm 3 Secp256k1.n
        _ ≤ Secp256k1.n * k := Nat.mul_le_mul_left Secp256k1.n hge
    omega
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with h1 | h2
  · -- `k = 1`: `#E = n · 1 = n`.
    rw [hk, h1, mul_one]
  · -- `k = 2`: `#E = 2n`; excluded via additive Cauchy (Step 5).
    exfalso
    haveI : Fintype secp256k1.toAffine.Point := Fintype.ofFinite _
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hdvd2 : 2 ∣ Fintype.card secp256k1.toAffine.Point := by
      rw [← Nat.card_eq_fintype_card, hk, h2]
      exact ⟨Secp256k1.n, by ring⟩
    obtain ⟨Q, hQ⟩ := exists_prime_addOrderOf_dvd_card 2 hdvd2
    -- `2 • Q = 0` from `addOrderOf Q = 2` and `addOrderOf Q ∣ 2` (`Eq.dvd`).
    have h2Q : (2 : ℕ) • Q = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp hQ.dvd
    have hQne : Q ≠ 0 := by
      rintro rfl
      rw [addOrderOf_zero] at hQ
      exact absurd hQ (by decide)
    exact hQne (secp256k1_no_nonzero_two_torsion Q h2Q)

end Ecdlp.Curve