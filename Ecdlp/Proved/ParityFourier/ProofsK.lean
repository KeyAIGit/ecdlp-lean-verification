import Ecdlp.Proved.ParityFourier.StatementsK
import Ecdlp.Proved.ParityFourier.ProofsF1

/-!
# Proofs of K (row K of the parity coverage map, both directions)

Proves the frozen statements `Ecdlp.ParityFourier.ParityMismatchZero`,
`Ecdlp.ParityFourier.EvenFeatureZero`, `Ecdlp.ParityFourier.OddFeatureZero` and
`Ecdlp.ParityFourier.XOnlyZero` from `Ecdlp.Proved.ParityFourier.StatementsK`.

Outline:
1. K0: reindexing `k ↦ -k` maps the sum `S` over `k ≠ 0` to `-S`, so `2 S = 0`;
2. `(-k).val • G = -(k.val • G)` when `addOrderOf G = n`, and `k.val • G ≠ -(k.val • G)`
   for `k ≠ 0` when `n` is an odd prime; so an even (odd) feature `Φ` of the point gives
   an even (odd on `k ≠ 0`) function `k ↦ Φ (k.val • G)` on `ZMod n`;
3. the targets: `sgn` and `g` are odd on `k ≠ 0` (`ProofsF1.sgn_neg`, `ProofsF1.gOdd`),
   `J` is even (`ProofsF1.jEven`), and `(-k / n) = χ₄(n) (k / n)` with `χ₄(n) = -1` for
   `n ≡ 3 (mod 4)` and `χ₄(n) = 1` for `n ≡ 1 (mod 4)`;
4. K-x: `xFeature` is even, because negation of a point keeps its x-coordinate.

Provenance: the K0 argument, the `sgn` and `J` instances, `nsmul_val_neg` and `xFeature_neg`
follow the scratch files `map/KummerZero.lean` and `paperlean/KummerFR.lean` (session
3eaafce7, disclosed in `StatementsK.lean`). `nsmul_val_ne_neg` (needed for odd features of
group elements), the `g` and Legendre conjuncts, and the derivation of K-x from K-even are
new here.
-/

namespace Ecdlp.ParityFourier.ProofsK

open Ecdlp.ParityFourier Finset

section Abstract

variable {n : ℕ} [NeZero n]

/-- Even against odd: the sum over `k ≠ 0` vanishes (no parity condition on `n` is needed). -/
theorem sum_even_mul_odd (F T : ZMod n → ℂ) (hF : ∀ k, F (-k) = F k)
    (hT : ∀ k, k ≠ 0 → T (-k) = -T k) :
    ∑ k ∈ univ.erase (0 : ZMod n), F k * T k = 0 := by
  set E := univ.erase (0 : ZMod n)
  have hre : ∑ k ∈ E, F k * T k = ∑ k ∈ E, F (-k) * T (-k) := by
    refine Finset.sum_nbij' (fun k => -k) (fun k => -k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [E, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, neg_eq_zero] at hk ⊢
      exact hk
    · intro k hk
      simp only [E, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, neg_eq_zero] at hk ⊢
      exact hk
    · intro k _
      simp
    · intro k _
      simp
    · intro k _
      simp
  have hneg : ∑ k ∈ E, F (-k) * T (-k) = -∑ k ∈ E, F k * T k := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    rw [hF k, hT k hk0]
    ring
  have h2 : (2 : ℂ) * ∑ k ∈ E, F k * T k = 0 := by
    have := hre.trans hneg
    linear_combination this
  simpa using h2

/-- Odd against even: the sum over `k ≠ 0` vanishes. -/
theorem sum_odd_mul_even (F T : ZMod n → ℂ) (hF : ∀ k, k ≠ 0 → F (-k) = -F k)
    (hT : ∀ k, T (-k) = T k) :
    ∑ k ∈ univ.erase (0 : ZMod n), F k * T k = 0 := by
  have h := sum_even_mul_odd T F hT hF
  simpa [mul_comm] using h

end Abstract

/-- K0. -/
theorem parityMismatchZero : Ecdlp.ParityFourier.ParityMismatchZero := by
  intro n _ _ F T hF hT
  exact sum_even_mul_odd F T hF hT

section Group

variable {A : Type} [AddCommGroup A] {G : A} {n : ℕ}

/-- Negation of the index is negation of the point. -/
lemma nsmul_val_neg [NeZero n] (hG : addOrderOf G = n) (k : ZMod n) :
    (-k).val • G = -(k.val • G) := by
  by_cases hk : k = 0
  · subst hk
    simp
  · haveI : NeZero k := ⟨hk⟩
    rw [ZMod.val_neg_of_ne_zero]
    have hlt : k.val < n := ZMod.val_lt k
    have hn : n • G = 0 := by
      rw [← hG]
      exact addOrderOf_nsmul_eq_zero G
    rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel hlt.le, hn]

/-- For `G` of odd prime order and `k ≠ 0`, the point `[k]G` is not 2-torsion. -/
lemma nsmul_val_ne_neg [Fact n.Prime] (hn2 : n ≠ 2) (hG : addOrderOf G = n) {k : ZMod n}
    (hk : k ≠ 0) : k.val • G ≠ -(k.val • G) := by
  haveI : NeZero n := ⟨(Fact.out : n.Prime).ne_zero⟩
  intro h
  have h2 : (2 * k.val) • G = 0 := by
    rw [mul_comm, mul_nsmul, two_nsmul]
    nth_rewrite 2 [h]
    exact add_neg_cancel _
  have hdvd : n ∣ 2 * k.val := by
    have h3 : addOrderOf G ∣ 2 * k.val := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2
    rwa [hG] at h3
  rcases (Nat.Prime.dvd_mul (Fact.out : n.Prime)).mp hdvd with h | h
  · have hle := Nat.le_of_dvd (by norm_num) h
    have h2le := (Fact.out : n.Prime).two_le
    omega
  · have hpos : 0 < k.val := (ZMod.val_pos).mpr hk
    have hle := Nat.le_of_dvd hpos h
    have hlt := ZMod.val_lt k
    omega

/-- An even feature of `[k]G` is an even function of `k`. -/
lemma even_comp [NeZero n] (hG : addOrderOf G = n) (Φ : A → ℂ) (hΦ : ∀ P, Φ (-P) = Φ P)
    (k : ZMod n) : Φ ((-k).val • G) = Φ (k.val • G) := by
  rw [nsmul_val_neg hG, hΦ]

/-- An odd feature of `[k]G` is an odd function of `k` on `k ≠ 0`. -/
lemma odd_comp [Fact n.Prime] (hn2 : n ≠ 2) (hG : addOrderOf G = n) (Ψ : A → ℂ)
    (hΨ : ∀ P, P ≠ -P → Ψ (-P) = -Ψ P) (k : ZMod n) (hk : k ≠ 0) :
    Ψ ((-k).val • G) = -Ψ (k.val • G) := by
  haveI : NeZero n := ⟨(Fact.out : n.Prime).ne_zero⟩
  rw [nsmul_val_neg hG, hΨ _ (nsmul_val_ne_neg hn2 hG hk)]

end Group

section Targets

variable {n : ℕ} [Fact n.Prime]

/-- The parity sign, as a complex function, is odd on `k ≠ 0`. -/
lemma sgnC_neg (hn2 : n ≠ 2) (k : ZMod n) (hk : k ≠ 0) :
    ((sgn (-k) : ℤ) : ℂ) = -((sgn k : ℤ) : ℂ) := by
  haveI : NeZero n := ⟨(Fact.out : n.Prime).ne_zero⟩
  rw [ProofsF1.sgn_neg (ProofsF1.odd_of_prime hn2) hk]
  push_cast
  ring

/-- The carry sign, as a complex function, is odd on `k ≠ 0`. -/
lemma gC_neg (hn2 : n ≠ 2) {lam : ZMod n} (hlam : lam ^ 2 + lam + 1 = 0) (k : ZMod n)
    (hk : k ≠ 0) : ((g lam (-k) : ℤ) : ℂ) = -((g lam k : ℤ) : ℂ) := by
  rw [ProofsF1.gOdd n hn2 lam hlam k hk]
  push_cast
  ring

/-- The ordered-sector sign, as a complex function, is even. -/
lemma JC_neg' (hn2 : n ≠ 2) {lam : ZMod n} (hlam : lam ^ 2 + lam + 1 = 0) (k : ZMod n) :
    ((J lam (-k) : ℤ) : ℂ) = ((J lam k : ℤ) : ℂ) := by
  rw [ProofsF1.jEven n hn2 lam hlam k]

/-- `((-k) / n) = χ₄(n) (k / n)` for the canonical representatives. -/
lemma legendre_val_neg (hn2 : n ≠ 2) (k : ZMod n) :
    legendreSym n ((-k).val : ℤ) = ZMod.χ₄ n * legendreSym n (k.val : ℤ) := by
  rw [← legendreSym.at_neg hn2]
  unfold legendreSym
  congr 1
  push_cast
  simp

/-- For `n ≡ 3 (mod 4)`, the Legendre symbol is odd. -/
lemma legendreC_neg_of_three (hn2 : n ≠ 2) (h3 : n % 4 = 3) (k : ZMod n) :
    ((legendreSym n ((-k).val : ℤ) : ℤ) : ℂ) = -((legendreSym n (k.val : ℤ) : ℤ) : ℂ) := by
  rw [legendre_val_neg hn2, ZMod.χ₄_nat_three_mod_four h3]
  push_cast
  ring

/-- For `n ≡ 1 (mod 4)`, the Legendre symbol is even. -/
lemma legendreC_neg_of_one (hn2 : n ≠ 2) (h1 : n % 4 = 1) (k : ZMod n) :
    ((legendreSym n ((-k).val : ℤ) : ℤ) : ℂ) = ((legendreSym n (k.val : ℤ) : ℤ) : ℂ) := by
  rw [legendre_val_neg hn2, ZMod.χ₄_nat_one_mod_four h1]
  push_cast
  ring

end Targets

/-- K-even. -/
theorem evenFeatureZero : Ecdlp.ParityFourier.EvenFeatureZero := by
  intro A _ G n _ hn2 hG Φ hΦ
  haveI : NeZero n := ⟨(Fact.out : n.Prime).ne_zero⟩
  have hF : ∀ k : ZMod n, Φ ((-k).val • G) = Φ (k.val • G) := even_comp hG Φ hΦ
  refine ⟨?_, ?_, ?_⟩
  · exact sum_even_mul_odd (fun k : ZMod n => Φ (k.val • G)) (fun k => ((sgn k : ℤ) : ℂ))
      hF (sgnC_neg hn2)
  · intro lam hlam
    exact sum_even_mul_odd (fun k : ZMod n => Φ (k.val • G)) (fun k => ((g lam k : ℤ) : ℂ))
      hF (gC_neg hn2 hlam)
  · intro h3
    exact sum_even_mul_odd (fun k : ZMod n => Φ (k.val • G))
      (fun k => ((legendreSym n (k.val : ℤ) : ℤ) : ℂ)) hF
      (fun k _ => legendreC_neg_of_three hn2 h3 k)

/-- K-odd. -/
theorem oddFeatureZero : Ecdlp.ParityFourier.OddFeatureZero := by
  intro A _ G n _ hn2 hG Ψ hΨ
  haveI : NeZero n := ⟨(Fact.out : n.Prime).ne_zero⟩
  have hF : ∀ k : ZMod n, k ≠ 0 → Ψ ((-k).val • G) = -Ψ (k.val • G) :=
    odd_comp hn2 hG Ψ hΨ
  refine ⟨?_, ?_⟩
  · intro lam hlam
    exact sum_odd_mul_even (fun k : ZMod n => Ψ (k.val • G)) (fun k => ((J lam k : ℤ) : ℂ))
      hF (JC_neg' hn2 hlam)
  · intro h1
    exact sum_odd_mul_even (fun k : ZMod n => Ψ (k.val • G))
      (fun k => ((legendreSym n (k.val : ℤ) : ℤ) : ℂ)) hF (legendreC_neg_of_one hn2 h1)

/-- `xFeature` is even: negation keeps the x-coordinate. -/
lemma xFeature_neg {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K)
    (Φ : K → ℂ) (c0 : ℂ) (P : W.toAffine.Point) :
    xFeature W Φ c0 (-P) = xFeature W Φ c0 P := by
  cases P with
  | zero => rfl
  | some x y h => rfl

/-- K-x. -/
theorem xOnlyZero : Ecdlp.ParityFourier.XOnlyZero := by
  intro K _ _ W G n _ hn2 hG Φ c0
  exact evenFeatureZero W.toAffine.Point G n hn2 hG (xFeature W Φ c0) (xFeature_neg W Φ c0)

end Ecdlp.ParityFourier.ProofsK
