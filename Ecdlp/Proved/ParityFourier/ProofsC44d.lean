import Ecdlp.Proved.ParityFourier.StatementsC44d

/-!
# Proofs of C44-N (norm lemma) and C44-6d (0 is not in GammaJ)

Proves the frozen statements `Ecdlp.ParityFourier.NormLemma` and
`Ecdlp.ParityFourier.ZeroNotInGammaJ` from `Ecdlp/Proved/ParityFourier/StatementsC44d.lean`.
-/

namespace Ecdlp.ParityFourier.ProofsC44d

open Ecdlp.ParityFourier

theorem normLemma : Ecdlp.ParityFourier.NormLemma := by
  intro n _ lam hlam x y hxy h
  have hz : (((x ^ 2 - x * y + y ^ 2 : ℤ)) : ZMod n) = 0 := by
    push_cast
    linear_combination ((x : ZMod n) - lam * (y : ZMod n) - (y : ZMod n)) * h
      + (y : ZMod n) ^ 2 * hlam
  have hdvd : (n : ℤ) ∣ x ^ 2 - x * y + y ^ 2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).1 hz
  have hpos : 0 < x ^ 2 - x * y + y ^ 2 := by
    by_cases hy : y = 0
    · subst hy
      have hx : x ≠ 0 := by
        intro hx; exact hxy (by simp [hx])
      have : 0 < x ^ 2 := by positivity
      nlinarith
    · have : 0 < y ^ 2 := by positivity
      nlinarith [sq_nonneg (2 * x - y)]
  exact Int.le_of_dvd hpos hdvd

theorem zeroNotInGammaJ : Ecdlp.ParityFourier.ZeroNotInGammaJ := by
  intro n hp hn2 lam hlam B hB h0
  simp only [GammaJ, window, Finset.mem_image, Finset.mem_product, Finset.mem_Icc] at h0
  obtain ⟨⟨t1, t2⟩, ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩, he⟩ := h0
  simp only at h1a h1b h2a h2b he
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    simp at hlam
  have hfac : (hC n + (t1 : ZMod n)) + lam * (hC n + (t2 : ZMod n)) = 0 := by
    have : lam * ((hC n + (t1 : ZMod n)) + lam * (hC n + (t2 : ZMod n))) = 0 := by
      linear_combination he
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hlam0
    · exact h
  have hodd : n % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hn2
    · exact h
  have hh : (2 : ZMod n) * hC n = 1 := by
    have hnat : 2 * ((n + 1) / 2) = n + 1 := by omega
    have : ((2 * ((n + 1) / 2) : ℕ) : ZMod n) = ((n + 1 : ℕ) : ZMod n) := by rw [hnat]
    unfold hC
    push_cast at this
    rw [this, ZMod.natCast_self, zero_add]
  have hxy : (((2 * t1 + 1 : ℤ)) : ZMod n) + lam * (((2 * t2 + 1 : ℤ)) : ZMod n) = 0 := by
    push_cast
    linear_combination 2 * hfac - (1 + lam) * hh
  have hne : ((2 * t1 + 1 : ℤ), (2 * t2 + 1 : ℤ)) ≠ (0, 0) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  have hN := normLemma n lam hlam _ _ hne hxy
  have hB' : (3 * (2 * (B : ℤ) + 1) ^ 2) < (n : ℤ) := by exact_mod_cast hB
  set M : ℤ := 2 * (B : ℤ) + 1 with hM
  set x : ℤ := 2 * t1 + 1 with hx
  set y : ℤ := 2 * t2 + 1 with hy
  have hxl : -M ≤ x := by omega
  have hxu : x ≤ M := by omega
  have hyl : -M ≤ y := by omega
  have hyu : y ≤ M := by omega
  nlinarith [mul_nonneg (sub_nonneg.2 hxu) (sub_nonneg.2 hyu),
    mul_nonneg (neg_le_iff_add_nonneg.1 hxl) (neg_le_iff_add_nonneg.1 hyl),
    mul_nonneg (sub_nonneg.2 hxu) (neg_le_iff_add_nonneg.1 hxl),
    mul_nonneg (sub_nonneg.2 hyu) (neg_le_iff_add_nonneg.1 hyl)]

end Ecdlp.ParityFourier.ProofsC44d
