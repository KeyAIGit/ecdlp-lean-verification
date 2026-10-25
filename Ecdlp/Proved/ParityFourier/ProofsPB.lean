import Ecdlp.Proved.ParityFourier.ProofsPB1
import Ecdlp.Proved.ParityFourier.ProofsPB23

/-!
# Proofs of PB-4, PB-4g and PB-5 (noisy binary division: one guess, guess grid, group)

Proves the frozen statements `Ecdlp.ParityFourier.NoisyHalvingRecovers`, `Ecdlp.ParityFourier.NoisyHalvingGrid`
and `Ecdlp.ParityFourier.GroupNoisyHalvingRecovers` from `Ecdlp.Proved.ParityFourier.StatementsPB` (frozen at commit
3230224), using PB-1 (`ProofsPB1`) and PB-2/PB-3 (`ProofsPB23`) through their helper lemmas.

Outline:
1. Correct path (`pbPath_eq_of_correct`). Write `y_t = x · 2⁻ᵗ` and
   `γ_t = y_t.val + (c0 - x.val)/2^t`, a rational that depends on `x` and `c0` only, not on
   the shift table. If every step `t < L`, run with the guess `γ_t`, decides the parity of
   `y_t`, then by induction the guess path is `γ_t` for `t ≤ L`: `halve_error` turns
   `(γ_t + (y_t.val % 2) n)/2` into `γ_{t+1}`.
2. Output (`pbDecode_eq_of_correct`). `|γ_L - y_L.val| = |c0 - x.val|/2^L < 1/2` when
   `2 |c0 - x.val| < 2^L`, so `round γ_L = y_L.val` (`round_natCast_add`,
   `round_eq_zero_iff`) and `2^L · y_L = x` in `ZMod n` (`2 ≠ 0`).
3. PB-4 (`noisyHalving_frac`). The card hypothesis forces `ε ≤ 1/2`, so
   `2 Δ ≤ 2 ε n - 2 < n ≤ 2^L` (strict rounding margin) and `δ = ε - (Δ + 1)/n ≥ 0`. For
   row `t` the good shifts are `s` with `pbVote (P (y_t + s)) γ_t s = y_t.val % 2`; since
   `|γ_t - y_t.val| ≤ Δ`, `vote_half_advantage` (PB-3) gives density `≥ 1/2 + δ`. If the
   decoder misses `x`, by step 2 some step `t` fails with the guess `γ_t`, and by
   `two_mul_card_le_of_pbBit_ne` at most half of the votes of row `t` are good.
   `majorityVote_rows_of_imp` (PB-1 per row plus a union bound over the `L` rows) bounds
   the fraction of such tables by `L · exp(-2 m δ^2)`.
4. PB-4g (`noisyHalvingGrid_frac`). `4 ≤ ε N` gives `ε > 0` and `N > 0`. The cell
   `j = ⌊x.val N / n⌋ < N` has centre `pbGuess n N j` within `n/(2N) ≤ ε n/8` of `x.val`
   (`grid_guess_close`). PB-4 with `Δ = ε n/8` (its hypothesis `(Δ + 1)/n ≤ ε` is
   `1/n ≤ 7ε/8`) gives `δ = 7ε/8 - 1/n`; `x` is a candidate whenever guess `j` decodes to
   `x` from the shared answer table.
5. PB-5 (`groupNoisyHalvingRecovers`). With `addOrderOf G = n`, `k • G = (k mod n) • G`
   (`mod_addOrderOf_nsmul`) and `a ↦ a.val • G` is injective on `ZMod n` (`nsmul_inj_mod`).
   From `2h ≡ 1 (mod n)`, `(h : ZMod n) = 2⁻¹`, so `[h^t]([x]G) + [r]G = [x · 2⁻ᵗ + r]G` and
   the group answer table is the scalar table of `P z = Pred (z.val • G)`
   (`pbGroupAnswers_eq`). The check `[x']G = [x]G` forces `x' = x`, so the verified output
   is contained in `{x}` for every table; it differs from `{x}` only if `x` is not a
   candidate, which PB-4g bounds.

Provenance: no proof of PB-4, PB-4g or PB-5 existed when `StatementsPB.lean` was frozen
(disclosed in its docstring), and nothing here is ported from a scratch file. The helpers
used are `ProofsPB1.majorityVote_rows_of_imp` (whose core `majorityVote_measure` is the
disclosed pre-freeze scratch proof of the PB-1 variant), `ProofsPB23.vote_half_advantage`,
`ProofsPB23.two_mul_card_le_of_pbBit_ne`, `ProofsPB23.halve_error` and
`ProofsF3F4a.two_ne_zero_zmod`. The idea of step 5 (multiples of `G` of order `n`) follows
`ProofsF4b`; no lemma of `ProofsF4b` is used.
-/

namespace Ecdlp.ParityFourier.ProofsPB

open Finset Ecdlp.ParityFourier

/-- Correct path: if every step `t < L` decides the parity of `y_t = x · 2⁻ᵗ` when run with
the guess `γ_t = y_t.val + (c0 - x.val)/2^t`, then the guess path is `γ_t` for `t ≤ L`. -/
theorem pbPath_eq_of_correct {n L m : ℕ} [Fact n.Prime] (h2 : n ≠ 2)
    (r : Fin L → Fin m → ZMod n) (a : Fin L → Fin m → ℕ) (x : ZMod n) (c0 : ℚ)
    (hbit : ∀ (t : ℕ) (ht : t < L), pbBit (r ⟨t, ht⟩) (a ⟨t, ht⟩)
        (((x * (2 : ZMod n)⁻¹ ^ t).val : ℚ) + (c0 - (x.val : ℚ)) / 2 ^ t) =
        (x * (2 : ZMod n)⁻¹ ^ t).val % 2) :
    ∀ t : ℕ, t ≤ L →
      pbPath r a c0 t = ((x * (2 : ZMod n)⁻¹ ^ t).val : ℚ) + (c0 - (x.val : ℚ)) / 2 ^ t := by
  intro t
  induction t with
  | zero => intro _; simp [pbPath]
  | succ t ih =>
    intro ht
    have htL : t < L := ht
    rw [pbPath, dif_pos htL, ih htL.le, hbit t htL]
    have hh := ProofsPB23.halve_error n h2 (x * (2 : ZMod n)⁻¹ ^ t)
      (((x * (2 : ZMod n)⁻¹ ^ t).val : ℚ) + (c0 - (x.val : ℚ)) / 2 ^ t)
    have hy : x * (2 : ZMod n)⁻¹ ^ (t + 1) = x * (2 : ZMod n)⁻¹ ^ t * (2 : ZMod n)⁻¹ := by
      rw [pow_succ, mul_assoc]
    have e : (c0 - (x.val : ℚ)) / 2 ^ (t + 1) =
        (((x * (2 : ZMod n)⁻¹ ^ t).val : ℚ) + (c0 - (x.val : ℚ)) / 2 ^ t -
          ((x * (2 : ZMod n)⁻¹ ^ t).val : ℚ)) / 2 := by
      rw [pow_succ]
      ring
    rw [hy, e]
    linarith

/-- Correct path, output: if every step decides the parity of `y_t` with the guess `γ_t` and
`2 |c0 - x.val| < 2^L`, the decoder outputs `x`. -/
theorem pbDecode_eq_of_correct {n L m : ℕ} [Fact n.Prime] (h2 : n ≠ 2)
    (r : Fin L → Fin m → ZMod n) (a : Fin L → Fin m → ℕ) (x : ZMod n) (c0 : ℚ)
    (hround : 2 * |(c0 : ℝ) - (x.val : ℝ)| < 2 ^ L)
    (hbit : ∀ (t : ℕ) (ht : t < L), pbBit (r ⟨t, ht⟩) (a ⟨t, ht⟩)
        (((x * (2 : ZMod n)⁻¹ ^ t).val : ℚ) + (c0 - (x.val : ℚ)) / 2 ^ t) =
        (x * (2 : ZMod n)⁻¹ ^ t).val % 2) :
    pbDecode r a c0 = x := by
  unfold pbDecode
  rw [pbPath_eq_of_correct h2 r a x c0 hbit L le_rfl]
  have hroundQ : 2 * |c0 - (x.val : ℚ)| < 2 ^ L := by
    have : (((2 * |c0 - (x.val : ℚ)|) : ℚ) : ℝ) < ((2 ^ L : ℚ) : ℝ) := by
      push_cast
      exact hround
    exact_mod_cast this
  have hd : |(c0 - (x.val : ℚ)) / 2 ^ L| < 1 / 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ L), div_lt_iff₀ (by positivity)]
    linarith
  have hr : round (((x * (2 : ZMod n)⁻¹ ^ L).val : ℚ) + (c0 - (x.val : ℚ)) / 2 ^ L) =
      ((x * (2 : ZMod n)⁻¹ ^ L).val : ℤ) := by
    rw [round_natCast_add, round_eq_zero_iff.mpr ?_, add_zero]
    obtain ⟨h1, h1'⟩ := abs_lt.mp hd
    exact ⟨by linarith, h1'⟩
  rw [hr, Int.cast_natCast, ZMod.natCast_zmod_val, ← mul_assoc, mul_comm ((2 : ZMod n) ^ L) x,
    mul_assoc, ← mul_pow, mul_inv_cancel₀ (ProofsF3F4a.two_ne_zero_zmod n h2), one_pow,
    mul_one]

/-- PB-4 with its hypotheses as arguments. -/
theorem noisyHalving_frac (n : ℕ) [Fact n.Prime] (h2 : n ≠ 2) (P : ZMod n → ℕ) (ε : ℝ)
    (hP : (1 / 2 + ε) * (n : ℝ) ≤
      ((univ.filter (fun z : ZMod n => P z = z.val % 2)).card : ℝ))
    (x : ZMod n) (c0 : ℚ) (Δ : ℝ) (hc : |(c0 : ℝ) - (x.val : ℝ)| ≤ Δ)
    (hΔ : (Δ + 1) / (n : ℝ) ≤ ε) (L m : ℕ) (hL : n ≤ 2 ^ L) :
    ((univ.filter (fun r : Fin L → Fin m → ZMod n =>
        pbDecode r (pbAnswers P x r) c0 ≠ x)).card : ℝ) /
      (Fintype.card (Fin L → Fin m → ZMod n) : ℝ) ≤
      (L : ℝ) * Real.exp (-2 * (m : ℝ) * (ε - (Δ + 1) / (n : ℝ)) ^ 2) := by
  have hprime : n.Prime := Fact.out
  have hodd : Odd n := hprime.odd_of_ne_two h2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hprime.pos
  have hcardle : ((univ.filter (fun z : ZMod n => P z = z.val % 2)).card : ℝ) ≤ n := by
    have := card_filter_le (univ : Finset (ZMod n)) (fun z : ZMod n => P z = z.val % 2)
    rw [card_univ, ZMod.card] at this
    exact_mod_cast this
  have hε : ε ≤ 1 / 2 := by nlinarith
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans hc
  have hΔn : Δ + 1 ≤ ε * n := by rwa [div_le_iff₀ hnpos] at hΔ
  have hδ : 0 ≤ ε - (Δ + 1) / (n : ℝ) := sub_nonneg.mpr hΔ
  have hround : 2 * |(c0 : ℝ) - (x.val : ℝ)| < 2 ^ L := by
    have h1 : (n : ℝ) ≤ 2 ^ L := by exact_mod_cast hL
    nlinarith [mul_le_mul_of_nonneg_right hε hnpos.le]
  have hγ : ∀ t : ℕ, |((((x * (2 : ZMod n)⁻¹ ^ t).val : ℚ) +
      (c0 - (x.val : ℚ)) / 2 ^ t : ℚ) : ℝ) - ((x * (2 : ZMod n)⁻¹ ^ t).val : ℝ)| ≤ Δ := by
    intro t
    have e : ((((x * (2 : ZMod n)⁻¹ ^ t).val : ℚ) + (c0 - (x.val : ℚ)) / 2 ^ t : ℚ) : ℝ) -
        ((x * (2 : ZMod n)⁻¹ ^ t).val : ℝ) = ((c0 : ℝ) - (x.val : ℝ)) / 2 ^ t := by
      push_cast
      ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ t)]
    exact (div_le_self (abs_nonneg _) (one_le_pow₀ (by norm_num))).trans hc
  have hgood : ∀ t : Fin L, (1 / 2 + (ε - (Δ + 1) / (n : ℝ))) * (Fintype.card (ZMod n) : ℝ) ≤
      ((univ.filter (fun s : ZMod n =>
        pbVote (P (x * (2 : ZMod n)⁻¹ ^ (t : ℕ) + s))
          (((x * (2 : ZMod n)⁻¹ ^ (t : ℕ)).val : ℚ) + (c0 - (x.val : ℚ)) / 2 ^ (t : ℕ)) s =
          (x * (2 : ZMod n)⁻¹ ^ (t : ℕ)).val % 2)).card : ℝ) := fun t =>
    ProofsPB23.vote_half_advantage hodd P ε hP _ _ Δ (hγ t)
  have key := ProofsPB1.majorityVote_rows_of_imp
    (fun (t : Fin L) (s : ZMod n) =>
      pbVote (P (x * (2 : ZMod n)⁻¹ ^ (t : ℕ) + s))
        (((x * (2 : ZMod n)⁻¹ ^ (t : ℕ)).val : ℚ) + (c0 - (x.val : ℚ)) / 2 ^ (t : ℕ)) s =
        (x * (2 : ZMod n)⁻¹ ^ (t : ℕ)).val % 2)
    _ hδ hgood m (fun r => pbDecode r (pbAnswers P x r) c0 ≠ x) (by
      intro r hr
      by_contra hall
      simp only [not_exists, not_le] at hall
      apply hr
      refine pbDecode_eq_of_correct h2 r _ x c0 hround ?_
      intro t ht
      by_contra hne
      exact absurd (ProofsPB23.two_mul_card_le_of_pbBit_ne (r ⟨t, ht⟩) _ _ _
        (Nat.mod_lt _ (by norm_num)) hne) (not_le.mpr (hall ⟨t, ht⟩)))
  rwa [Fintype.card_fin] at key

/-- PB-4. `NoisyHalvingRecovers`. -/
theorem noisyHalvingRecovers : Ecdlp.ParityFourier.NoisyHalvingRecovers := by
  intro n _ h2 P ε hP x c0 Δ hc hΔ L m hL
  exact noisyHalving_frac n h2 P ε hP x c0 Δ hc hΔ L m hL

/-- Grid cell: for `N > 0`, the cell index `j = ⌊x.val N / n⌋` is below `N` and its centre
`pbGuess n N j` is within `n/(2N)` of `x.val`. -/
theorem grid_guess_close {n : ℕ} [NeZero n] (N : ℕ) (hN : 0 < N) (x : ZMod n) :
    x.val * N / n < N ∧
      |((pbGuess n N (x.val * N / n) : ℚ) : ℝ) - (x.val : ℝ)| ≤ (n : ℝ) / (2 * N) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hx := ZMod.val_lt x
  have hdiv : n * (x.val * N / n) + x.val * N % n = x.val * N := Nat.div_add_mod _ _
  have hqlt : x.val * N % n < n := Nat.mod_lt _ hn
  constructor
  · apply Nat.div_lt_of_lt_mul
    exact Nat.mul_lt_mul_of_pos_right hx hN
  · set j := x.val * N / n with hj
    set q := x.val * N % n with hq
    have hdivR : (n : ℝ) * j + q = x.val * N := by exact_mod_cast hdiv
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hqR : (q : ℝ) < n := by exact_mod_cast hqlt
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have e : ((pbGuess n N j : ℚ) : ℝ) - (x.val : ℝ) = ((n : ℝ) - 2 * q) / (2 * N) := by
      have hxv : (x.val : ℝ) = ((n : ℝ) * j + q) / N := by
        rw [hdivR]
        field_simp
      unfold pbGuess
      push_cast
      rw [hxv]
      field_simp
      ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * N)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [abs_le]
    constructor <;> linarith

/-- PB-4g with its hypotheses as arguments. -/
theorem noisyHalvingGrid_frac (n : ℕ) [Fact n.Prime] (h2 : n ≠ 2) (P : ZMod n → ℕ) (ε : ℝ)
    (hP : (1 / 2 + ε) * (n : ℝ) ≤
      ((univ.filter (fun z : ZMod n => P z = z.val % 2)).card : ℝ))
    (hn78 : 1 / (n : ℝ) ≤ 7 * ε / 8)
    (x : ZMod n) (N L m : ℕ) (hN : 4 ≤ ε * (N : ℝ)) (hL : n ≤ 2 ^ L) :
    ((univ.filter (fun r : Fin L → Fin m → ZMod n =>
        x ∉ pbCandidates N r (pbAnswers P x r))).card : ℝ) /
      (Fintype.card (Fin L → Fin m → ZMod n) : ℝ) ≤
      (L : ℝ) * Real.exp (-2 * (m : ℝ) * (7 * ε / 8 - 1 / (n : ℝ)) ^ 2) := by
  have hprime : n.Prime := Fact.out
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hprime.pos
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hεpos : 0 < ε := by
    by_contra h
    have h' := not_lt.mp h
    nlinarith
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      simp at hN
      linarith
    · exact h
  obtain ⟨hjN, hclose⟩ := grid_guess_close N hNpos x
  have hclose' : |((pbGuess n N (x.val * N / n) : ℚ) : ℝ) - (x.val : ℝ)| ≤ ε * n / 8 := by
    refine hclose.trans ?_
    have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hΔε : (ε * n / 8 + 1) / (n : ℝ) ≤ ε := by
    rw [div_le_iff₀ hnpos]
    have : 1 ≤ 7 * ε / 8 * n := by rwa [div_le_iff₀ hnpos] at hn78
    nlinarith
  have h4 := noisyHalving_frac n h2 P ε hP x (pbGuess n N (x.val * N / n)) (ε * n / 8)
    hclose' hΔε L m hL
  have heq : ε - (ε * n / 8 + 1) / (n : ℝ) = 7 * ε / 8 - 1 / n := by
    field_simp
    ring
  rw [heq] at h4
  refine le_trans ?_ h4
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsub : univ.filter (fun r : Fin L → Fin m → ZMod n =>
        x ∉ pbCandidates N r (pbAnswers P x r)) ⊆
      univ.filter (fun r : Fin L → Fin m → ZMod n =>
        pbDecode r (pbAnswers P x r) (pbGuess n N (x.val * N / n)) ≠ x) := by
    apply monotone_filter_right
    intro r _ hr hd
    apply hr
    unfold pbCandidates
    exact mem_image.mpr ⟨x.val * N / n, mem_range.mpr hjN, hd⟩
  exact_mod_cast card_le_card hsub

/-- PB-4g. `NoisyHalvingGrid`. -/
theorem noisyHalvingGrid : Ecdlp.ParityFourier.NoisyHalvingGrid := by
  intro n _ h2 P ε hP hn78 x N L m hN hL
  exact noisyHalvingGrid_frac n h2 P ε hP hn78 x N L m hN hL

/-- With `addOrderOf G = n`, `k • G` depends only on `k mod n`. -/
theorem val_natCast_nsmul {A : Type*} [AddCommGroup A] (G : A) (n : ℕ)
    (hG : addOrderOf G = n) (k : ℕ) : ((k : ZMod n)).val • G = k • G := by
  rw [ZMod.val_natCast, ← hG, mod_addOrderOf_nsmul]

/-- With `addOrderOf G = n`, `a ↦ a.val • G` is injective on `ZMod n`. -/
theorem val_nsmul_injective {A : Type*} [AddCommGroup A] (G : A) (n : ℕ) [NeZero n]
    (hG : addOrderOf G = n) {a b : ZMod n} (h : a.val • G = b.val • G) : a = b := by
  rw [nsmul_inj_mod, hG, Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)]
    at h
  exact ZMod.val_injective n h

/-- The group answers are the scalar answers of `P z = Pred (z.val • G)`:
`[h^t]([x]G) + [r]G = [x · 2⁻ᵗ + r]G`. -/
theorem pbGroupAnswers_eq {A : Type*} [AddCommGroup A] (G : A) (n : ℕ) [Fact n.Prime]
    (h2 : n ≠ 2) (hG : addOrderOf G = n) (h : ℕ) (hh : (2 * h) % n = 1) (Pred : A → ℕ)
    (x : ZMod n) {L m : ℕ} (r : Fin L → Fin m → ZMod n) :
    pbGroupAnswers Pred G (x.val • G) h r = pbAnswers (fun z => Pred (z.val • G)) x r := by
  have h2z := ProofsF3F4a.two_ne_zero_zmod n h2
  have h2h : (2 : ZMod n) * (h : ZMod n) = 1 := by
    have : (((2 * h) % n : ℕ) : ZMod n) = ((2 * h : ℕ) : ZMod n) := ZMod.natCast_mod _ _
    rw [hh] at this
    push_cast at this
    exact this.symm
  have hinv : (h : ZMod n) = (2 : ZMod n)⁻¹ := by
    rw [← one_mul (2 : ZMod n)⁻¹, ← h2h, mul_comm (2 : ZMod n), mul_assoc, mul_inv_cancel₀ h2z,
      mul_one]
  funext t i
  unfold pbGroupAnswers pbAnswers
  congr 1
  rw [smul_smul, ← add_nsmul, ← val_natCast_nsmul G n hG]
  congr 2
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hinv, mul_comm]

/-- PB-5. `GroupNoisyHalvingRecovers`. -/
theorem groupNoisyHalvingRecovers : Ecdlp.ParityFourier.GroupNoisyHalvingRecovers := by
  intro A _ _ G n _ h2 hG h hh Pred ε hP hn78 x N L m hN hL
  have hsub : ∀ r : Fin L → Fin m → ZMod n,
      pbGroupOutput G (x.val • G) N r (pbGroupAnswers Pred G (x.val • G) h r) ⊆ {x} := by
    intro r x' hx'
    unfold pbGroupOutput at hx'
    rw [mem_filter] at hx'
    exact mem_singleton.mpr (val_nsmul_injective G n hG hx'.2)
  refine ⟨hsub, ?_⟩
  have hgrid := noisyHalvingGrid_frac n h2 (fun z => Pred (z.val • G)) ε hP hn78 x N L m hN hL
  refine le_trans ?_ hgrid
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hs : univ.filter (fun r : Fin L → Fin m → ZMod n =>
        pbGroupOutput G (x.val • G) N r (pbGroupAnswers Pred G (x.val • G) h r) ≠ {x}) ⊆
      univ.filter (fun r : Fin L → Fin m → ZMod n =>
        x ∉ pbCandidates N r (pbAnswers (fun z => Pred (z.val • G)) x r)) := by
    apply monotone_filter_right
    intro r _ hne hx
    apply hne
    apply Subset.antisymm (hsub r)
    rw [singleton_subset_iff]
    unfold pbGroupOutput
    rw [mem_filter, pbGroupAnswers_eq G n h2 hG h hh Pred x r]
    exact ⟨hx, rfl⟩
  exact_mod_cast card_le_card hs

end Ecdlp.ParityFourier.ProofsPB
