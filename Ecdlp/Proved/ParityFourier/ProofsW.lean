import Ecdlp.Proved.ParityFourier.StatementsW
import Ecdlp.Proved.ParityFourier.ProofsK

/-!
# Proofs of W (the window law; row W of the parity coverage map)

Proves the frozen statements `Ecdlp.ParityFourier.WindowShape`, `Ecdlp.ParityFourier.WindowLaw`,
`Ecdlp.ParityFourier.WindowRefined` and `Ecdlp.ParityFourier.WindowX` from `Ecdlp.Proved.ParityFourier.StatementsW`.

Outline (`v = k.val`, read as an integer in `[0, n)`):
1. membership: `k ∈ windowW n c` iff `1 ≤ v ≤ 2c` (for `c > 0`) or `n + 2c ≤ v`
   (for `c ≤ 0`), because the integers of the defining interval lie in `[-n, n)`;
2. reflection: for `k ≠ 0` outside the window, `2c - v ∈ [-n, 0)`, so the residue
   `2c - k` has value `n + 2c - v`; it is nonzero, lies outside the window, and
   `(n + 2c - v) + v = n + 2c` is odd, so `sgn` flips (W-shape);
3. W-law: split the sum over `k ≠ 0` into the window and its complement `D`; the
   reflection is an involution of `D` that flips `sgn`, so
   `∑_D sgn(k) F(2c - k) = -∑_D F(k) sgn(k)`, which gives the identity; the bound is the
   triangle inequality with `|sgn| = 1` and `|F| ≤ 1`;
4. W-refined: the off-window sum vanishes, and `F(c) = 0` with `c` in the window leaves
   at most `2|c| - 1` window terms;
5. W-x: with `F(k) = xFeature W Φ 0 ([k]G + [r]G)` and `c = -r`, the point of
   `2c - k` is `-([k]G + [r]G)` (since `[m]G` depends only on `m mod n`), negation keeps
   the x-coordinate (`ProofsK.xFeature_neg`), and `F(c) = xFeature(O) = 0`; then W-refined.

Provenance (disclosed in `StatementsW.lean`): the computation of the value of the reflected
residue (step 2, here `val_refl`), the parity argument for the `sgn` flip, and the
reindexing of the off-window sum along the reflection (step 3, here `sum_refl`) follow the
scratch proofs `windowSigma` and `windowAbstract` of `bv/paperlean/Window.lean`
(session 3eaafce7), which treat a natural number `c` and real `F`. The membership
characterisation for `windowW` and the `c < 0` case, complex `F`, the exact W-law identity,
the counting of nonzero window terms, symmetry assumed only off the window, and W-x are
new here.
-/

namespace Ecdlp.ParityFourier.ProofsW

open Ecdlp.ParityFourier Finset

section Residues

variable {n : ℕ} [NeZero n]

/-- The value of an integer in `[0, n)` cast to `ZMod n`. -/
lemma val_intCast_of_nonneg (a : ℤ) (h0 : 0 ≤ a) (h1 : a < n) :
    (((a : ZMod n).val : ℕ) : ℤ) = a := by
  rw [ZMod.val_intCast]
  exact Int.emod_eq_of_lt h0 h1

/-- The value of an integer in `[-n, 0)` cast to `ZMod n`. -/
lemma val_intCast_of_neg (a : ℤ) (h0 : -(n : ℤ) ≤ a) (h1 : a < 0) :
    (((a : ZMod n).val : ℕ) : ℤ) = a + n := by
  rw [ZMod.val_intCast]
  have h : (a + n) % (n : ℤ) = a % n := Int.add_emod_right a n
  rw [← h]
  exact Int.emod_eq_of_lt (by omega) (by omega)

lemma intCast_val (k : ZMod n) : (((k.val : ℕ) : ℤ) : ZMod n) = k := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

omit [NeZero n] in
/-- Bounds on `c` from `2|c| < n`. -/
lemma c_bounds {c : ℤ} (hc : 2 * |c| < n) : 2 * c < n ∧ -(n : ℤ) < 2 * c := by
  have h1 := le_abs_self c
  have h2 := neg_abs_le c
  constructor <;> omega

/-- Membership in the window through the value of the residue. -/
lemma mem_windowW_iff {c : ℤ} (hc : 2 * |c| < n) (k : ZMod n) :
    k ∈ windowW n c ↔
      (0 < c ∧ 1 ≤ (k.val : ℤ) ∧ (k.val : ℤ) ≤ 2 * c) ∨ (c ≤ 0 ∧ (n : ℤ) + 2 * c ≤ k.val) := by
  obtain ⟨hc1, hc2⟩ := c_bounds hc
  have hvn : ((k.val : ℕ) : ℤ) < n := by exact_mod_cast ZMod.val_lt k
  have hv0 : (0 : ℤ) ≤ ((k.val : ℕ) : ℤ) := Int.natCast_nonneg _
  unfold windowW
  split_ifs with hpos
  · simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
      rw [val_intCast_of_nonneg m (by omega) (by omega)]
      exact Or.inl ⟨hpos, h1, h2⟩
    · rintro (⟨_, h1, h2⟩ | ⟨h, _⟩)
      · exact ⟨(k.val : ℤ), ⟨h1, h2⟩, intCast_val k⟩
      · omega
  · simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
      rw [val_intCast_of_neg m (by omega) (by omega)]
      exact Or.inr ⟨by omega, by omega⟩
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · omega
      · refine ⟨(k.val : ℤ) - n, ⟨by omega, by omega⟩, ?_⟩
        push_cast
        rw [ZMod.natCast_self, sub_zero, ZMod.natCast_zmod_val]

lemma zero_not_mem_windowW {c : ℤ} (hc : 2 * |c| < n) : (0 : ZMod n) ∉ windowW n c := by
  obtain ⟨hc1, hc2⟩ := c_bounds hc
  rw [mem_windowW_iff hc, ZMod.val_zero, Nat.cast_zero]
  omega

omit [NeZero n] in
lemma card_windowW {c : ℤ} (hc : 2 * |c| < n) : (windowW n c).card = 2 * c.natAbs := by
  obtain ⟨hc1, hc2⟩ := c_bounds hc
  have hinj : ∀ a b : ℤ, -(n : ℤ) ≤ a → a < n → -(n : ℤ) ≤ b → b < n →
      a ≤ b → b - a < n → (a : ZMod n) = (b : ZMod n) → a = b := by
    intro a b _ _ _ _ hab hba h
    have hd : (n : ℤ) ∣ b - a := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [h, sub_self]
    obtain ⟨q, hq⟩ := hd
    rcases lt_trichotomy q 0 with hq0 | hq0 | hq0
    · nlinarith
    · subst hq0; linarith
    · nlinarith
  have hinj' : ∀ s : Finset ℤ, (∀ a ∈ s, -(n : ℤ) ≤ a ∧ a < n) →
      (∀ a ∈ s, ∀ b ∈ s, a ≤ b → b - a < n) →
      Set.InjOn (fun m : ℤ => (m : ZMod n)) s := by
    intro s hs hd a ha b hb h
    rcases le_total a b with hab | hab
    · exact hinj a b (hs a ha).1 (hs a ha).2 (hs b hb).1 (hs b hb).2 hab (hd a ha b hb hab) h
    · exact (hinj b a (hs b hb).1 (hs b hb).2 (hs a ha).1 (hs a ha).2 hab (hd b hb a ha hab)
        h.symm).symm
  unfold windowW
  split_ifs with hpos
  · rw [Finset.card_image_of_injOn]
    · rw [Int.card_Icc]
      omega
    · refine hinj' _ ?_ ?_
      · intro a ha
        rw [Finset.mem_Icc] at ha
        omega
      · intro a ha b hb _
        rw [Finset.mem_Icc] at ha hb
        omega
  · rw [Finset.card_image_of_injOn]
    · rw [Int.card_Icc]
      omega
    · refine hinj' _ ?_ ?_
      · intro a ha
        rw [Finset.mem_Icc] at ha
        omega
      · intro a ha b hb _
        rw [Finset.mem_Icc] at ha hb
        omega

omit [NeZero n] in
lemma self_mem_windowW {c : ℤ} (hc0 : c ≠ 0) :
    (c : ZMod n) ∈ windowW n c := by
  unfold windowW
  split_ifs with hpos
  · exact Finset.mem_image.mpr ⟨c, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
  · exact Finset.mem_image.mpr ⟨c, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩

/-- The value of the reflected residue `2c - k`, for `k ≠ 0` outside the window. -/
lemma val_refl {c : ℤ} (hc : 2 * |c| < n) {k : ZMod n} (hk0 : k ≠ 0)
    (hkW : k ∉ windowW n c) :
    (((((2 * c : ℤ) : ZMod n) - k).val : ℕ) : ℤ) = n + 2 * c - k.val := by
  obtain ⟨hc1, hc2⟩ := c_bounds hc
  have hvn : ((k.val : ℕ) : ℤ) < n := by exact_mod_cast ZMod.val_lt k
  have hv1 : (1 : ℤ) ≤ ((k.val : ℕ) : ℤ) := by
    have := (ZMod.val_pos (a := k)).mpr hk0
    omega
  rw [mem_windowW_iff hc] at hkW
  have hcast : ((2 * c : ℤ) : ZMod n) - k = ((2 * c - (k.val : ℤ) : ℤ) : ZMod n) := by
    rw [Int.cast_sub, intCast_val]
  rw [hcast, val_intCast_of_neg _ (by omega) (by omega)]
  ring


/-- The reflection `k ↦ 2c - k` maps nonzero residues outside the window to nonzero residues
outside the window and flips `sgn`. -/
lemma refl_facts (hn : Odd n) {c : ℤ} (hc : 2 * |c| < n) {k : ZMod n} (hk0 : k ≠ 0)
    (hkW : k ∉ windowW n c) :
    ((2 * c : ℤ) : ZMod n) - k ≠ 0 ∧ ((2 * c : ℤ) : ZMod n) - k ∉ windowW n c ∧
      sgn (((2 * c : ℤ) : ZMod n) - k) = - sgn k := by
  obtain ⟨hc1, hc2⟩ := c_bounds hc
  have hv := val_refl hc hk0 hkW
  have hvn : ((k.val : ℕ) : ℤ) < n := by exact_mod_cast ZMod.val_lt k
  have hv1 : (1 : ℤ) ≤ ((k.val : ℕ) : ℤ) := by
    have := (ZMod.val_pos (a := k)).mpr hk0
    omega
  have hkW' := hkW
  rw [mem_windowW_iff hc] at hkW'
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    rw [h0, ZMod.val_zero, Nat.cast_zero] at hv
    omega
  · rw [mem_windowW_iff hc, hv]
    omega
  · have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
    unfold sgn
    rcases Nat.even_or_odd k.val with he | ho
    · have he' := Nat.even_iff.mp he
      have hw : Odd (((2 * c : ℤ) : ZMod n) - k).val := Nat.odd_iff.mpr (by omega)
      rw [hw.neg_one_pow, he.neg_one_pow]
    · have ho' := Nat.odd_iff.mp ho
      have hw : Even (((2 * c : ℤ) : ZMod n) - k).val := Nat.even_iff.mpr (by omega)
      rw [hw.neg_one_pow, ho.neg_one_pow, neg_neg]

/-- The reflection is an involution of the off-window set that flips `sgn`. -/
lemma sum_refl (hn : Odd n) {c : ℤ} (hc : 2 * |c| < n) (F : ZMod n → ℂ) :
    ∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c,
        (sgn k : ℂ) * F (((2 * c : ℤ) : ZMod n) - k) =
      -∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c, F k * (sgn k : ℂ) := by
  have hmem : ∀ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c, k ≠ 0 ∧ k ∉ windowW n c := by
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true] at hk
    exact hk
  have hmaps : ∀ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c,
      ((2 * c : ℤ) : ZMod n) - k ∈ (univ.erase (0 : ZMod n)) \ windowW n c := by
    intro k hk
    obtain ⟨h0, hW⟩ := hmem k hk
    obtain ⟨h1, h2, _⟩ := refl_facts hn hc h0 hW
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨h1, h2⟩
  have hinv : ∀ k : ZMod n, ((2 * c : ℤ) : ZMod n) - (((2 * c : ℤ) : ZMod n) - k) = k :=
    fun k => sub_sub_cancel _ _
  calc ∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c,
        (sgn k : ℂ) * F (((2 * c : ℤ) : ZMod n) - k)
      = ∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c,
          (sgn (((2 * c : ℤ) : ZMod n) - k) : ℂ) * F k := by
        refine Finset.sum_nbij' (fun k => ((2 * c : ℤ) : ZMod n) - k)
          (fun k => ((2 * c : ℤ) : ZMod n) - k) hmaps hmaps (fun k _ => hinv k)
          (fun k _ => hinv k) ?_
        intro k _
        simp only [hinv]
    _ = ∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c, -(F k * (sgn k : ℂ)) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        obtain ⟨h0, hW⟩ := hmem k hk
        rw [(refl_facts hn hc h0 hW).2.2]
        push_cast
        ring
    _ = _ := Finset.sum_neg_distrib _

omit [NeZero n] in
lemma norm_sgn (k : ZMod n) : ‖((sgn k : ℤ) : ℂ)‖ = 1 := by
  simp [sgn]

end Residues

/-- W-shape. -/
theorem windowShape : Ecdlp.ParityFourier.WindowShape := by
  intro n _ hn c hc
  exact ⟨card_windowW hc, zero_not_mem_windowW hc, fun hc0 => self_mem_windowW hc0,
    fun k hk0 hkW => refl_facts hn hc hk0 hkW⟩

/-- W-law. -/
theorem windowLaw : Ecdlp.ParityFourier.WindowLaw := by
  intro n _ hn c hc F
  have hWE : windowW n c ⊆ univ.erase (0 : ZMod n) := by
    intro k hk
    rw [Finset.mem_erase]
    refine ⟨fun h => zero_not_mem_windowW hc ?_, Finset.mem_univ _⟩
    rw [← h]
    exact hk
  have hsplit := Finset.sum_sdiff hWE (f := fun k => F k * (sgn k : ℂ))
  have hrefl := sum_refl hn hc F
  have hid : ∑ k ∈ univ.erase (0 : ZMod n), F k * (sgn k : ℂ) =
      ∑ k ∈ windowW n c, F k * (sgn k : ℂ) +
        (1 / 2 : ℂ) * ∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c,
          (sgn k : ℂ) * (F k - F (((2 * c : ℤ) : ZMod n) - k)) := by
    have hdist : ∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c,
          (sgn k : ℂ) * (F k - F (((2 * c : ℤ) : ZMod n) - k)) =
        ∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c, F k * (sgn k : ℂ) -
          ∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c,
            (sgn k : ℂ) * F (((2 * c : ℤ) : ZMod n) - k) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hdist, hrefl, ← hsplit]
    ring
  refine ⟨hid, fun hF => ?_⟩
  rw [hid]
  have hA : ‖∑ k ∈ windowW n c, F k * (sgn k : ℂ)‖ ≤
      (((windowW n c).filter (fun k => F k ≠ 0)).card : ℝ) := by
    rw [Finset.natCast_card_filter]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_sgn, mul_one]
    split_ifs with h
    · exact hF k
    · rw [not_not.mp h, norm_zero]
  have hB : ‖∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c,
        (sgn k : ℂ) * (F k - F (((2 * c : ℤ) : ZMod n) - k))‖ ≤
      ∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c, ‖F k - F (((2 * c : ℤ) : ZMod n) - k)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_sgn, one_mul]
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_div, norm_one, Complex.norm_two]
  calc _ ≤ ‖∑ k ∈ windowW n c, F k * (sgn k : ℂ)‖ +
        ‖(1 / 2 : ℂ) * ∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c,
          (sgn k : ℂ) * (F k - F (((2 * c : ℤ) : ZMod n) - k))‖ := norm_add_le _ _
    _ ≤ _ := by
        rw [norm_mul, hhalf]
        gcongr

/-- W-refined. -/
theorem windowRefined : Ecdlp.ParityFourier.WindowRefined := by
  intro n _ hn c hc0 hc F hF hFc hsym
  have hlaw := (windowLaw n hn c hc F).2 hF
  have hzero : ∑ k ∈ (univ.erase (0 : ZMod n)) \ windowW n c,
      ‖F k - F (((2 * c : ℤ) : ZMod n) - k)‖ = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_sdiff, Finset.mem_erase] at hk
    rw [hsym k hk.1.1 hk.2, sub_self, norm_zero]
  rw [hzero, mul_zero, add_zero] at hlaw
  have hsub : (windowW n c).filter (fun k => F k ≠ 0) ⊆ (windowW n c).erase (c : ZMod n) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_erase]
    refine ⟨fun h => hk.2 ?_, hk.1⟩
    rw [h]
    exact hFc
  have hcard : ((windowW n c).filter (fun k => F k ≠ 0)).card ≤ 2 * c.natAbs - 1 := by
    calc _ ≤ ((windowW n c).erase (c : ZMod n)).card := Finset.card_le_card hsub
      _ = (windowW n c).card - 1 := Finset.card_erase_of_mem (self_mem_windowW hc0)
      _ = 2 * c.natAbs - 1 := by rw [card_windowW hc]
  have hpos : 1 ≤ c.natAbs := Int.natAbs_pos.mpr hc0
  have h1 : (((windowW n c).filter (fun k => F k ≠ 0)).card : ℝ) ≤
      ((2 * c.natAbs - 1 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs] at h1
  push_cast at h1
  linarith

section Curve

/-- `[m]G` depends only on `m mod n`, read through `ZMod.val`. -/
lemma val_intCast_nsmul {A : Type} [AddCommGroup A] {G : A} {n : ℕ} [NeZero n]
    (hG : addOrderOf G = n) (a : ℤ) : ((a : ZMod n).val) • G = a • G := by
  rw [← natCast_zsmul, zsmul_eq_zsmul_iff_modEq, hG, ZMod.val_intCast]
  exact Int.mod_modEq a n

/-- An x-feature with value `0` at `O` is bounded by the bound on `Φ`. -/
lemma norm_xFeature_le {K : Type*} [Field K] (W : WeierstrassCurve K) {Φ : K → ℂ}
    (hΦ : ∀ t, ‖Φ t‖ ≤ 1) (P : W.toAffine.Point) : ‖xFeature W Φ 0 P‖ ≤ 1 := by
  cases P with
  | zero => simp [xFeature]
  | some x y h => exact hΦ x

end Curve

/-- W-x. -/
theorem windowX : Ecdlp.ParityFourier.WindowX := by
  intro K _ _ W G n _ hn hG r hr0 hr Φ hΦ
  have hc : 2 * |(-r)| < (n : ℤ) := by rwa [abs_neg]
  have hFb : ∀ k : ZMod n, ‖xFeature W Φ 0 (k.val • G + r • G)‖ ≤ 1 :=
    fun k => norm_xFeature_le W hΦ _
  have hFc : xFeature W Φ 0 ((((-r : ℤ) : ZMod n)).val • G + r • G) = 0 := by
    rw [val_intCast_nsmul hG, neg_zsmul, neg_add_cancel]
    rfl
  have hsym : ∀ k : ZMod n,
      xFeature W Φ 0 ((((2 * (-r) : ℤ) : ZMod n) - k).val • G + r • G) =
        xFeature W Φ 0 (k.val • G + r • G) := by
    intro k
    have h1 : ((2 * (-r) : ℤ) : ZMod n) - k = ((2 * (-r) - (k.val : ℤ) : ℤ) : ZMod n) := by
      rw [Int.cast_sub, intCast_val]
    rw [h1, val_intCast_nsmul hG, ← natCast_zsmul, ← add_zsmul, ← add_zsmul]
    have h2 : 2 * (-r) - (k.val : ℤ) + r = -((k.val : ℤ) + r) := by ring
    rw [h2, neg_zsmul, ProofsK.xFeature_neg]
  have key := windowRefined n hn (-r) (neg_ne_zero.mpr hr0) hc
    (fun k => xFeature W Φ 0 (k.val • G + r • G)) hFb hFc (fun k _ _ => hsym k)
  rw [Int.cast_neg, abs_neg] at key
  exact key

end Ecdlp.ParityFourier.ProofsW
