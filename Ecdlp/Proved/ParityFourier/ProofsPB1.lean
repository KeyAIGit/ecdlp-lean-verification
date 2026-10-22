import Ecdlp.Proved.ParityFourier.StatementsPB

/-!
# Proof of PB-1 (majority vote, counting form; row P of the parity coverage map)

Proves the frozen statement `Ecdlp.ParityFourier.MajorityVote` from `Ecdlp.Proved.ParityFourier.StatementsPB`
(frozen at commit 3230224) and exposes the counting-form lemmas that PB-4 is expected to use.

Outline:
1. measure form (`majorityVote_measure`): under the product `Measure.pi` of `m` uniform
   measures on a finite `Ω`, the centred coordinates `a - V (s i)` of a `[0, 1]`-valued `V`
   with mean `a` are independent (`iIndepFun_pi`) and sub-Gaussian with parameter `1/4`
   (Hoeffding's lemma, `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`); Mathlib's
   Hoeffding inequality `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` at level `m δ`
   bounds the probability that `∑ V (s i) ≤ m/2` by `exp(-2 m δ^2)`;
2. conversion (`pi_uniformOn_real_finset`): by `uniformOn_pi` the product of the uniform
   measures is the uniform measure on `Fin m → Ω`, so the measure of a finite set of tuples is
   its cardinality divided by `#(Fin m → Ω)`;
3. counting form (`majorityVote_card`, `majorityVote_frac`): `Ω` gets the discrete
   σ-algebra `⊤`, `V` is the indicator of `good`, and `∑ V (s i) ≤ m/2` is exactly
   `2 · #{i : good (s i)} ≤ m`; an empty `Ω` is handled separately;
4. PB-1 (`majorityVote`) is the fraction form.

Helpers for PB-4 (not needed for PB-1):
* `card_filter_row_div`: the fraction of tables `r : ι → β` whose row `t` lies in a set is
  the fraction of that set in `β` (split off row `t` with `Equiv.funSplitAt`);
* `card_filter_exists_le`: union bound, counting form;
* `majorityVote_rows`, `majorityVote_rows_of_imp`: for a table `r : ι → Fin m → Ω` and a good
  set `good t` of density at least `1/2 + δ` for each row index `t`, the fraction of tables
  having a row with at most half of its entries good (or any event forcing such a row) is at
  most `#ι · exp(-2 m δ^2)`;
* `two_mul_card_le_of_pbBit_ne`: if `pbBit` differs from a bit `b < 2`, at most half of the
  votes equal `b` (ties are failures, as in PB-1).

Provenance (disclosed in `StatementsPB.lean`): `integral_uniformOn_univ` and
`majorityVote_measure` are the pre-freeze scratch proofs `integral_uniform` and
`majority_vote` of `bv/lean-feasibility/MajorityVote.lean` (session 3eaafce7), ported with
renaming, the `[Nonempty Ω]` assumption moved to the theorem that needs it and one unused simp
argument removed. The conversion to counting measure, the counting form with an indicator,
the empty-`Ω` case, the table, union-bound and `pbBit` helpers are new here.
-/

namespace Ecdlp.ParityFourier.ProofsPB1

open Ecdlp.ParityFourier Finset MeasureTheory ProbabilityTheory

section MeasureForm

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The mean of `V` under the uniform measure on a finite type. -/
lemma integral_uniformOn_univ (V : Ω → ℝ) :
    ∫ ω, V ω ∂(uniformOn (Set.univ : Set Ω)) = (∑ ω, V ω) / Fintype.card Ω := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [smul_eq_mul]
  have h : ∀ ω : Ω, (uniformOn (Set.univ : Set Ω)).real {ω} = 1 / Fintype.card Ω := by
    intro ω
    simp [Measure.real, uniformOn_univ]
  simp_rw [h]
  rw [← Finset.mul_sum]
  ring

/-- Hoeffding for a majority of `m` i.i.d. uniform draws, measure form, with a `[0, 1]`-valued
score `V` of mean at least `1/2 + δ`. -/
theorem majorityVote_measure [Nonempty Ω] (V : Ω → ℝ) (hV : ∀ ω, V ω ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hmean : 1 / 2 + δ ≤ (∑ ω, V ω) / Fintype.card Ω) (m : ℕ) :
    (Measure.pi (fun _ : Fin m => uniformOn (Set.univ : Set Ω))).real
      {s | ∑ i, V (s i) ≤ (m : ℝ) / 2} ≤ Real.exp (-2 * m * δ ^ 2) := by
  set μ := Measure.pi (fun _ : Fin m => uniformOn (Set.univ : Set Ω)) with hμ
  set a : ℝ := (∑ ω, V ω) / Fintype.card Ω with ha
  let X : Fin m → (Fin m → Ω) → ℝ := fun i s => a - V (s i)
  have hind : iIndepFun X μ :=
    iIndepFun_pi (μ := fun _ : Fin m => uniformOn (Set.univ : Set Ω))
      (X := fun (_ : Fin m) (ω : Ω) => a - V ω) (fun _ => Measurable.of_discrete.aemeasurable)
  have hsub : ∀ i ∈ (univ : Finset (Fin m)),
      HasSubgaussianMGF (X i) ((‖(a - 0) - (a - 1)‖₊ / 2) ^ 2) μ := by
    intro i _
    have hint : ∫ s, X i s ∂μ = 0 := by
      have := integral_comp_eval (μ := fun _ : Fin m => uniformOn (Set.univ : Set Ω)) (i := i)
        (f := fun ω => a - V ω) (Measurable.of_discrete.aestronglyMeasurable)
      simp only [X]
      rw [this, integral_sub (integrable_const a) Integrable.of_finite, integral_const,
        integral_uniformOn_univ]
      simp [ha]
    apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    · exact Measurable.of_discrete.aemeasurable
    · refine ae_of_all _ fun s => ?_
      obtain ⟨h0, h1⟩ := hV (s i)
      simp only [X, Set.mem_Icc]
      constructor <;> linarith
    · exact hint
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub
    (ε := (m : ℝ) * δ) (by positivity)
  have hc : (‖(a - 0) - (a - 1)‖₊ / 2 : NNReal) ^ 2 = 1 / 4 := by
    have : (a - 0) - (a - 1) = (1 : ℝ) := by ring
    rw [this]
    ext
    simp
    norm_num
  rw [hc] at hH
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hH
  have hsubset : {s : Fin m → Ω | ∑ i, V (s i) ≤ (m : ℝ) / 2}
      ⊆ {s | (m : ℝ) * δ ≤ ∑ i, X i s} := by
    intro s hs
    simp only [Set.mem_setOf_eq, X] at hs ⊢
    rw [Finset.sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith
  calc μ.real {s | ∑ i, V (s i) ≤ (m : ℝ) / 2}
      ≤ μ.real {s | (m : ℝ) * δ ≤ ∑ i, X i s} := measureReal_mono hsubset
    _ ≤ Real.exp (-((m : ℝ) * δ) ^ 2 / (2 * ((m : ℝ) * (1 / 4 : NNReal)))) := hH
    _ = Real.exp (-2 * m * δ ^ 2) := by
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm; simp
        · congr 1
          have : (0 : ℝ) < m := by exact_mod_cast hm
          push_cast
          field_simp
          ring

/-- On a finite type the product of uniform measures is counting measure normalised by the
number of tuples. -/
lemma pi_uniformOn_real_finset (m : ℕ) (S : Finset (Fin m → Ω)) :
    (Measure.pi (fun _ : Fin m => uniformOn (Set.univ : Set Ω))).real (S : Set (Fin m → Ω)) =
      (S.card : ℝ) / (Fintype.card (Fin m → Ω) : ℝ) := by
  rw [← uniformOn_pi, Set.pi_univ, Measure.real, uniformOn_univ, Measure.count_apply_finset,
    ENNReal.toReal_div]
  simp

end MeasureForm

section CountingForm

/-- PB-1 with a general good set, in multiplied (division-free) form: if at least a `1/2 + δ`
fraction of `Ω` is good, `δ ≥ 0`, then the number of `m`-tuples in which at most half of the
entries are good is at most `exp(-2 m δ^2)` times the number of all `m`-tuples. `Ω` may be
empty. -/
theorem majorityVote_card {Ω : Type*} [Fintype Ω] (good : Ω → Prop) [DecidablePred good]
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgood : (1 / 2 + δ) * (Fintype.card Ω : ℝ) ≤ ((univ.filter good).card : ℝ)) (m : ℕ) :
    ((univ.filter (fun s : Fin m → Ω =>
        2 * (univ.filter (fun i => good (s i))).card ≤ m)).card : ℝ) ≤
      Real.exp (-2 * (m : ℝ) * δ ^ 2) * (Fintype.card (Fin m → Ω) : ℝ) := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [CharP.cast_eq_zero, mul_zero, zero_mul, Real.exp_zero, one_mul]
      exact_mod_cast card_le_univ _
    · have : IsEmpty (Fin m → Ω) := by
        rw [isEmpty_fun]
        exact ⟨⟨⟨0, hm⟩⟩, hΩ⟩
      simp
  letI : MeasurableSpace Ω := ⊤
  haveI : DiscreteMeasurableSpace Ω := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  set V : Ω → ℝ := fun ω => if good ω then 1 else 0 with hVdef
  have hV : ∀ ω, V ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro ω
    by_cases h : good ω <;> simp [V, h]
  have hsumV : ∑ ω, V ω = ((univ.filter good).card : ℝ) := by
    simp [V, Finset.sum_boole]
  have hcard : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hmean : 1 / 2 + δ ≤ (∑ ω, V ω) / Fintype.card Ω := by
    rw [hsumV, le_div_iff₀ hcard]
    exact hgood
  have hM := majorityVote_measure V hV δ hδ hmean m
  have hset : {s : Fin m → Ω | ∑ i, V (s i) ≤ (m : ℝ) / 2} =
      ((univ.filter (fun s : Fin m → Ω =>
        2 * (univ.filter (fun i => good (s i))).card ≤ m)) : Set (Fin m → Ω)) := by
    ext s
    simp only [Set.mem_setOf_eq, coe_filter, mem_univ, true_and]
    have hs : ∑ i, V (s i) = ((univ.filter (fun i => good (s i))).card : ℝ) := by
      simp [V, Finset.sum_boole]
    rw [hs]
    constructor
    · intro h
      have : (2 * (univ.filter (fun i => good (s i))).card : ℝ) ≤ m := by linarith
      exact_mod_cast this
    · intro h
      have : (2 * (univ.filter (fun i => good (s i))).card : ℝ) ≤ m := by exact_mod_cast h
      linarith
  rw [hset, pi_uniformOn_real_finset] at hM
  have hpos : (0 : ℝ) < Fintype.card (Fin m → Ω) := by exact_mod_cast Fintype.card_pos
  rwa [div_le_iff₀ hpos] at hM

/-- PB-1 with a general good set, fraction form (`Ω` may be empty). -/
theorem majorityVote_frac {Ω : Type*} [Fintype Ω] (good : Ω → Prop) [DecidablePred good]
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgood : (1 / 2 + δ) * (Fintype.card Ω : ℝ) ≤ ((univ.filter good).card : ℝ)) (m : ℕ) :
    ((univ.filter (fun s : Fin m → Ω =>
        2 * (univ.filter (fun i => good (s i))).card ≤ m)).card : ℝ) /
      (Fintype.card (Fin m → Ω) : ℝ) ≤ Real.exp (-2 * (m : ℝ) * δ ^ 2) := by
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card (Fin m → Ω))).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]
    exact (Real.exp_pos _).le
  · rw [div_le_iff₀ hpos]
    exact majorityVote_card good δ hδ hgood m

end CountingForm

section Tables

/-- The fraction of tables `r : ι → β` whose row `t` satisfies `p` equals the fraction of
rows satisfying `p`. -/
theorem card_filter_row_div {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (t : ι) (p : β → Prop) [DecidablePred p] :
    ((univ.filter (fun r : ι → β => p (r t))).card : ℝ) / (Fintype.card (ι → β) : ℝ) =
      ((univ.filter p).card : ℝ) / (Fintype.card β : ℝ) := by
  have h1 : (univ.filter (fun r : ι → β => p (r t))).card =
      (univ.filter p).card * Fintype.card ({j : ι // j ≠ t} → β) := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype, ← Fintype.card_prod]
    refine Fintype.card_congr ?_
    exact ((Equiv.funSplitAt t β).subtypeEquiv (p := fun r : ι → β => p (r t))
      (q := fun q : β × ({j : ι // j ≠ t} → β) => p q.1)
      (fun r => by simp)).trans Equiv.prodSubtypeFstEquivSubtypeProd
  have h2 : Fintype.card (ι → β) = Fintype.card β * Fintype.card ({j : ι // j ≠ t} → β) := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr (Equiv.funSplitAt t β)
  rcases isEmpty_or_nonempty β with hβ | hβ
  · have : IsEmpty (ι → β) := by
      rw [isEmpty_fun]
      exact ⟨⟨t⟩, hβ⟩
    simp
  · have hγ : (0 : ℝ) < Fintype.card ({j : ι // j ≠ t} → β) := by exact_mod_cast Fintype.card_pos
    rw [h1, h2]
    push_cast
    exact mul_div_mul_right _ _ hγ.ne'

/-- Union bound, counting form. -/
theorem card_filter_exists_le {α ι : Type*} [Fintype α] (s : Finset ι) (E : ι → α → Prop)
    [∀ t, DecidablePred (E t)] :
    ((univ.filter (fun a => ∃ t ∈ s, E t a)).card : ℝ) ≤
      ∑ t ∈ s, ((univ.filter (E t)).card : ℝ) := by
  classical
  have hsub : univ.filter (fun a => ∃ t ∈ s, E t a) ⊆
      s.biUnion (fun t => univ.filter (E t)) := by
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    obtain ⟨t, ht, hE⟩ := ha
    exact mem_biUnion.mpr ⟨t, ht, by simpa using hE⟩
  have := (card_le_card hsub).trans card_biUnion_le
  exact_mod_cast this

/-- Hoeffding plus a union bound over the rows of a table `r : ι → Fin m → Ω` (uniform over all
tables): if for each row index `t` at least a `1/2 + δ` fraction of `Ω` is `good t`, then the
fraction of tables having some row `t` with at most half of its entries `good t` is at most
`#ι · exp(-2 m δ^2)`. -/
theorem majorityVote_rows {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (good : ι → Ω → Prop) [∀ t, DecidablePred (good t)] (δ : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ t, (1 / 2 + δ) * (Fintype.card Ω : ℝ) ≤ ((univ.filter (good t)).card : ℝ))
    (m : ℕ) :
    ((univ.filter (fun r : ι → Fin m → Ω =>
        ∃ t, 2 * (univ.filter (fun i => good t (r t i))).card ≤ m)).card : ℝ) /
      (Fintype.card (ι → Fin m → Ω) : ℝ) ≤
      (Fintype.card ι : ℝ) * Real.exp (-2 * (m : ℝ) * δ ^ 2) := by
  have hU := card_filter_exists_le (α := ι → Fin m → Ω) (univ : Finset ι)
    (fun t r => 2 * (univ.filter (fun i => good t (r t i))).card ≤ m)
  simp only [mem_univ, true_and] at hU
  have hnn : (0 : ℝ) ≤ Fintype.card (ι → Fin m → Ω) := Nat.cast_nonneg _
  calc ((univ.filter (fun r : ι → Fin m → Ω =>
        ∃ t, 2 * (univ.filter (fun i => good t (r t i))).card ≤ m)).card : ℝ) /
      (Fintype.card (ι → Fin m → Ω) : ℝ)
      ≤ (∑ t, ((univ.filter (fun r : ι → Fin m → Ω =>
          2 * (univ.filter (fun i => good t (r t i))).card ≤ m)).card : ℝ)) /
        (Fintype.card (ι → Fin m → Ω) : ℝ) := div_le_div_of_nonneg_right hU hnn
    _ = ∑ t, ((univ.filter (fun r : ι → Fin m → Ω =>
          2 * (univ.filter (fun i => good t (r t i))).card ≤ m)).card : ℝ) /
        (Fintype.card (ι → Fin m → Ω) : ℝ) := by rw [Finset.sum_div]
    _ = ∑ t, ((univ.filter (fun s : Fin m → Ω =>
          2 * (univ.filter (fun i => good t (s i))).card ≤ m)).card : ℝ) /
        (Fintype.card (Fin m → Ω) : ℝ) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        exact card_filter_row_div t
          (fun s : Fin m → Ω => 2 * (univ.filter (fun i => good t (s i))).card ≤ m)
    _ ≤ ∑ _t : ι, Real.exp (-2 * (m : ℝ) * δ ^ 2) :=
        Finset.sum_le_sum fun t _ => majorityVote_frac (good t) δ hδ (hgood t) m
    _ = (Fintype.card ι : ℝ) * Real.exp (-2 * (m : ℝ) * δ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Variant of `majorityVote_rows` for an arbitrary event `E` of tables that forces some row
`t` to have at most half of its entries `good t`. -/
theorem majorityVote_rows_of_imp {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (good : ι → Ω → Prop) [∀ t, DecidablePred (good t)] (δ : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ t, (1 / 2 + δ) * (Fintype.card Ω : ℝ) ≤ ((univ.filter (good t)).card : ℝ))
    (m : ℕ) (E : (ι → Fin m → Ω) → Prop) [DecidablePred E]
    (hE : ∀ r, E r → ∃ t, 2 * (univ.filter (fun i => good t (r t i))).card ≤ m) :
    ((univ.filter E).card : ℝ) / (Fintype.card (ι → Fin m → Ω) : ℝ) ≤
      (Fintype.card ι : ℝ) * Real.exp (-2 * (m : ℝ) * δ ^ 2) := by
  refine le_trans ?_ (majorityVote_rows good δ hδ hgood m)
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast card_le_card (monotone_filter_right _ fun r _ => hE r)

end Tables

section Decision

/-- A wrong majority decision `pbBit` (against a bit `b < 2`) means that at most half of the
votes equal `b` (ties count as failures, as in PB-1). -/
theorem two_mul_card_le_of_pbBit_ne {n m : ℕ} (r : Fin m → ZMod n) (a : Fin m → ℕ) (c : ℚ)
    (b : ℕ) (hb : b < 2) (h : pbBit r a c ≠ b) :
    2 * (univ.filter (fun i => pbVote (a i) c (r i) = b)).card ≤ m := by
  unfold pbBit at h
  have hlt : ∀ i, pbVote (a i) c (r i) < 2 := fun i => by
    unfold pbVote
    exact Nat.mod_lt _ (by norm_num)
  interval_cases b
  · have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
      (fun i => pbVote (a i) c (r i) = 0)
    have hne : univ.filter (fun i => ¬ pbVote (a i) c (r i) = 0) =
        univ.filter (fun i => pbVote (a i) c (r i) = 1) := by
      refine filter_congr fun i _ => ?_
      have := hlt i
      omega
    rw [hne, card_univ, Fintype.card_fin] at hsplit
    split_ifs at h with hm
    · omega
    · exact absurd rfl h
  · split_ifs at h with hm
    · exact absurd rfl h
    · omega

end Decision

/-- PB-1. -/
theorem majorityVote : Ecdlp.ParityFourier.MajorityVote := by
  intro Ω _ _ good _ δ hδ hgood m
  exact majorityVote_frac good δ hδ hgood m

end Ecdlp.ParityFourier.ProofsPB1
