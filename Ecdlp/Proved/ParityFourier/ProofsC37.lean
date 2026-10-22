import Ecdlp.Proved.ParityFourier.StatementsC37
import Ecdlp.Proved.ParityFourier.ProofsF3F4a
import Ecdlp.Proved.ParityFourier.ProofsF4b

/-!
# Proofs of C37 (relabelling with a defect; exact branch oracle gives the DL; square-root branch)

Proves the frozen statements `Ecdlp.ParityFourier.RelabelDefect`, `Ecdlp.ParityFourier.RelabelDL` and
`Ecdlp.ParityFourier.SqrtBranch` from `Ecdlp.Proved.ParityFourier.StatementsC37`.

Outline:
1. Pointwise relabelling. Off `Ω`, `c x = some v` with `v = ±1` and `σ x = v * b x`, so
   `relabelPred c P x = v * P x`; cancelling `v` gives `v P = σ ↔ P = b`, and multiplying
   by `v` (with `v * v = 1`) gives `v P = b ↔ P = σ`.
2. C37-1. The two agreement sets of each item coincide off `Ω`, so the agreement set of the
   input predictor lies in the agreement set of `relabelPred c P` union `Ω`; hence its card is
   at most the new count plus `|Ω| ≤ δ |X|`, and items (1)–(2) follow by linear arithmetic.
   For item (3), `Ω = ∅` makes `c` total; with `c' = c.getD 1` (a `±1` function with
   `relabelPred c P = c' P`, `σ = c' b` and `b = c' σ`), both equalities are F3
   `ProofsF3F4a.relabel`, applied to `(σ, c', b)` and to `(b, c', σ)`.
3. C37-DL. On `y.val • G` with `y ≠ 0` the relabelled oracle equals `sgn y = (-1)^y.val`
   (point 1 with `D = b`), the point is not `0` because `0 < y.val < addOrderOf G`, so
   `bitOfSign` reads `y.val % 2`; at `y = 0` the point is `0` and `bitOfSign` reads `0`.
   This is the exact parity oracle of F4b, and `ProofsF4b.groupHalvingRecovers` concludes.
4. C37-sqrt. `s ≠ 0` and `s' ≠ 0` because their squares are `R ≠ 0`; `(M/s)^2 = R/R = 1`
   and `(s/s')^2 = 1`, so both are `±1` (`sq_eq_one_iff`), and `M/s * (s/s') = M/s'`
   cancels `s`.

Provenance: no proof of these statements existed when `StatementsC37.lean` was frozen; all
proofs here are new. Item (3) of C37-1 applies F3 (`ProofsF3F4a.relabel`); C37-DL applies
F4b (`ProofsF4b.groupHalvingRecovers`).
-/

namespace Ecdlp.ParityFourier.ProofsC37

open Finset Ecdlp.ParityFourier

/-- Pointwise relabelling off the exceptional set: with `c x = some v`, `v = ±1` and
`σ x = v * b x`, the relabelled predictor agrees with `σ` iff `P` agrees with `b`, and agrees
with `b` iff `P` agrees with `σ`. -/
theorem relabelPred_iff {X : Type*} (sigma b : X → ℤ) (c : X → Option ℤ) (P : X → ℤ) (x : X)
    (v : ℤ) (hcx : c x = some v) (hv : v = 1 ∨ v = -1) (hs : sigma x = v * b x) :
    (relabelPred c P x = sigma x ↔ P x = b x) ∧ (relabelPred c P x = b x ↔ P x = sigma x) := by
  have hrel : relabelPred c P x = v * P x := by
    simp only [relabelPred, hcx]
  rw [hrel, hs]
  rcases hv with rfl | rfl
  · simp
  · constructor
    · constructor
      · intro h; linarith
      · intro h; rw [h]
    · constructor
      · intro h; linarith
      · intro h; rw [h]; ring

/-- If two predicates agree off `Ω`, the agreement set of `q` has card at most that of `p`
plus `|Ω|`. -/
theorem card_filter_le_add {X : Type*} [Fintype X] (Ω : Finset X) (p q : X → Prop)
    [DecidablePred p] [DecidablePred q] (hpq : ∀ x, x ∉ Ω → (p x ↔ q x)) :
    (univ.filter q).card ≤ (univ.filter p).card + Ω.card := by
  classical
  have hsub : univ.filter q ⊆ univ.filter p ∪ Ω := by
    intro x hx
    rw [mem_filter] at hx
    rw [mem_union, mem_filter]
    by_cases hxΩ : x ∈ Ω
    · exact Or.inr hxΩ
    · exact Or.inl ⟨mem_univ x, (hpq x hxΩ).mpr hx.2⟩
  exact (card_le_card hsub).trans (card_union_le _ _)

/-- The real-arithmetic step of items (1) and (2): an agreement count `a ≥ (1/2 + ε)|X|`
that exceeds the new count `a'` by at most `|Ω| ≤ δ |X|` gives `a' ≥ (1/2 + (ε - δ))|X|`. -/
theorem advantage_step (N a a' w ε δ : ℝ) (hw : w ≤ δ * N) (ha : (1 / 2 + ε) * N ≤ a)
    (hle : a ≤ a' + w) : (1 / 2 + (ε - δ)) * N ≤ a' := by
  nlinarith

/-- C37-1 (Proposition 1, items 1–3). -/
theorem relabelDefect : Ecdlp.ParityFourier.RelabelDefect := by
  intro X _ sigma b c Ω hc hΩ P ε δ hδ
  have hpt : ∀ x, x ∉ Ω →
      (relabelPred c P x = sigma x ↔ P x = b x) ∧ (relabelPred c P x = b x ↔ P x = sigma x) := by
    intro x hx
    obtain ⟨v, hcx, hs⟩ := hΩ x hx
    exact relabelPred_iff sigma b c P x v hcx (hc x v hcx) hs
  refine ⟨?_, ?_, ?_⟩
  · intro hA
    have hle := card_filter_le_add Ω (fun x => relabelPred c P x = sigma x)
      (fun x => P x = b x) (fun x hx => (hpt x hx).1)
    have hleR : ((univ.filter (fun x => P x = b x)).card : ℝ) ≤
        ((univ.filter (fun x => relabelPred c P x = sigma x)).card : ℝ) + (Ω.card : ℝ) := by
      exact_mod_cast hle
    exact advantage_step _ _ _ _ ε δ hδ hA hleR
  · intro hA
    have hle := card_filter_le_add Ω (fun x => relabelPred c P x = b x)
      (fun x => P x = sigma x) (fun x hx => (hpt x hx).2)
    have hleR : ((univ.filter (fun x => P x = sigma x)).card : ℝ) ≤
        ((univ.filter (fun x => relabelPred c P x = b x)).card : ℝ) + (Ω.card : ℝ) := by
      exact_mod_cast hle
    exact advantage_step _ _ _ _ ε δ hδ hA hleR
  · intro hempty
    subst hempty
    -- With `Ω = ∅` the label is total; `c' = c.getD 1` is the total `±1` label of F3.
    have hdef : ∀ x, ∃ v, c x = some v ∧ sigma x = v * b x := fun x => hΩ x (notMem_empty x)
    set c' : X → ℤ := fun x => (c x).getD 1 with hc'def
    have hcx : ∀ x, c x = some (c' x) := by
      intro x
      obtain ⟨v, hv, _⟩ := hdef x
      simp [hc'def, hv]
    have hc' : ∀ x, c' x = 1 ∨ c' x = -1 := fun x => hc x (c' x) (hcx x)
    have hsq : ∀ x, c' x * c' x = 1 := by
      intro x
      rcases hc' x with h | h <;> rw [h] <;> norm_num
    have hs : ∀ x, sigma x = c' x * b x := by
      intro x
      obtain ⟨v, hv, hsv⟩ := hdef x
      rw [hcx x, Option.some.injEq] at hv
      rw [hsv, hv]
    have hb : ∀ x, b x = c' x * sigma x := by
      intro x
      rw [hs x, ← mul_assoc, hsq x, one_mul]
    have hrel : ∀ x, relabelPred c P x = c' x * P x := by
      intro x
      simp only [relabelPred, hcx x]
    simp only [hrel]
    exact ⟨ProofsF3F4a.relabel X sigma c' b P hc' hs, ProofsF3F4a.relabel X b c' sigma P hc' hb⟩

/-- `bitOfSign` of the parity sign `(-1)^m` is `m % 2` away from the identity. -/
theorem bit_of_neg_one_pow (m : ℕ) : (if (-1 : ℤ) ^ m = 1 then 0 else 1) = m % 2 := by
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow, if_pos rfl, Nat.even_iff.mp he]
  · rw [ho.neg_one_pow, if_neg (by decide), Nat.odd_iff.mp ho]

/-- C37-DL (Corollary 2, exact case). -/
theorem relabelDL : Ecdlp.ParityFourier.RelabelDL := by
  intro A _ _ G n _ h2 hG h hh c b D hc hD x L hL
  refine ProofsF4b.groupHalvingRecovers A G n h2 hG h hh _ ?_ x L hL
  intro y
  by_cases hy : y = 0
  · subst hy
    simp [bitOfSign]
  · have hval0 : y.val ≠ 0 := by
      intro h0
      exact hy ((ZMod.val_eq_zero y).mp h0)
    have hlt : y.val < addOrderOf G := by
      rw [hG]
      exact ZMod.val_lt y
    have hne : y.val • G ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf hval0 hlt
    obtain ⟨v, hcv, hsv⟩ := hc y hy
    have hrel : relabelPred c D (y.val • G) = sgn y := by
      simp only [relabelPred, hcv]
      rw [hD y hy, hsv]
    simp only [bitOfSign, if_neg hne, hrel, sgn]
    exact bit_of_neg_one_pow y.val

/-- C37-sqrt (Section 2b). -/
theorem sqrtBranch : Ecdlp.ParityFourier.SqrtBranch := by
  intro K _ M R s s' hR hM hs hs'
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hR
    rw [← hs]
    ring
  have hs'0 : s' ≠ 0 := by
    rintro rfl
    apply hR
    rw [← hs']
    ring
  have hMs : (M / s) ^ 2 = 1 := by
    rw [div_pow, hM, hs, div_self hR]
  have hss : (s / s') ^ 2 = 1 := by
    rw [div_pow, hs, hs', div_self hR]
  refine ⟨sq_eq_one_iff.mp hMs, sq_eq_one_iff.mp hss, ?_⟩
  field_simp

end Ecdlp.ParityFourier.ProofsC37
