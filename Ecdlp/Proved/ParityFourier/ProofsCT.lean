import Ecdlp.Proved.ParityFourier.StatementsCT
import Ecdlp.Proved.ParityFourier.ProofsC44
import Ecdlp.Proved.ParityFourier.ProofsWT
import Ecdlp.Proved.ParityFourier.ProofsK

/-!
# Proofs of CT (Fourier transfer; L1 bounds of J and g; WT-J and WT-g)

Proves the frozen statements `Ecdlp.ParityFourier.CharTransfer`, `Ecdlp.ParityFourier.L1JBound`,
`Ecdlp.ParityFourier.L1GBound`, `Ecdlp.ParityFourier.WeilTransferLsbJ` and
`Ecdlp.ParityFourier.WeilTransferLsbG` from `Ecdlp.Proved.ParityFourier.StatementsCT`.

Outline (with `e = ZMod.stdAddChar`, `L = ∑_a |σ̂(a)| ≤ 2 + log n` from
`ProofsWT.sum_ft_sigma_le`):
1. CT: Fourier inversion of `T` turns the correlation into `∑_α T̂(α) ∑_{k ≠ 0} F(k) e(α k)`,
   and the triangle inequality finishes;
2. a trigonometric polynomial `∑_i c_i e(m_i k)` has Fourier L1 norm at most `∑_i |c_i|`;
3. L1J: `J(k) = σ(lam k) σ(lam² k)` is, by inversion of both factors, a trigonometric
   polynomial with coefficients `σ̂(a) σ̂(b)`, so its L1 norm is at most `L²`;
   L1G: `g(k) = σ(k) σ(lam k) σ(lam² k)` gives `L³` in the same way;
4. WT-J, WT-g: `WT` (`ProofsWT.weilTransfer`) with `b = σ` on `ZMod p` and `T = J` or `g`;
   `σ̂(0) = 1/p` and `|∑_{k ≠ 0} J(k)| ≤ n - 1`, while `∑_{k ≠ 0} g(k) = 0` because `g`
   is odd (`ProofsK`).

Provenance: CT, `l1_trig`, `J_trig` and L1J are ported from the scratch files
`map/CharTransfer.lean` and `map/L1J.lean` (session 3eaafce7, disclosed in
`StatementsCT.lean`). `g_trig`, L1G, WT-J and WT-g are new here.
-/

namespace Ecdlp.ParityFourier.ProofsCT

open Ecdlp.ParityFourier Finset

local notation "𝐞" => ZMod.stdAddChar

/-- CT. -/
theorem charTransfer : Ecdlp.ParityFourier.CharTransfer := by
  intro n _ F T C hC
  have hinv : ∀ k, T k = ∑ α : ZMod n, ft T α * 𝐞 (α * k) := fun k => ProofsC44.inversion T k
  have hswap : ∑ k ∈ univ.erase (0 : ZMod n), F k * T k
      = ∑ α : ZMod n, ft T α * ∑ k ∈ univ.erase (0 : ZMod n), F k * eChar (α * k) := by
    simp_rw [ProofsWT.eChar_eq]
    conv_lhs => arg 2; ext k; rw [hinv k, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hswap]
  calc ‖∑ α : ZMod n, ft T α * ∑ k ∈ univ.erase (0 : ZMod n), F k * eChar (α * k)‖
      ≤ ∑ α : ZMod n, ‖ft T α * ∑ k ∈ univ.erase (0 : ZMod n), F k * eChar (α * k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ α : ZMod n, ‖ft T α‖ * C := by
        refine Finset.sum_le_sum fun α _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hC α) (norm_nonneg _)
    _ = C * ∑ α : ZMod n, ‖ft T α‖ := by rw [← Finset.sum_mul, mul_comm]

section L1

variable {n : ℕ} [NeZero n]

/-- The Fourier L1 norm of a trigonometric polynomial is at most the L1 norm of its
coefficients. -/
lemma l1_trig {ι : Type*} (s : Finset ι) (c : ι → ℂ) (m : ι → ZMod n) :
    ∑ γ : ZMod n, ‖ft (fun k => ∑ i ∈ s, c i * 𝐞 (m i * k)) γ‖ ≤ ∑ i ∈ s, ‖c i‖ := by
  simp_rw [ProofsC44.ft_trig]
  calc ∑ γ : ZMod n, ‖∑ i ∈ s, c i * (if m i = γ then 1 else 0)‖
      ≤ ∑ γ : ZMod n, ∑ i ∈ s, ‖c i * (if m i = γ then (1 : ℂ) else 0)‖ :=
        sum_le_sum fun γ _ => norm_sum_le _ _
    _ = ∑ i ∈ s, ∑ γ : ZMod n, ‖c i * (if m i = γ then (1 : ℂ) else 0)‖ := sum_comm
    _ = ∑ i ∈ s, ‖c i‖ := by
        refine sum_congr rfl fun i _ => ?_
        simp only [mul_ite, mul_one, mul_zero, apply_ite norm, norm_zero]
        rw [sum_ite_eq]
        simp

/-- `J` as a trigonometric polynomial with coefficients `σ̂(a) σ̂(b)`. -/
lemma J_trig (lam : ZMod n) :
    JC lam = fun k => ∑ q ∈ (univ : Finset (ZMod n)) ×ˢ (univ : Finset (ZMod n)),
      (ft (sigmaC (n := n)) q.1 * ft (sigmaC (n := n)) q.2) *
        𝐞 ((lam * q.1 + lam ^ 2 * q.2) * k) := by
  funext k
  unfold JC
  rw [ProofsC44.inversion (sigmaC (n := n)) (lam * k),
    ProofsC44.inversion (sigmaC (n := n)) (lam ^ 2 * k), sum_mul_sum, sum_product]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  have e : 𝐞 ((lam * a + lam ^ 2 * b) * k) = 𝐞 (a * (lam * k)) * 𝐞 (b * (lam ^ 2 * k)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [e]
  ring

/-- `g` as a trigonometric polynomial with coefficients `σ̂(a) σ̂(b) σ̂(c)`. -/
lemma g_trig (lam : ZMod n) :
    (fun k => ((g lam k : ℤ) : ℂ)) = fun k =>
      ∑ q ∈ ((univ : Finset (ZMod n)) ×ˢ (univ : Finset (ZMod n))) ×ˢ (univ : Finset (ZMod n)),
        (ft (sigmaC (n := n)) q.1.1 * ft (sigmaC (n := n)) q.1.2 * ft (sigmaC (n := n)) q.2) *
          𝐞 ((q.1.1 + lam * q.1.2 + lam ^ 2 * q.2) * k) := by
  funext k
  have hg : ((g lam k : ℤ) : ℂ) = sigmaC k * sigmaC (lam * k) * sigmaC (lam ^ 2 * k) := by
    unfold g J sgn sigmaC
    push_cast
    ring
  rw [hg, ProofsC44.inversion (sigmaC (n := n)) k,
    ProofsC44.inversion (sigmaC (n := n)) (lam * k),
    ProofsC44.inversion (sigmaC (n := n)) (lam ^ 2 * k), sum_product, sum_product,
    sum_mul_sum, sum_mul]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c _ => ?_
  have e : 𝐞 ((a + lam * b + lam ^ 2 * c) * k)
      = 𝐞 (a * k) * 𝐞 (b * (lam * k)) * 𝐞 (c * (lam ^ 2 * k)) := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [e]
  ring

end L1

/-- L1J. -/
theorem l1JBound : Ecdlp.ParityFourier.L1JBound := by
  intro n _ hodd lam
  rw [J_trig]
  refine le_trans (l1_trig _ _ _) ?_
  rw [sum_product]
  simp_rw [norm_mul, ← mul_sum, ← sum_mul]
  have h := ProofsWT.sum_ft_sigma_le (m := n) hodd
  have h0 : 0 ≤ ∑ a : ZMod n, ‖ft (sigmaC (n := n)) a‖ := sum_nonneg fun _ _ => norm_nonneg _
  rw [sq]
  exact mul_le_mul h h h0 (le_trans h0 h)

/-- L1G. -/
theorem l1GBound : Ecdlp.ParityFourier.L1GBound := by
  intro n _ hodd lam
  rw [g_trig]
  refine le_trans (l1_trig _ _ _) ?_
  rw [sum_product, sum_product]
  simp_rw [norm_mul, ← mul_sum, ← sum_mul]
  have h := ProofsWT.sum_ft_sigma_le (m := n) hodd
  have h0 : 0 ≤ ∑ a : ZMod n, ‖ft (sigmaC (n := n)) a‖ := sum_nonneg fun _ _ => norm_nonneg _
  have e : (∑ a : ZMod n, ‖ft (sigmaC (n := n)) a‖) * (∑ a : ZMod n, ‖ft (sigmaC (n := n)) a‖) *
      (∑ a : ZMod n, ‖ft (sigmaC (n := n)) a‖) = (∑ a : ZMod n, ‖ft (sigmaC (n := n)) a‖) ^ 3 := by
    ring
  rw [← sum_mul_sum, e]
  exact pow_le_pow_left₀ h0 h 3

section Transfer

variable {m : ℕ} [NeZero m]

/-- `σ̂(0) = 1/m` for odd `m`. -/
lemma norm_ft_sigma_zero (hodd : Odd m) : ‖ft (sigmaC (n := m)) 0‖ = 1 / (m : ℝ) := by
  have hall : ∑ k : ZMod m, sigmaC k = 1 := by
    have h0 := Finset.add_sum_erase (univ : Finset (ZMod m)) (sigmaC (n := m)) (mem_univ 0)
    rw [ProofsWT.sum_sigma_erase hodd] at h0
    have hs0 : sigmaC (0 : ZMod m) = 1 := by simp [sigmaC]
    rw [hs0] at h0
    rw [← h0]
    ring
  rw [ProofsC44.ft_eq]
  simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
  rw [hall, mul_one, norm_div, norm_one, Complex.norm_natCast]

/-- `|∑_{k ≠ 0} J(k)| ≤ m - 1`. -/
lemma norm_sum_JC_le (lam : ZMod m) :
    ‖∑ k ∈ univ.erase (0 : ZMod m), JC lam k‖ ≤ (m : ℝ) - 1 := by
  refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
  have h1 : ∀ k ∈ univ.erase (0 : ZMod m), ‖JC lam k‖ = 1 := by
    intro k _
    unfold JC
    rw [norm_mul, ProofsC44.norm_sigmaC, ProofsC44.norm_sigmaC, mul_one]
  rw [sum_congr rfl h1, sum_const, card_erase_of_mem (mem_univ _), card_univ, ZMod.card,
    nsmul_eq_mul, mul_one]
  have hm : 1 ≤ m := NeZero.one_le
  push_cast [hm]
  ring

/-- `∑_{k ≠ 0} g(k) = 0` (oddness of `g`). -/
lemma sum_gC_erase {n : ℕ} [Fact n.Prime] (hn2 : n ≠ 2) {lam : ZMod n}
    (hlam : lam ^ 2 + lam + 1 = 0) :
    ∑ k ∈ univ.erase (0 : ZMod n), ((g lam k : ℤ) : ℂ) = 0 := by
  haveI : NeZero n := ⟨(Fact.out : n.Prime).ne_zero⟩
  have h := ProofsK.sum_even_mul_odd (fun _ : ZMod n => (1 : ℂ)) (fun k => ((g lam k : ℤ) : ℂ))
    (fun _ => rfl) (ProofsK.gC_neg hn2 hlam)
  simpa using h

end Transfer

/-- WT-J. -/
theorem weilTransferLsbJ : Ecdlp.ParityFourier.WeilTransferLsbJ := by
  intro n p _ _ _ _ hn2 hp2 lam V hV
  have hnodd : Odd n := (Fact.out : n.Prime).odd_of_ne_two hn2
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h := ProofsWT.weilTransfer n p V (sigmaC (n := p)) (JC lam) (2 * Real.sqrt p) hV
  refine le_trans h ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 : ‖ft (sigmaC (n := p)) 0‖ * ‖∑ k ∈ univ.erase (0 : ZMod n), JC lam k‖
      ≤ ((n : ℝ) - 1) / p := by
    rw [norm_ft_sigma_zero hpodd, one_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (norm_sum_JC_le lam) hp0.le
  have hLp : ∑ a ∈ (univ.erase (0 : ZMod p)), ‖ft (sigmaC (n := p)) a‖ ≤ 2 + Real.log p :=
    le_trans (Finset.sum_le_univ_sum_of_nonneg fun _ => norm_nonneg _)
      (ProofsWT.sum_ft_sigma_le hpodd)
  have hLn := l1JBound n hnodd lam
  have h0p : 0 ≤ ∑ a ∈ (univ.erase (0 : ZMod p)), ‖ft (sigmaC (n := p)) a‖ :=
    sum_nonneg fun _ _ => norm_nonneg _
  have h0n : 0 ≤ ∑ α : ZMod n, ‖ft (JC lam) α‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hs : 0 ≤ 2 * Real.sqrt p := by positivity
  have hlogp : 0 ≤ 2 + Real.log p := le_trans h0p hLp
  have h2 : 2 * Real.sqrt p * (∑ a ∈ (univ.erase (0 : ZMod p)), ‖ft (sigmaC (n := p)) a‖) *
        (∑ α : ZMod n, ‖ft (JC lam) α‖)
      ≤ 2 * Real.sqrt p * (2 + Real.log p) * (2 + Real.log n) ^ 2 :=
    calc 2 * Real.sqrt p * (∑ a ∈ (univ.erase (0 : ZMod p)), ‖ft (sigmaC (n := p)) a‖) *
          (∑ α : ZMod n, ‖ft (JC lam) α‖)
        ≤ 2 * Real.sqrt p * (2 + Real.log p) * (∑ α : ZMod n, ‖ft (JC lam) α‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLp hs) h0n
      _ ≤ 2 * Real.sqrt p * (2 + Real.log p) * (2 + Real.log n) ^ 2 :=
          mul_le_mul_of_nonneg_left hLn (mul_nonneg hs hlogp)
  linarith

/-- WT-g. -/
theorem weilTransferLsbG : Ecdlp.ParityFourier.WeilTransferLsbG := by
  intro n p _ _ _ _ hn2 hp2 lam hlam V hV
  have hnodd : Odd n := (Fact.out : n.Prime).odd_of_ne_two hn2
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h := ProofsWT.weilTransfer n p V (sigmaC (n := p)) (fun k => ((g lam k : ℤ) : ℂ))
    (2 * Real.sqrt p) hV
  rw [sum_gC_erase hn2 hlam, norm_zero, mul_zero, zero_add] at h
  refine le_trans h ?_
  have hLp : ∑ a ∈ (univ.erase (0 : ZMod p)), ‖ft (sigmaC (n := p)) a‖ ≤ 2 + Real.log p :=
    le_trans (Finset.sum_le_univ_sum_of_nonneg fun _ => norm_nonneg _)
      (ProofsWT.sum_ft_sigma_le hpodd)
  have hLn := l1GBound n hnodd lam
  have h0p : 0 ≤ ∑ a ∈ (univ.erase (0 : ZMod p)), ‖ft (sigmaC (n := p)) a‖ :=
    sum_nonneg fun _ _ => norm_nonneg _
  have h0n : 0 ≤ ∑ α : ZMod n, ‖ft (fun k => ((g lam k : ℤ) : ℂ)) α‖ :=
    sum_nonneg fun _ _ => norm_nonneg _
  have hs : 0 ≤ 2 * Real.sqrt p := by positivity
  have hlogp : 0 ≤ 2 + Real.log p := le_trans h0p hLp
  calc 2 * Real.sqrt p * (∑ a ∈ (univ.erase (0 : ZMod p)), ‖ft (sigmaC (n := p)) a‖) *
        (∑ α : ZMod n, ‖ft (fun k => ((g lam k : ℤ) : ℂ)) α‖)
      ≤ 2 * Real.sqrt p * (2 + Real.log p) *
          (∑ α : ZMod n, ‖ft (fun k => ((g lam k : ℤ) : ℂ)) α‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLp hs) h0n
    _ ≤ 2 * Real.sqrt p * (2 + Real.log p) * (2 + Real.log n) ^ 3 :=
        mul_le_mul_of_nonneg_left hLn (mul_nonneg hs hlogp)

end Ecdlp.ParityFourier.ProofsCT
