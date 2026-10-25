import Mathlib
import Ecdlp.Proved.SemaevThree
import Ecdlp.Proved.SemaevFour

/-!
# Semaev degree ⇒ bounded decomposition fan-out (a prime-field barrier ingredient, secp256k1)

Index calculus decomposes a target point `R = P₁ + P₂` and, by `PointDecomposition.lean`, every
such decomposition satisfies the Semaev relation `S₃(x₁, x₂, x_R) = 0`. The *cost* of the attack is
governed by how many decompositions there are and how hard the Semaev system is to solve. This file
proves the one exact, kernel-checkable quantitative fact underneath that cost analysis: **the Semaev
polynomial has degree exactly `2` in its last variable when `x₁ ≠ x₂`, so for a fixed base
coordinate there are at most `2` completions to a 2-decomposition of `R`.**

* `secp256k1_S₃poly_natDegree` — for `x₁ ≠ x₂`, `S₃(x₁, x₂, ·)` is a degree-**exactly**-`2`
  polynomial (leading coefficient `(x₁ − x₂)²`, nonzero over the field `𝔽_p`). This is the base
  case of the classical `deg_{xᵢ} Sₘ = 2^{m−2}` tower — the degree doubling that makes higher-order
  decompositions blow up.
* `secp256k1_decomposition_completions_le_two` — fixing `x₁` and the target `x_R` (with `x₁ ≠ x_R`),
  **at most `2` field elements `x₂` complete a decomposition** `S₃(x₁, x₂, x_R) = 0`. The relation
  graph of index calculus has bounded fan-out at each factor-base point.

**Honest scope — this is an *ingredient*, not the barrier.** The full statement "ECDLP over `𝔽_p` is
`Θ(√n)`" is the open hardness conjecture and is **not** provable (a machine proof would settle a
famous open problem; see `BARRIERS.md`). What is rigorous and proved here is the degree/fan-out
fact. The reason it does not, by itself, yield a subexponential attack over the prime field — the
absence of Weil-restriction structure to split the single Semaev equation into a solvable system —
is a studied heuristic, recorded in `BARRIERS.md` as an open frontier, **not** asserted as a theorem.
No new axioms; fully kernel-checked.
-/

namespace Ecdlp.Semaev

open Polynomial Ecdlp.Curve

variable [Fact (Nat.Prime Secp256k1.p)]

/-- **The Semaev polynomial has degree exactly `2` in its last variable (secp256k1).**
For `x₁ ≠ x₂`, `S₃(x₁, x₂, ·)` — as a univariate polynomial over the field `𝔽_p` — has
`natDegree = 2`, its leading coefficient being `(x₁ − x₂)² ≠ 0`. Base case of the
`deg Sₘ = 2^{m−2}` degree tower. `S₃poly` is literally `C ((x₁−x₂)²)·X² + C(·)·X + C(·)`, so
`natDegree_quadratic` applies once the leading coefficient is shown nonzero. -/
theorem secp256k1_S₃poly_natDegree (x₁ x₂ : ZMod Secp256k1.p) (hx : x₁ ≠ x₂) :
    (S₃poly (0 : ZMod Secp256k1.p) 7 x₁ x₂).natDegree = 2 := by
  rw [S₃poly]
  exact natDegree_quadratic (pow_ne_zero 2 (sub_ne_zero.mpr hx))

/-- **Bounded decomposition fan-out for secp256k1 (index-calculus cost ingredient).** Fix a base
coordinate `x₁` and the target's coordinate `x_R`, with `x₁ ≠ x_R`. Then **at most `2` field
elements `x₂` complete a 2-decomposition** of the target, i.e. satisfy `S₃(x₁, x₂, x_R) = 0`: any
finite set of such completions has cardinality `≤ 2`. Immediate from the Semaev polynomial having
degree `2` (a degree-`2` polynomial over a field has at most `2` roots). Quantifies the bounded
fan-out of the index-calculus relation graph at each factor-base point. -/
theorem secp256k1_decomposition_completions_le_two
    (x₁ xR : ZMod Secp256k1.p) (hx : x₁ ≠ xR)
    (s : Finset (ZMod Secp256k1.p))
    (hs : ∀ x₂ ∈ s, S₃ (0 : ZMod Secp256k1.p) 7 x₁ x₂ xR = 0) :
    s.card ≤ 2 := by
  set q : (ZMod Secp256k1.p)[X] := S₃poly (0 : ZMod Secp256k1.p) 7 x₁ xR with hq
  have hqdeg : q.natDegree = 2 := secp256k1_S₃poly_natDegree x₁ xR hx
  have hqne : q ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hqdeg; exact absurd hqdeg (by norm_num)
  have hsub : s ⊆ q.roots.toFinset := by
    intro x₂ hx₂
    rw [Multiset.mem_toFinset, mem_roots']
    refine ⟨hqne, ?_⟩
    show q.eval x₂ = 0
    rw [hq, S₃poly_eval, ← S₃_symm₂₃]
    exact hs x₂ hx₂
  calc s.card ≤ q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := q.card_roots'
    _ = 2 := hqdeg

end Ecdlp.Semaev
