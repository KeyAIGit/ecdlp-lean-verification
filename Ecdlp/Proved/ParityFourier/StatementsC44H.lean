import Ecdlp.Proved.ParityFourier.Statements
import Ecdlp.Proved.ParityFourier.StatementsC44

/-!
# Frozen statements C44-H and C44-9J (heavy Fourier coefficient; C44 Lemma 9 for J)

This file fixes the statements; proof files must not edit it. Disclosure: a
scratch proof of a `Finset (ZMod n)`-indexed variant of C44-H (`heavy_core` in
`lean-feasibility/HeavyCore.lean`, sha256
0297d67d5431c589582c8b4e66d00c3a7545c9a9bbfd3cfaae9e5a94423260c2; a scratch
file of session 3eaafce7, not in the repository) was compiled on 2026-10-22
before this file was written. No proof of C44-9J existed when this file was
written.

Process note: for HeavyCore, a scratch proof was found before this file was
written (session 3eaafce7, 2026-10-22); the statement was audited against the
paper claim, not against the proof. For JHeavy no proof existed at freeze
time.

Notation as in `Statements.lean` (`J`) and `StatementsC44.lean` (`ft`,
`GammaJ`, `L1low`). `stdAddChar a = exp(2 π i a.val / n)`.

* C44-H (generic core of `C44_J_G_HARDCORE_PROOF.md` Lemma 9, proof steps
  1–4): let `w` be bounded by `1`, let `Re((1/n) ∑_x w(x) f(x)) ≥ 2η > 0`
  (a bilinear correlation, no conjugate; this is why the frequency below is
  `-m_i`), and let `f` be `η`-close in normalised `L2` to a trigonometric
  polynomial `F = ∑_{i ∈ I} c_i e(m_i x)`. Then some frequency of `F`
  carries a heavy coefficient of `w`: `η ≤ (∑_j |c_j|) |ŵ(-m_i)|`.
* C44-9J (Lemma 9(J) with the kernel-checked constants of C44-6'): for a
  real `w` with `|w| ≤ 1`, `k ≠ 0`, and `(1 + L1low B)^2 / B ≤ η^2`, if
  `(1/n) ∑_x w(x) J(x k) ≥ 2η`, then some `α ∈ GammaJ lam B` has
  `η ≤ L1low(B)^2 |ŵ(α k)|`. The paper's sharper threshold `T_J(B) ≤ η^2`
  is replaced by the expression `(1 + L1low B)^2 / B` of C44-6' used as a
  threshold; by the audit's computation it exceeds `T_J(B)` by a factor of
  order `log^2 B` (about 25 at `B = 111` and about 160 at `B ≈ 3·10^7`), so
  for a given `η` the window `B` must be larger than in the paper. Reusing
  that expression does not make C44-9J a corollary of the C44-6' Prop alone.
  The paper's standing assumption `2B + 1 < n` is not made.

When C44-9J says something: the hypotheses force `η ≤ 1/2` (since `|w| ≤ 1`
and `|J| = 1`), so the threshold needs `(1 + L1low B)^2 / B ≤ 1/4`. The audit
found no admissible `(n, B)` with `n ≤ 163`, and found `GammaJ lam B` equal to
all of `ZMod n` in every admissible instance with `n < 37633`; there the
conclusion has no concentration content. `0 ∉ GammaJ lam B` (the Theorem 10
regime) holds when `3 (2B + 1)^2 < n` (C44-6d).

Not claimed here: Lemma 9(g), Theorem 10 and Corollary 11 of the C44
document, the paper's threshold `T_J(B)`, and the list-decoding and
hard-core chain (Akavia) are not stated.
-/

namespace Ecdlp.ParityFourier

open Finset

/-- C44-H. Correlation plus `L2` approximation by a trigonometric polynomial gives a heavy
coefficient, with the `L1` loss of the approximant. -/
def HeavyCore : Prop :=
  ∀ (n : ℕ) [NeZero n] (ι : Type) (I : Finset ι) (w f F : ZMod n → ℂ) (c : ι → ℂ)
    (m : ι → ZMod n),
    (∀ x, F x = ∑ i ∈ I, c i * ZMod.stdAddChar (m i * x)) → (∀ x, ‖w x‖ ≤ 1) →
    ∀ η : ℝ, 0 < η → 2 * η ≤ ((1 / (n : ℂ)) * ∑ x, w x * f x).re →
      (1 / (n : ℝ)) * ∑ x, ‖f x - F x‖ ^ 2 ≤ η ^ 2 →
        ∃ i ∈ I, η ≤ (∑ j ∈ I, ‖c j‖) * ‖ft w (-(m i))‖

/-- C44-9J. A bounded real `w` that correlates with `x ↦ J(x k)` has a heavy Fourier
coefficient at `α k` for some `α ∈ GammaJ lam B`. -/
def JHeavy : Prop :=
  ∀ (n : ℕ) [NeZero n] [Fact n.Prime], n ≠ 2 → ∀ (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    ∀ B : ℕ, 1 ≤ B → ∀ w : ZMod n → ℝ, (∀ x, |w x| ≤ 1) → ∀ k : ZMod n, k ≠ 0 →
    ∀ η : ℝ, 0 < η → (1 + L1low n B) ^ 2 / (B : ℝ) ≤ η ^ 2 →
      2 * η ≤ (1 / (n : ℝ)) * ∑ x, w x * (J lam (x * k) : ℝ) →
        ∃ α ∈ GammaJ lam B, η ≤ L1low n B ^ 2 * ‖ft (fun x => (w x : ℂ)) (α * k)‖

end Ecdlp.ParityFourier
