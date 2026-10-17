import Mathlib

/-!
# Frozen statements (KeyAI Parity Lab, consolidation stage, ADR 0022)

This file fixes the statements before any proof is searched. Proof files
prove these `Prop`s and must not edit this file; the Lean kernel then checks
that exactly these statements were proved.

Setting:
* `n` is a prime, `n ≠ 2`;
* `lam : ZMod n` satisfies `lam ^ 2 + lam + 1 = 0`, i.e. `lam` is a
  primitive cube root of unity mod `n`;
* `[k]` is `k.val`, the representative of `k` in `[0, n)`.

Definitions:
* `sgn k = (-1) ^ k.val` is the parity sign sigma;
* `J lam k = sgn (lam * k) * sgn (lam ^ 2 * k)` is the C44 ordered-sector
  sign;
* `g lam k = sgn k * J lam k` is the GLV carry sign.

Statements:
* F1: the carry identity and the symmetries of J and g;
* F2: the balance identity of J;
* F3: public relabelling transfers predictor agreement exactly (C37 note);
* F4: an exact parity oracle recovers the discrete logarithm by halving
  (Lauter-Stange, Prop. 2), first in `ZMod n` and then in any additive
  group, using group operations only.
-/

namespace Ecdlp.ParityFourier

open Finset

/-- Parity sign of the canonical representative: `(-1) ^ k.val`. -/
def sgn {n : ℕ} (k : ZMod n) : ℤ := (-1) ^ k.val

/-- The C44 ordered-sector sign `J(k) = sigma(lam k) * sigma(lam^2 k)`. -/
def J {n : ℕ} (lam k : ZMod n) : ℤ := sgn (lam * k) * sgn (lam ^ 2 * k)

/-- The GLV carry sign `g(k) = sigma(k) * J(k)`. -/
def g {n : ℕ} (lam k : ZMod n) : ℤ := sgn k * J lam k

/-- F1a. Carry identity: for `k ≠ 0`, `[k] + [lam k] + [lam^2 k]` is `n` or `2n`. -/
def CarrySum : Prop :=
  ∀ (n : ℕ) [Fact n.Prime], n ≠ 2 → ∀ (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    ∀ k : ZMod n, k ≠ 0 →
      k.val + (lam * k).val + (lam ^ 2 * k).val = n ∨
        k.val + (lam * k).val + (lam ^ 2 * k).val = 2 * n

/-- F1b. The carry sign is `-1` exactly when the carry sum equals `n`. -/
def CarrySign : Prop :=
  ∀ (n : ℕ) [Fact n.Prime], n ≠ 2 → ∀ (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    ∀ k : ZMod n, k ≠ 0 →
      g lam k = if k.val + (lam * k).val + (lam ^ 2 * k).val = n then -1 else 1

/-- F1c. `J` is even: `J(-k) = J(k)` for every `k`. -/
def JEven : Prop :=
  ∀ (n : ℕ) [Fact n.Prime], n ≠ 2 → ∀ (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    ∀ k : ZMod n, J lam (-k) = J lam k

/-- F1d. `g` is odd on nonzero `k`: `g(-k) = -g(k)`. -/
def GOdd : Prop :=
  ∀ (n : ℕ) [Fact n.Prime], n ≠ 2 → ∀ (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    ∀ k : ZMod n, k ≠ 0 → g lam (-k) = - g lam k

/-- F1e. `g` is invariant under the GLV action `k ↦ lam k`. -/
def GInvariant : Prop :=
  ∀ (n : ℕ) (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    ∀ k : ZMod n, g lam (lam * k) = g lam k

/-- F1f. Orbit product: `J(k) J(lam k) J(lam^2 k) = 1`. -/
def JOrbitProduct : Prop :=
  ∀ (n : ℕ) (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    ∀ k : ZMod n, J lam k * J lam (lam * k) * J lam (lam ^ 2 * k) = 1

/-- F2. Balance identity: with `M` the number of nonzero `k` for which
`sigma(k) = sigma(lam k) = sigma(lam^2 k)`, `3 * sum_{k ≠ 0} J(k) = 4 M - (n - 1)`. -/
def JBalance : Prop :=
  ∀ (n : ℕ) [Fact n.Prime], n ≠ 2 → ∀ (lam : ZMod n), lam ^ 2 + lam + 1 = 0 →
    3 * (∑ k ∈ (univ.erase (0 : ZMod n)), J lam k) =
      4 * (((univ.erase (0 : ZMod n)).filter
              (fun k => sgn k = sgn (lam * k) ∧ sgn (lam * k) = sgn (lam ^ 2 * k))).card : ℤ)
        - ((n : ℤ) - 1)

/-- F3. Public relabelling: if `sigma = c * b` with a `±1`-valued public `c`,
then the predictor `c * P` agrees with `sigma` exactly where `P` agrees with `b`. -/
def Relabel : Prop :=
  ∀ (X : Type) [Fintype X] (sigma c b P : X → ℤ),
    (∀ x, c x = 1 ∨ c x = -1) → (∀ x, sigma x = c x * b x) →
      (univ.filter (fun x => c x * P x = sigma x)).card =
        (univ.filter (fun x => P x = b x)).card

/-- One halving step driven by a parity oracle `O`: `y ↦ (y - O y) / 2` in `ZMod n`. -/
def halvingState {n : ℕ} (O : ZMod n → ℕ) (x : ZMod n) : ℕ → ZMod n
  | 0 => x
  | i + 1 => (halvingState O x i - (O (halvingState O x i) : ZMod n)) * (2 : ZMod n)⁻¹

/-- F4a. Halving recovery in `ZMod n`: with an exact parity oracle, the bits read
at the successive states are the binary digits of `x.val`. -/
def HalvingRecovers : Prop :=
  ∀ (n : ℕ) [Fact n.Prime], n ≠ 2 → ∀ (O : ZMod n → ℕ), (∀ y, O y = y.val % 2) →
    ∀ (x : ZMod n) (L : ℕ), n ≤ 2 ^ L →
      (∑ i ∈ range L, O (halvingState O x i) * 2 ^ i) = x.val

/-- Halving on group elements: `P ↦ h • (P - (O P) • G)`, where `h` is an inverse
of 2 modulo the order `n` of `G`. Only group operations and the oracle are used. -/
def groupHalvingState {A : Type} [AddCommGroup A] (O : A → ℕ) (G : A) (h : ℕ) (Q : A) :
    ℕ → A
  | 0 => Q
  | i + 1 =>
      h • (groupHalvingState O G h Q i - (O (groupHalvingState O G h Q i)) • G)

/-- F4b. Halving recovery in a group: if `G` has odd prime order `n`, `2 h ≡ 1 (mod n)`, and
the oracle returns the parity of the discrete logarithm of every multiple of `G`,
then the bits read along the halving chain recover `x.val` for `Q = x • G`. -/
def GroupHalvingRecovers : Prop :=
  ∀ (A : Type) [AddCommGroup A] (G : A) (n : ℕ) [Fact n.Prime], n ≠ 2 →
    addOrderOf G = n → ∀ (h : ℕ), (2 * h) % n = 1 →
    ∀ (O : A → ℕ), (∀ y : ZMod n, O (y.val • G) = y.val % 2) →
    ∀ (x : ZMod n) (L : ℕ), n ≤ 2 ^ L →
      (∑ i ∈ range L, O (groupHalvingState O G h (x.val • G) i) * 2 ^ i) = x.val

end Ecdlp.ParityFourier
