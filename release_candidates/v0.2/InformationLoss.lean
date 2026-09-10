import Init

/-!
Release v0.2 proof candidates. This file has NOT been compiled in the preparation
session. It is outside Ecdlp.lean and both canonical ledgers. Only the successful
Lean invocation plus the exact axiom audit may provide machine-verification evidence.

These are elementary information-loss and measurement lemmas, not ECDLP algorithms.
No theorem here formalizes the analytic character-sum estimate for cycle labels.
-/

namespace Ecdlp.ReleaseV02

/-- A feature collision between different labels precludes an exact decoder. -/
theorem noExactDecoderOfCollision {X S Y : Type}
    (feature : X → S) (label : X → Y) (x y : X)
    (same : feature x = feature y) (different : label x ≠ label y) :
    ¬ ∃ decoder : S → Y, ∀ z, decoder (feature z) = label z :=
  fun ⟨decoder, correct⟩ =>
    different ((correct x).symm.trans ((congrArg decoder same).trans (correct y)))

/-- The number of correct predictions on one binary observation. -/
def hit (prediction label : Bool) : Nat := if prediction = label then 1 else 0

/-- One identical prediction on two complementary labels has exactly one hit. -/
theorem complementaryPair (prediction label : Bool) :
    hit prediction label + hit prediction (!label) = 1 := by
  cases prediction <;> cases label <;> rfl

/-- A finite sample represented explicitly by equally weighted opposite-label pairs. -/
def pairedHits : List (Bool × Bool) → Nat
  | [] => 0
  | (prediction, label) :: rest =>
      hit prediction label + hit prediction (!label) + pairedHits rest

/-- Exactly half the observations are correct, for any finite list of such pairs. -/
theorem pairedHits_eq_length (pairs : List (Bool × Bool)) :
    pairedHits pairs = pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      cases pair with
      | mk prediction label =>
          change hit prediction label + hit prediction (!label) + pairedHits rest =
            rest.length + 1
          rw [complementaryPair, ih, Nat.add_comm]

/-- A local mask action, defined here to keep the candidate independent of Mathlib. -/
def bxor : Bool → Bool → Bool
  | false, b => b
  | true, b => !b

/-- Changing both endpoints affects an edge only where the masks differ. -/
theorem maskedEdgeIdentity (a b u v : Bool) :
    bxor (bxor (bxor a u) (bxor b v)) (bxor a b) = bxor u v := by
  cases a <;> cases b <;> cases u <;> cases v <;> rfl

/-- A positive counterpart: exact transition rules and an anchor determine a path.
This is a uniqueness theorem, not an efficient evaluator of a hidden scalar bit. -/
theorem anchoredSequenceUnique (f g : Nat → Bool)
    (anchor : f 0 = g 0)
    (stepF : ∀ k, f (k + 1) = !(f k))
    (stepG : ∀ k, g (k + 1) = !(g k)) : ∀ k, f k = g k := by
  intro k
  induction k with
  | zero => exact anchor
  | succ k ih =>
      calc
        f (k + 1) = !(f k) := stepF k
        _ = !(g k) := congrArg (fun b : Bool => !b) ih
        _ = g (k + 1) := (stepG k).symm

/-- The numerical order parameter only. Primality and ord_n(2) are not proved here. -/
def orderParameter : Nat :=
  115792089237316195423570985008687907852837564279074904382605163141518161494337

/-- Cross-multiplied rational envelope for a separately stated analytic bound.
This arithmetic inequality alone is NOT a parity-prediction lower/upper bound. -/
theorem rationalEnvelope :
    17 * 179 * 2^128 * 10^36 < 9 * (orderParameter - 1) := by
  decide

end Ecdlp.ReleaseV02

#print axioms Ecdlp.ReleaseV02.noExactDecoderOfCollision
#print axioms Ecdlp.ReleaseV02.complementaryPair
#print axioms Ecdlp.ReleaseV02.pairedHits_eq_length
#print axioms Ecdlp.ReleaseV02.maskedEdgeIdentity
#print axioms Ecdlp.ReleaseV02.anchoredSequenceUnique
#print axioms Ecdlp.ReleaseV02.rationalEnvelope
