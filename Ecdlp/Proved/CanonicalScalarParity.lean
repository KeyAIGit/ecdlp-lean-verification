import Mathlib.Tactic

/-!
# Canonical scalar parity: representative, carry, and symmetry boundaries

These elementary results concern natural-number representatives modulo an odd
order. They do not construct a scalar decoder and do not establish a lower bound
for unrestricted algorithms. A negation-invariant feature is an explicit
hypothesis, not a property asserted of every public feature.

The positive results specify the exact wrap/carry correction. The negative
results rule out only representative-independent parity, globally alternating
odd-period Boolean labels, and exact decoding through a negation-invariant
feature. No experiment or cryptographic target is used.
-/

namespace Ecdlp.CanonicalScalarParity

/-- Adding an odd order changes the parity of the integer representative. -/
theorem parity_add_odd_order (n k : ℕ) (hn : n % 2 = 1) :
    (k + n) % 2 = 1 - k % 2 := by
  omega

/-- Nonzero canonical representatives paired by negation have opposite parity. -/
theorem canonical_negation_parity (n k : ℕ) (hn : n % 2 = 1)
    (hk0 : 0 < k) (hkn : k < n) :
    (n - k) % 2 = 1 - k % 2 := by
  omega

/-- Before wraparound, canonical successor toggles parity. -/
theorem successor_before_wrap (n k : ℕ) (hk : k + 1 < n) :
    ((k + 1) % n) % 2 = 1 - k % 2 := by
  rw [Nat.mod_eq_of_lt hk]
  omega

/-- At the odd-order boundary, both n-1 and its canonical successor are even. -/
theorem successor_at_wrap (n : ℕ) (hn : n % 2 = 1) :
    (n - 1) % 2 = 0 ∧ (((n - 1) + 1) % n) % 2 = 0 := by
  have hn0 : 0 < n := by omega
  have hs : n - 1 + 1 = n := by omega
  constructor
  · omega
  · simp [hs]

/-- No-carry addition follows ordinary parity addition. -/
theorem modular_add_without_carry (n a b : ℕ) (h : a + b < n) :
    ((a + b) % n) % 2 = (a % 2 + b % 2) % 2 := by
  rw [Nat.mod_eq_of_lt h]
  omega

/-- With exactly one modular carry, odd-order reduction complements parity. -/
theorem modular_add_with_carry (n a b : ℕ) (hn : n % 2 = 1)
    (ha : a < n) (hb : b < n) (hc : n ≤ a + b) :
    ((a + b) % n) % 2 = 1 - (a % 2 + b % 2) % 2 := by
  have hmod : (a + b) % n = a + b - n := by
    calc
      (a + b) % n = ((a + b - n) + n) % n := by congr 1; omega
      _ = (a + b - n) % n := by simp [Nat.add_mod]
      _ = a + b - n := Nat.mod_eq_of_lt (by omega)
  rw [hmod]
  omega

/-- Parity of arbitrary integer representatives does not descend modulo odd n.
This does NOT deny the existence of parity after choosing canonical representatives. -/
theorem parity_not_residue_invariant (n : ℕ) (hn : n % 2 = 1) :
    ¬ (∀ a b : ℕ, a % n = b % n → a % 2 = b % 2) := by
  intro h
  have hbad := h n 0 (by simp)
  omega

/-- Exact decoding cannot factor through a feature that identifies k and n-k.
Only nonzero canonical representatives and exact decoders are in scope. -/
theorem no_negation_invariant_decoder {α : Type*} (n : ℕ)
    (hn : n % 2 = 1) (hn1 : 1 < n) (feature : ℕ → α)
    (hinv : ∀ k : ℕ, 0 < k → k < n → feature (n - k) = feature k) :
    ¬ (∃ decode : α → ℕ, ∀ k : ℕ, 0 < k → k < n →
        decode (feature k) = k % 2) := by
  rintro ⟨decode, hdecode⟩
  have hleft := hdecode 1 (by omega) hn1
  have hright := hdecode (n - 1) (by omega) (by omega)
  rw [hinv 1 (by omega) hn1] at hright
  omega

private theorem alternating_value (f : ℕ → Bool)
    (hstep : ∀ k : ℕ, f (k + 1) = !(f k)) :
    ∀ k : ℕ, f k = if k % 2 = 0 then f 0 else !(f 0) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hstep k, ih]
    by_cases hk : k % 2 = 0
    · have hs : (k + 1) % 2 = 1 := by omega
      simp [hk, hs]
    · have hs : (k + 1) % 2 = 0 := by omega
      simp [hk, hs]

/-- An odd closed cycle admits no Boolean label toggling on every edge.
The canonical-parity wrap edge is therefore a necessary exception, not noise. -/
theorem no_odd_period_alternation (f : ℕ → Bool) (n : ℕ)
    (hn : n % 2 = 1) (hperiod : f n = f 0)
    (hstep : ∀ k : ℕ, f (k + 1) = !(f k)) : False := by
  have hvalue := alternating_value f hstep n
  cases hzero : f 0 <;> simp_all

end Ecdlp.CanonicalScalarParity
