import Mathlib

/-!
# Discrete cocycle integration on a path

This file isolates the elementary algebra behind the `COCYCLE-INTEGRATION-001`
research line.

A local edge observable `δ k` determines the change from a potential value
`s k` to `s (k + 1)`. On a path, the potential is the base value plus the
prefix integral of `δ`. Consequently:

* fixing the base value makes the potential unique;
* without the base value, all potentials differ by one global additive
  constant (the gauge ambiguity);
* if the path closes to a cycle, the total edge integral must vanish.

For `A = ZMod 2`, addition models multiplication of signs in `{+1,-1}`.
These theorems do not construct an ECDLP parity oracle and do not prove a
query-complexity lower bound. They formalize only the exact local-to-global
obligation that any proposed theta/EDS phase lift must discharge.
-/

open scoped BigOperators

namespace Ecdlp.CocycleIntegration

variable {A : Type*} [AddCommGroup A]

/-- Prefix integral of an additive edge observable. -/
def pathIntegral (δ : ℕ → A) : ℕ → A
  | 0 => 0
  | k + 1 => pathIntegral δ k + δ k

@[simp]
theorem pathIntegral_zero (δ : ℕ → A) :
    pathIntegral δ 0 = 0 := rfl

@[simp]
theorem pathIntegral_succ (δ : ℕ → A) (k : ℕ) :
    pathIntegral δ (k + 1) = pathIntegral δ k + δ k := rfl

/-- The recursive prefix integral agrees with the finite sum over the path. -/
theorem pathIntegral_eq_sum_range (δ : ℕ → A) (k : ℕ) :
    pathIntegral δ k = ∑ i in Finset.range k, δ i := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      simp [pathIntegral, ih, Finset.sum_range_succ]

/-- A potential satisfying the local edge equation is its base value plus the
prefix integral of the edge observable. -/
theorem potential_eq_base_add_pathIntegral
    (s δ : ℕ → A)
    (hstep : ∀ k, s (k + 1) = s k + δ k) :
    ∀ k, s k = s 0 + pathIntegral δ k := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        s (k + 1) = s k + δ k := hstep k
        _ = (s 0 + pathIntegral δ k) + δ k := by rw [ih]
        _ = s 0 + pathIntegral δ (k + 1) := by
              simp [add_assoc]

/-- Adding one global constant to a potential preserves every local edge. -/
theorem add_constant_preserves_cocycle
    (s δ : ℕ → A)
    (hstep : ∀ k, s (k + 1) = s k + δ k)
    (c : A) :
    ∀ k, c + s (k + 1) = (c + s k) + δ k := by
  intro k
  rw [hstep k]
  abel

/-- Two potentials with the same local edge data differ by one global constant. -/
theorem potentials_differ_by_constant
    (s t δ : ℕ → A)
    (hs : ∀ k, s (k + 1) = s k + δ k)
    (ht : ∀ k, t (k + 1) = t k + δ k)
    (k : ℕ) :
    s k - t k = s 0 - t 0 := by
  rw [potential_eq_base_add_pathIntegral s δ hs k]
  rw [potential_eq_base_add_pathIntegral t δ ht k]
  abel

/-- Once the base value is fixed, a potential for the local edge data is unique. -/
theorem potential_unique_of_base
    (s t δ : ℕ → A)
    (hs : ∀ k, s (k + 1) = s k + δ k)
    (ht : ∀ k, t (k + 1) = t k + δ k)
    (hbase : s 0 = t 0) :
    s = t := by
  funext k
  rw [potential_eq_base_add_pathIntegral s δ hs k]
  rw [potential_eq_base_add_pathIntegral t δ ht k]
  rw [hbase]

/-- Closing a path to a cycle forces the total edge integral to vanish. -/
theorem cycle_closure
    (s δ : ℕ → A)
    (hstep : ∀ k, s (k + 1) = s k + δ k)
    (n : ℕ)
    (hperiod : s n = s 0) :
    pathIntegral δ n = 0 := by
  have h := potential_eq_base_add_pathIntegral s δ hstep n
  rw [hperiod] at h
  have h' : s 0 + pathIntegral δ n = s 0 + 0 := by
    simpa using h.symm
  exact add_left_cancel h'

end Ecdlp.CocycleIntegration
