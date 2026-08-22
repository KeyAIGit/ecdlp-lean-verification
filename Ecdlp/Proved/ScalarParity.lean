import Mathlib
import Ecdlp.Proved.EdsResidueBalance

/-!
# Generator-relative scalar parity foundations

This file formalizes the arithmetic core of `PARITY-LIFT-000` independently of
any concrete curve or discrete-log target.

For an odd cyclic order `n`, the canonical representative parity is
anti-invariant under negation, cannot factor through a representation that
identifies a generator with its inverse, cannot arise from a globally
alternating nonzero observable around the odd cycle, and recursively determines
the whole canonical scalar by exact bit peeling.
-/

namespace Ecdlp.ParityLift

/-- Least-significant bit of a canonical nonnegative scalar representative. -/
def scalarParity (k : ℕ) : ℕ := k % 2

@[simp] theorem scalarParity_zero : scalarParity 0 = 0 := by
  simp [scalarParity]

@[simp] theorem scalarParity_one : scalarParity 1 = 1 := by
  simp [scalarParity]

/-- Canonical scalar parity is always a bit. -/
theorem scalarParity_lt_two (k : ℕ) : scalarParity k < 2 := by
  exact Nat.mod_lt _ (by omega)

/-- **Negation complement.** In an odd-order cyclic group, the canonical scalar
for the inverse of a nonzero scalar `k` is `n-k`, whose parity is the complement
of the parity of `k`. -/
theorem scalarParity_neg {n k : ℕ}
    (hnOdd : n % 2 = 1) (hkPos : 0 < k) (hkLt : k < n) :
    scalarParity (n - k) = 1 - scalarParity k := by
  unfold scalarParity
  omega

/-- **Kummer-factorization obstruction.** Any representation that identifies
canonical scalars `1` and `n-1` (the generator and its inverse) cannot support a
decoder for scalar parity on all canonical representatives of an odd order.

This is the abstract arithmetic witness used for x-only, Kummer, even-theta,
and other sign-erasing representations. -/
theorem scalarParity_not_factor_through_Kummer
    {X : Type*} {n : ℕ} (hn : 2 < n) (hnOdd : n % 2 = 1)
    (π : ℕ → X) (hCollapse : π 1 = π (n - 1)) :
    ¬ ∃ decode : X → ℕ,
        ∀ k, k < n → decode (π k) = scalarParity k := by
  rintro ⟨decode, hdecode⟩
  have hOne : decode (π 1) = scalarParity 1 := hdecode 1 (by omega)
  have hNegOne : decode (π (n - 1)) = scalarParity (n - 1) :=
    hdecode (n - 1) (by omega)
  have hEq : scalarParity 1 = scalarParity (n - 1) := by
    calc
      scalarParity 1 = decode (π 1) := hOne.symm
      _ = decode (π (n - 1)) := congrArg decode hCollapse
      _ = scalarParity (n - 1) := hNegOne
  unfold scalarParity at hEq
  omega

/-- **Odd-cycle alternation obstruction.** A nonzero integer-valued observable
cannot change sign at every translation step and also be periodic with odd
period `n`. This is the elementary obstruction to treating canonical parity as
an order-two group character. -/
theorem no_global_alternating_translation_observable
    {n : ℕ} (hnOdd : n % 2 = 1)
    (F : ℕ → ℤ)
    (hStep : ∀ k, F (k + 1) = -F k)
    (hPeriod : F n = F 0)
    (hNonzero : F 0 ≠ 0) : False := by
  have hTwo : ∀ k, F (k + 2) = F k := by
    intro k
    calc
      F (k + 2) = F ((k + 1) + 1) := by congr 1 <;> omega
      _ = -F (k + 1) := hStep (k + 1)
      _ = -(-F k) := by rw [hStep k]
      _ = F k := by ring
  have hEven : ∀ m, F (2 * m) = F 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          F (2 * Nat.succ m) = F (2 * m + 2) := by congr 1 <;> omega
          _ = F (2 * m) := hTwo (2 * m)
          _ = F 0 := ih
  let m := n / 2
  have hnSplit : n = 2 * m + 1 := by
    dsimp [m]
    omega
  have hNeg : F n = -F 0 := by
    calc
      F n = F (2 * m + 1) := by rw [hnSplit]
      _ = -F (2 * m) := hStep (2 * m)
      _ = -F 0 := by rw [hEven m]
  have hZero : F 0 = 0 := by omega
  exact hNonzero hZero

/-- One exact parity-oracle peel step on canonical natural representatives. -/
def parityPeel (k : ℕ) : ℕ := (k - scalarParity k) / 2

/-- Removing the least-significant bit and dividing by two strictly decreases a
positive canonical scalar. -/
theorem parityPeel_lt {k : ℕ} (hk : 0 < k) : parityPeel k < k := by
  unfold parityPeel scalarParity
  omega

/-- One parity bit plus the recursively peeled scalar reconstructs the input. -/
theorem parity_reconstruct_step (k : ℕ) :
    scalarParity k + 2 * parityPeel k = k := by
  unfold parityPeel scalarParity
  omega

/-- The sequence of exact parity-oracle answers obtained by repeated peeling. -/
def parityTrace : (k : ℕ) → List ℕ
  | 0 => []
  | k + 1 => scalarParity (k + 1) :: parityTrace (parityPeel (k + 1))
termination_by k => k
decreasing_by
  apply parityPeel_lt
  omega

/-- Decode a little-endian list of binary digits. -/
def bitsValue : List ℕ → ℕ
  | [] => 0
  | b :: bs => b + 2 * bitsValue bs

/-- **Exact parity recovers the full scalar.** Repeated exact parity queries,
with the canonical scalar halved after each answer, reconstruct every natural
scalar. In a cyclic group of odd order this is the arithmetic core of the
standard adaptive parity-oracle reduction. -/
theorem parityOracle_recovers_dlog (k : ℕ) :
    bitsValue (parityTrace k) = k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero => simp [parityTrace, bitsValue]
      | succ k =>
          rw [parityTrace]
          simp only [bitsValue]
          rw [ih (parityPeel (k + 1)) (parityPeel_lt (by omega))]
          exact parity_reconstruct_step (k + 1)

/-- Parity of the canonical wrap quotient produced by multiplying `k` by `a`
modulo `n`. -/
def scalarCarry (a k n : ℕ) : ℕ := (a * k / n) % 2

/-- The scalar carry is a bit. -/
theorem scalarCarry_lt_two (a k n : ℕ) : scalarCarry a k n < 2 := by
  exact Nat.mod_lt _ (by omega)

/-- For odd `a` and odd `n`, output parity XOR wrap-carry equals input parity.
Equivalently, the parity transport under multiplication by `a` is the sign
`(-1)^((a*k)/n)`. -/
theorem scalarParity_odd_mul_mod_add_carry
    {a k n : ℕ} (haOdd : a % 2 = 1) (hnOdd : n % 2 = 1) :
    (scalarParity ((a * k) % n) + scalarCarry a k n) % 2 = scalarParity k := by
  have hDecomp := Nat.mod_add_div (a * k) n
  have hMod := congrArg (fun z : ℕ => z % 2) hDecomp
  simpa [scalarParity, scalarCarry, Nat.add_mod, Nat.mul_mod, haOdd, hnOdd] using hMod

end Ecdlp.ParityLift
