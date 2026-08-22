import Mathlib
import Ecdlp.Proved.ScalarParity

/-!
# Cross-cycle scalar carry

This file formalizes the arithmetic core of the C56 cross-cycle transport.
For odd scalar multiplier `a` and odd cyclic order `n`, the parity change from
`k` to the canonical residue `(a * k) % n` is exactly controlled by the parity
of the wrap quotient `(a * k) / n`.

The analytic character-sum degree bound remains an external mathematical input
and is not claimed as a kernel theorem here.
-/

namespace Ecdlp.ParityLift

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
