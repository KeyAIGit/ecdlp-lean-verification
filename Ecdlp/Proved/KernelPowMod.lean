import Mathlib

/-!
# Kernel-evaluable modular exponentiation and its transfer to `ZMod`

The Lean kernel cannot evaluate a 256-bit power such as `(3 : ZMod p) ^ (p - 1)` by
unfolding `ZMod`/`Fin` multiplication (it exhausts the recursion depth), but it evaluates
closed `Nat` arithmetic with its built-in big-number (GMP) acceleration. This file provides

* `powMod m n b e` — binary exponentiation `b ^ e % m` for `e < 2 ^ n`, written as a
  `Nat.rec` that branches with `Nat.beq`/`cond`, so `decide +kernel` can evaluate it; and
* bridge lemmas that move a kernel-evaluated `powMod` value into `ZMod m`
  (`zmod_pow_natCast`, `kpow_eq_one`, `kpow_ne_one`, `natCast_ne_one_of_mod`).

The generated Pratt certificates (`scripts/pratt_certificate.py`) use `kpow_eq_one` and
`kpow_ne_one` for their witness-power leaves, and `Ecdlp/Proved/KernelScalarMul.lean` uses
`powMod` for field inversion. Every leaf is then checked by the kernel (`decide +kernel`),
with no `native_decide` and no `Lean.ofReduceBool`.

**Provenance.** `powMod`, `powMod_zero`, `powMod_succ` and `powMod_eq` are reused from
pyca/verified-garbage (`lean/VerifiedGarbage/Proof/Framework/Pratt.lean`, commit
`38c744308fcd4d10fec525d975f6164fe9f8d6fe`), available under Apache-2.0 OR BSD-3-Clause
and used here under Apache-2.0; only the namespace changed. See `THIRD_PARTY_NOTICES.md`.
The `ZMod` bridge lemmas are project-authored.
-/

namespace Ecdlp.Kernel

/-- `b^e % m` for `e < 2^n`, by binary exponentiation. For the kernel, which
evaluates it in every certificate: a `Nat.rec` (structural recursion compiles
to `brecOn`) testing with `Nat.beq` and `cond` (not `Decidable` instances), two
and a half times faster. (pyca/verified-garbage `Pratt.powMod`.) -/
def powMod (m n b e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 1)
    (fun _ ih b e => bif Nat.beq e 0 then 1 else
      bif Nat.beq (e % 2) 0 then ih (b * b % m) (e / 2) else b * ih (b * b % m) (e / 2) % m) n b e

theorem powMod_zero (m b e : Nat) : powMod m 0 b e = 1 := rfl

theorem powMod_succ (m n b e : Nat) : powMod m (n + 1) b e = if e = 0 then 1 else
    if e % 2 = 0 then powMod m n (b * b % m) (e / 2) else b * powMod m n (b * b % m) (e / 2) % m := by
  show (bif Nat.beq e 0 then 1 else bif Nat.beq (e % 2) 0 then powMod m n (b * b % m) (e / 2)
    else b * powMod m n (b * b % m) (e / 2) % m) = _
  simp only [Nat.beq_eq, cond_eq_ite]

/-- Correctness of `powMod`: with enough fuel (`e < 2 ^ n`) it computes `b ^ e % m`. -/
theorem powMod_eq (m : Nat) (hm : 1 < m) (n b e : Nat) (he : e < 2 ^ n) :
    powMod m n b e = b ^ e % m := by
  induction n generalizing b e with
  | zero =>
    have : e = 0 := by simpa using he
    subst this; simp [powMod_zero, Nat.mod_eq_of_lt hm]
  | succ n ih =>
    by_cases h0 : e = 0
    · subst h0; simp [powMod_succ, Nat.mod_eq_of_lt hm]
    have he2 : e / 2 < 2 ^ n := by rw [Nat.pow_succ] at he; omega
    have hsplit : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := by
      rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega
    by_cases h2 : e % 2 = 0
    · simp only [powMod_succ, h0, h2, ite_false, ite_true]
      rw [ih _ _ he2, hsplit, h2, Nat.pow_zero, Nat.mul_one, ← Nat.pow_mod]
    · simp only [powMod_succ, h0, h2, ite_false]
      have h1 : e % 2 = 1 := by omega
      rw [ih _ _ he2, hsplit, h1, Nat.pow_one, ← Nat.pow_mod, Nat.mul_mod_mod, Nat.mul_comm]

/-- A `ZMod m` power of a cast natural number is the cast of the kernel-evaluable
`powMod` value. -/
theorem zmod_pow_natCast (m : Nat) (hm : 1 < m) (n a e : Nat) (he : e < 2 ^ n) :
    ((a : ZMod m)) ^ e = ((powMod m n a e : Nat) : ZMod m) := by
  rw [powMod_eq m hm n a e he, ZMod.natCast_mod, Nat.cast_pow]

/-- `x ^ e = 1` in `ZMod m` from a kernel-decided `powMod m n a e = 1`, where `x = a`. -/
theorem kpow_eq_one {m : Nat} (x : ZMod m) (a n e : Nat) (hx : x = (a : ZMod m)) (hm : 1 < m)
    (he : e < 2 ^ n) (h : powMod m n a e = 1) : x ^ e = 1 := by
  rw [hx, zmod_pow_natCast m hm n a e he, h, Nat.cast_one]

/-- `x ^ e ≠ 1` in `ZMod m` from a kernel-decided `powMod m n a e % m ≠ 1 % m`,
where `x = a`. -/
theorem kpow_ne_one {m : Nat} (x : ZMod m) (a n e : Nat) (hx : x = (a : ZMod m)) (hm : 1 < m)
    (he : e < 2 ^ n) (h : powMod m n a e % m ≠ 1 % m) : x ^ e ≠ 1 := by
  rw [hx, zmod_pow_natCast m hm n a e he]
  intro hk
  exact h ((ZMod.natCast_eq_natCast_iff' _ 1 m).mp (by simpa using hk))

/-- `((k : ℕ) : ZMod m) ≠ 1` from a kernel-decided `k % m ≠ 1 % m`. -/
theorem natCast_ne_one_of_mod (m k : Nat) (h : k % m ≠ 1 % m) : ((k : Nat) : ZMod m) ≠ 1 := by
  intro hk
  exact h ((ZMod.natCast_eq_natCast_iff' k 1 m).mp (by simpa using hk))

end Ecdlp.Kernel
