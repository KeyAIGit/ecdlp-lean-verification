import Mathlib
import Ecdlp.Proved.P256Curve

/-!
# NIST P-256 quadratic-twist security certificate

Cross-curve companion of the secp256k1 twist certificate (`TwistSecurity.lean`): the same
`x`-only / point-validation limitation, quantified for NIST P-256.

A single-coordinate (Montgomery-ladder) scalar multiplication cannot tell whether its input
`x` lies on `E` or on the quadratic twist `Ẽ` — both share the `x`-line. An implementation
that skips point validation and receives a twist point computes in `Ẽ(𝔽_p)`, so its security
is the twist's, not the curve's.

For P-256 the number certified below is `2p + 2 − n`. **Honest scope:** interpreting it as
the twist order `#Ẽ = p + 1 + t` rests on `#E(𝔽_p) = n`, which is now proved in
`P256CardinalityExact.lean` (`p256_card_point_eq_n`, with `native_decide` compiler trust). The
twist-order identity `#Ẽ = 2p + 2 − #E` itself is not formalized in this repository; every
theorem below is *unconditional arithmetic about the literal number* `2p + 2 − n`. Its exact factorization is
```
2p + 2 − n = 3 · 5 · 13 · 179 · Q,     Q a 241-bit prime.
```
Two consequences, mirroring secp256k1:

* **The twist is not prime-order.** The cofactor `3 · 5 · 13 · 179 = 34905 ≈ 2¹⁵` is
  nontrivial — genuine small-order subgroups a twist point can be confined to.
* **Twist security is below the curve's.** `2²⁴⁰ < Q < 2²⁴¹`, so generic discrete log in the
  twist's big subgroup costs `≈ √Q ≈ 2¹²⁰`, under the curve's `≈ 2¹²⁸` — reproducing the
  publicly tabulated P-256 twist-security figure (~2^120.3), now machine-checked.

Comparison certified across the two curves of this repo: secp256k1's twist (`≈ 2¹¹⁰`, cofactor
`≈ 2³⁷`) is *weaker* than P-256's (`≈ 2¹²⁰`, cofactor `2¹⁵`) — both below their curves' `2¹²⁸`,
so point validation is mandatory for `x`-only code on either curve. `Q`'s primality is a full
recursive Pratt certificate (`scripts/pratt_certificate.py` machinery, witness `a = 3`,
10 nodes). No new axioms beyond the compiler-trusted `Lean.ofReduceBool` that the
`native_decide` facts already carry.
-/

namespace Ecdlp.P256.TwistPrimality
open Nat

theorem pr_2420633 : Nat.Prime 2420633 := by
  refine lucas_primality 2420633 (3 : ZMod 2420633) (by native_decide) ?_
  intro q hq hqd
  rw [show (2420633 : ℕ) - 1 = 2 ^ 3 * (302579 ^ 1) by native_decide] at hqd
  rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 2 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
  ·
    rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 302579 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide

theorem pr_203333173 : Nat.Prime 203333173 := by
  refine lucas_primality 203333173 (2 : ZMod 203333173) (by native_decide) ?_
  intro q hq hqd
  rw [show (203333173 : ℕ) - 1 = 2 ^ 2 * (3 ^ 1 * (7 ^ 1 * (2420633 ^ 1))) by native_decide] at hqd
  rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 2 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
  ·
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 3 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
    ·
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 7 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
      ·
        rw [(Nat.prime_dvd_prime_iff_eq hq pr_2420633).mp (hq.dvd_of_dvd_pow h)]; native_decide

theorem pr_1387801 : Nat.Prime 1387801 := by
  refine lucas_primality 1387801 (11 : ZMod 1387801) (by native_decide) ?_
  intro q hq hqd
  rw [show (1387801 : ℕ) - 1 = 2 ^ 3 * (3 ^ 3 * (5 ^ 2 * (257 ^ 1))) by native_decide] at hqd
  rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 2 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
  ·
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 3 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
    ·
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 5 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
      ·
        rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 257 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide

theorem pr_13610371 : Nat.Prime 13610371 := by
  refine lucas_primality 13610371 (3 : ZMod 13610371) (by native_decide) ?_
  intro q hq hqd
  rw [show (13610371 : ℕ) - 1 = 2 ^ 1 * (3 ^ 1 * (5 ^ 1 * (17 ^ 1 * (26687 ^ 1)))) by native_decide] at hqd
  rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 2 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
  ·
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 3 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
    ·
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 5 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
      ·
        rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 17 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
        ·
          rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 26687 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide

theorem pr_110244005101 : Nat.Prime 110244005101 := by
  refine lucas_primality 110244005101 (2 : ZMod 110244005101) (by native_decide) ?_
  intro q hq hqd
  rw [show (110244005101 : ℕ) - 1 = 2 ^ 2 * (3 ^ 4 * (5 ^ 2 * (13610371 ^ 1))) by native_decide] at hqd
  rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 2 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
  ·
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 3 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
    ·
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 5 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
      ·
        rw [(Nat.prime_dvd_prime_iff_eq hq pr_13610371).mp (hq.dvd_of_dvd_pow h)]; native_decide

theorem pr_1386428608150177 : Nat.Prime 1386428608150177 := by
  refine lucas_primality 1386428608150177 (5 : ZMod 1386428608150177) (by native_decide) ?_
  intro q hq hqd
  rw [show (1386428608150177 : ℕ) - 1 = 2 ^ 5 * (3 ^ 1 * (131 ^ 1 * (110244005101 ^ 1))) by native_decide] at hqd
  rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 2 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
  ·
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 3 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
    ·
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 131 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
      ·
        rw [(Nat.prime_dvd_prime_iff_eq hq pr_110244005101).mp (hq.dvd_of_dvd_pow h)]; native_decide

theorem pr_124778574733515931 : Nat.Prime 124778574733515931 := by
  refine lucas_primality 124778574733515931 (10 : ZMod 124778574733515931) (by native_decide) ?_
  intro q hq hqd
  rw [show (124778574733515931 : ℕ) - 1 = 2 ^ 1 * (3 ^ 2 * (5 ^ 1 * (1386428608150177 ^ 1))) by native_decide] at hqd
  rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 2 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
  ·
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 3 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
    ·
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 5 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
      ·
        rw [(Nat.prime_dvd_prime_iff_eq hq pr_1386428608150177).mp (hq.dvd_of_dvd_pow h)]; native_decide

theorem pr_718995365596683143 : Nat.Prime 718995365596683143 := by
  refine lucas_primality 718995365596683143 (10 : ZMod 718995365596683143) (by native_decide) ?_
  intro q hq hqd
  rw [show (718995365596683143 : ℕ) - 1 = 2 ^ 1 * (11 ^ 1 * (89 ^ 1 * (127 ^ 2 * (577 ^ 1 * (587 ^ 1 * (67219 ^ 1)))))) by native_decide] at hqd
  rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 2 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
  ·
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 11 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
    ·
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 89 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
      ·
        rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 127 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
        ·
          rcases (Nat.Prime.dvd_mul hq).mp h with h | h
          · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 577 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
          ·
            rcases (Nat.Prime.dvd_mul hq).mp h with h | h
            · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 587 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
            ·
              rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 67219 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide

theorem pr_112600039977335252189018616651067202354555503111433 : Nat.Prime 112600039977335252189018616651067202354555503111433 := by
  refine lucas_primality 112600039977335252189018616651067202354555503111433 (3 : ZMod 112600039977335252189018616651067202354555503111433) (by native_decide) ?_
  intro q hq hqd
  rw [show (112600039977335252189018616651067202354555503111433 : ℕ) - 1 = 2 ^ 3 * (857 ^ 1 * (131909 ^ 1 * (1387801 ^ 1 * (124778574733515931 ^ 1 * (718995365596683143 ^ 1))))) by native_decide] at hqd
  rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 2 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
  ·
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 857 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
    ·
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 131909 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
      ·
        rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · rw [(Nat.prime_dvd_prime_iff_eq hq pr_1387801).mp (hq.dvd_of_dvd_pow h)]; native_decide
        ·
          rcases (Nat.Prime.dvd_mul hq).mp h with h | h
          · rw [(Nat.prime_dvd_prime_iff_eq hq pr_124778574733515931).mp (hq.dvd_of_dvd_pow h)]; native_decide
          ·
            rw [(Nat.prime_dvd_prime_iff_eq hq pr_718995365596683143).mp (hq.dvd_of_dvd_pow h)]; native_decide

theorem pr_3317349640749355357762425066592395746459685764401801118712075735758936647 : Nat.Prime 3317349640749355357762425066592395746459685764401801118712075735758936647 := by
  refine lucas_primality 3317349640749355357762425066592395746459685764401801118712075735758936647 (3 : ZMod 3317349640749355357762425066592395746459685764401801118712075735758936647) (by native_decide) ?_
  intro q hq hqd
  rw [show (3317349640749355357762425066592395746459685764401801118712075735758936647 : ℕ) - 1 = 2 ^ 1 * (3 ^ 1 * (19 ^ 1 * (1861 ^ 1 * (2729 ^ 1 * (250259 ^ 1 * (203333173 ^ 1 * (112600039977335252189018616651067202354555503111433 ^ 1))))))) by native_decide] at hqd
  rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 2 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
  ·
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 3 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
    ·
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 19 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
      ·
        rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 1861 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
        ·
          rcases (Nat.Prime.dvd_mul hq).mp h with h | h
          · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 2729 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
          ·
            rcases (Nat.Prime.dvd_mul hq).mp h with h | h
            · rw [(Nat.prime_dvd_prime_iff_eq hq (show Nat.Prime 250259 by norm_num)).mp (hq.dvd_of_dvd_pow h)]; native_decide
            ·
              rcases (Nat.Prime.dvd_mul hq).mp h with h | h
              · rw [(Nat.prime_dvd_prime_iff_eq hq pr_203333173).mp (hq.dvd_of_dvd_pow h)]; native_decide
              ·
                rw [(Nat.prime_dvd_prime_iff_eq hq pr_112600039977335252189018616651067202354555503111433).mp (hq.dvd_of_dvd_pow h)]; native_decide
end Ecdlp.P256.TwistPrimality

namespace Ecdlp.P256
open Ecdlp.P256.TwistPrimality

/-- The largest prime factor of the P-256 twist order is prime (full Pratt certificate). -/
theorem p256_twist_maxprime_prime :
    Nat.Prime 3317349640749355357762425066592395746459685764401801118712075735758936647 :=
  pr_3317349640749355357762425066592395746459685764401801118712075735758936647

/-- **Exact factorization of `2p + 2 − n` for P-256** (the quadratic-twist order, given
`#E = n`, which is `p256_card_point_eq_n`; the twist-order identity is not formalized — see the
file docstring). Exhibits the
`3 · 5 · 13 · 179 = 34905 ≈ 2¹⁵` cofactor and the 241-bit large prime `Q`. -/
theorem p256_twist_order_factorization :
    2 * p + 2 - n
      = 3 * 5 * 13 * 179 * 3317349640749355357762425066592395746459685764401801118712075735758936647 := by
  native_decide

/-- **NIST P-256 quadratic-twist security profile** (one certificate).
* `2p + 2 − n` (the twist order, under the standard `#E = n`) factors as `3 · 5 · 13 · 179 · Q`;
* `Q` is prime and `2²⁴⁰ < Q < 2²⁴¹` (241-bit ⇒ generic twist-DLP `≈ √Q ≈ 2¹²⁰`, below the
  curve's `2¹²⁸` — the machine-checked form of the publicly tabulated ~2^120.3 figure);
* the cofactor `3 · 5 · 13 · 179 = 34905 > 1` is nontrivial — the twist has small-order
  subgroups, so `x`-only arithmetic on a twist point can be confined.

Honest reading: a *limitation* certificate, the P-256 companion of
`secp256k1_twist_security_profile`. P-256's twist is stronger than secp256k1's (`2¹²⁰` vs
`2¹¹⁰`) but still below the curve; point validation stays mandatory. Says nothing about
non-generic or quantum attacks. -/
theorem p256_twist_security_profile :
    2 * p + 2 - n
        = 3 * 5 * 13 * 179 * 3317349640749355357762425066592395746459685764401801118712075735758936647
      ∧ Nat.Prime 3317349640749355357762425066592395746459685764401801118712075735758936647
      ∧ 2 ^ 240 < 3317349640749355357762425066592395746459685764401801118712075735758936647 ∧ 3317349640749355357762425066592395746459685764401801118712075735758936647 < 2 ^ 241
      ∧ 1 < 3 * 5 * 13 * 179 :=
  ⟨p256_twist_order_factorization, p256_twist_maxprime_prime,
    by native_decide, by native_decide, by native_decide⟩

end Ecdlp.P256
