import Mathlib
import Ecdlp.Proved.CoprimeCommonRoot
import Ecdlp.Proved.Secp256k1Curve
import Ecdlp.Proved.Secp256k1PrimeP

/-!
# Integral resultants of secp256k1 division polynomials

This file isolates the parts of the general coprimality argument that are available in
Mathlib v4.31.0.  The division polynomials are first defined over `Z`.  Their fixed-size
resultants commute with reduction to `ZMod Secp256k1.p`; a unit resultant then supplies
an explicit Bezout identity, hence `IsCoprime`.

The remaining integral arithmetic assertions are exposed as the propositions
`Secp256k1IntegralResultantBadPrimeSupport` and
`Secp256k1IntegralResultantFormula`.  They are inputs to conditional theorems, not
global assumptions and not theorems claimed by this file.

The file also states the missing arbitrary-index root-to-torsion bridge exactly.  From
one proof of that bridge over an algebraic closure it derives the desired coprimality
theorem for all distinct odd primes.  The derivation itself is unconditional and uses
only polynomial gcds, existence of roots over an algebraically closed field, and the
elementary intersection of coprime torsion subgroups.
-/

namespace Ecdlp.Curve

open Polynomial

/-! ## The exact root-to-torsion frontier -/

/-- Every x-coordinate over an algebraically closed field lifts to a nonsingular point
of an elliptic Weierstrass curve. -/
theorem exists_nonsingular_y
    {K : Type*} [Field K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] (x : K) :
    ∃ y : K, W.toAffine.Nonsingular x y := by
  let q : K[X] :=
    X ^ 2 + C (W.a₁ * x + W.a₃) * X -
      C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  have hdegree : q.degree ≠ 0 := by
    have hq : q.natDegree = 2 := by
      dsimp [q]
      compute_degree!
    have hq0 : q ≠ 0 := by
      intro hzero
      rw [hzero] at hq
      norm_num at hq
    rw [degree_eq_natDegree hq0, hq]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q hdegree
  refine ⟨y, WeierstrassCurve.Affine.equation_iff_nonsingular.mp ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff']
  simpa [q, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, add_mul, add_assoc] using hy

/-- The precise missing Mathlib theorem used by the geometric route.

For every odd index, an affine point is killed by that index exactly when its
x-coordinate is a root of the corresponding univariate division polynomial.  The
`DecidableEq` parameter is only needed by Mathlib's computable affine group law. -/
def OddDivisionPolynomialTorsionBridge
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (x y : K) (hxy : W.toAffine.Nonsingular x y),
      (W.preΨ' r).eval x = 0 ↔
        r • (WeierstrassCurve.Affine.Point.some x y hxy) = 0

/-- The missing root-to-torsion bridge implies coprimality for all distinct odd prime
indices over an algebraically closed field. -/
theorem isCoprime_preΨ'_odd_primes_of_torsion_bridge
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (hbridge : OddDivisionPolynomialTorsionBridge W)
    {m n : ℕ} (hm : Nat.Prime m) (hn : Nat.Prime n)
    (hmOdd : Odd m) (hnOdd : Odd n) (hmn : m ≠ n) :
    IsCoprime (W.preΨ' m) (W.preΨ' n) := by
  by_contra hcoprime
  obtain ⟨x, hmx, hnx⟩ :=
    Ecdlp.DivisionPoly.exists_common_root_of_not_isCoprime
      (RingHom.id K) Function.injective_id hcoprime
  simp only [Polynomial.map_id] at hmx hnx
  obtain ⟨y, hxy⟩ := exists_nonsingular_y W x
  let P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y hxy
  have hmP : m • P = 0 := (hbridge m hmOdd x y hxy).mp hmx
  have hnP : n • P = 0 := (hbridge n hnOdd x y hxy).mp hnx
  have hordm : addOrderOf P ∣ m := addOrderOf_dvd_of_nsmul_eq_zero hmP
  have hordn : addOrderOf P ∣ n := addOrderOf_dvd_of_nsmul_eq_zero hnP
  have hmnCoprime : Nat.Coprime m n := (Nat.coprime_primes hm hn).mpr hmn
  have hordOne : addOrderOf P ∣ 1 := by
    simpa [Nat.Coprime, hmnCoprime] using Nat.dvd_gcd hordm hordn
  have hPzero : P = 0 :=
    AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hordOne)
  exact WeierstrassCurve.Affine.Point.some_ne_zero hxy hPzero

/-- The algebraic-closure bridge descends the coprimality result to the base field. -/
theorem isCoprime_preΨ'_odd_primes_of_algebraicClosure_torsion_bridge
    {F : Type*} [Field F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    [DecidableEq (AlgebraicClosure F)]
    (hbridge : OddDivisionPolynomialTorsionBridge
      (W.map (algebraMap F (AlgebraicClosure F))))
    {m n : ℕ} (hm : Nat.Prime m) (hn : Nat.Prime n)
    (hmOdd : Odd m) (hnOdd : Odd n) (hmn : m ≠ n) :
    IsCoprime (W.preΨ' m) (W.preΨ' n) := by
  rw [← Polynomial.isCoprime_map (p := W.preΨ' m) (q := W.preΨ' n)
    (algebraMap F (AlgebraicClosure F))]
  simpa only [WeierstrassCurve.map_preΨ'] using
    isCoprime_preΨ'_odd_primes_of_torsion_bridge
      (W.map (algebraMap F (AlgebraicClosure F))) hbridge
      hm hn hmOdd hnOdd hmn

/-- The exact missing root-to-torsion proposition specialized to secp256k1 over the
algebraic closure of its base field.  The classical equality decision procedure is only
an implementation parameter for the affine point group. -/
noncomputable def Secp256k1OddDivisionPolynomialTorsionBridge : Prop := by
  letI : DecidableEq (AlgebraicClosure (ZMod Secp256k1.p)) := Classical.decEq _
  exact OddDivisionPolynomialTorsionBridge
      (secp256k1.map (algebraMap (ZMod Secp256k1.p)
        (AlgebraicClosure (ZMod Secp256k1.p))))

/-- The requested secp256k1 theorem, conditional on exactly the missing arbitrary-index
root-to-torsion bridge over the algebraic closure of its base field. -/
theorem secp256k1_isCoprime_preΨ'_odd_primes_of_torsion_bridge
    (hbridge : Secp256k1OddDivisionPolynomialTorsionBridge)
    {m n : ℕ} (hm : Nat.Prime m) (hn : Nat.Prime n)
    (hmOdd : Odd m) (hnOdd : Odd n) (hmn : m ≠ n) :
    IsCoprime (secp256k1.preΨ' m) (secp256k1.preΨ' n) := by
  classical
  -- The secp256k1 field-primality and ellipticity instances are kernel-checked
  -- (`decide +kernel`); this theorem depends on the standard axioms only.
  exact isCoprime_preΨ'_odd_primes_of_algebraicClosure_torsion_bridge
    secp256k1 (by simpa [Secp256k1OddDivisionPolynomialTorsionBridge] using hbridge)
    hm hn hmOdd hnOdd hmn

/-! ## Integral resultant transport -/

/-- The integral short Weierstrass model with coefficients `(0, 0, 0, 0, 7)`. -/
def secp256k1Z : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 7

/-- The exact integral discriminant of the chosen model. -/
theorem secp256k1Z_discriminant : secp256k1Z.Δ = -21168 := by
  norm_num [secp256k1Z, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- An integer has only secp256k1 bad-prime divisors when every natural prime dividing it
is one of `2`, `3`, or `7`. -/
def HasOnlySecp256k1BadPrimeDivisors (z : ℤ) : Prop :=
  ∀ q : ℕ, Nat.Prime q → (q : ℤ) ∣ z → q = 2 ∨ q = 3 ∨ q = 7

/-- Every power of the integral discriminant has prime support contained in `{2,3,7}`. -/
theorem secp256k1Z_discriminant_pow_bad_prime_support (e : ℕ) :
    HasOnlySecp256k1BadPrimeDivisors (secp256k1Z.Δ ^ e) := by
  intro q hq hdiv
  rw [secp256k1Z_discriminant] at hdiv
  have hpow : q ∣ 21168 ^ e := by
    simpa [Int.natAbs_pow] using (Int.natCast_dvd.mp hdiv)
  have hbase : q ∣ 21168 := hq.dvd_of_dvd_pow hpow
  rw [show 21168 = 2 ^ 4 * (3 ^ 3 * 7 ^ 2) by norm_num] at hbase
  rcases hq.dvd_mul.mp hbase with h2 | hrest
  · exact Or.inl <|
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2)
  rcases hq.dvd_mul.mp hrest with h3 | h7
  · exact Or.inr <| Or.inl <|
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h3)
  · exact Or.inr <| Or.inr <|
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp (hq.dvd_of_dvd_pow h7)

/-- Reduction of the integral model modulo the secp256k1 field characteristic. -/
theorem secp256k1Z_map :
    secp256k1Z.map (Int.castRingHom (ZMod Secp256k1.p)) = secp256k1 := by
  rfl

/-- The standard upper bound for the degree of an odd-index division polynomial. -/
def oddDivisionDegree (n : ℕ) : ℕ := (n ^ 2 - 1) / 2

/-- The exponent predicted by the classical coprime-index resultant formula. -/
def divisionResultantExponent (m n : ℕ) : ℕ :=
  ((m ^ 2 - 1) * (n ^ 2 - 1)) / 24

/-- An odd-index division polynomial has degree at most `oddDivisionDegree n` over any
commutative coefficient ring. -/
theorem natDegree_preΨ'_le_odd {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) {n : ℕ} (hodd : Odd n) :
    (W.preΨ' n).natDegree ≤ oddDivisionDegree n := by
  simpa only [oddDivisionDegree, if_neg (Nat.not_even_iff_odd.mpr hodd)] using
    W.natDegree_preΨ'_le n

/-- The fixed degree bound is nonzero for an odd prime index. -/
theorem oddDivisionDegree_ne_zero_of_prime {n : ℕ} (hn : Nat.Prime n)
    (hodd : Odd n) : oddDivisionDegree n ≠ 0 := by
  have hn3 : 3 ≤ n := hn.odd_iff.mp hodd
  have hsquare0 : 9 ≤ n ^ 2 := by nlinarith
  have hsquare : 2 ≤ n ^ 2 - 1 := by omega
  unfold oddDivisionDegree
  omega

/-- A unit fixed-size resultant gives a Bezout identity whenever the supplied sizes
bound the actual polynomial degrees and at least one size is nonzero. -/
theorem isCoprime_of_isUnit_resultant {R : Type*} [CommRing R]
    {f g : R[X]} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hmn : m ≠ 0 ∨ n ≠ 0) (hunit : IsUnit (f.resultant g m n)) :
    IsCoprime f g := by
  obtain ⟨p, q, _hp, _hq, hbez⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hmn
  exact ⟨C (hunit.unit⁻¹).1 * p, C (hunit.unit⁻¹).1 * q, by
    simp only [mul_assoc, ← mul_add, mul_comm p, mul_comm q, hbez,
      ← map_mul, IsUnit.val_inv_mul, map_one]⟩

/-- Fixed-size resultants of the integral division polynomials reduce to the corresponding
fixed-size resultants over the secp256k1 field. -/
theorem secp256k1_resultant_eq_intCast (m n dm dn : ℕ) :
    (secp256k1.preΨ' m).resultant (secp256k1.preΨ' n) dm dn =
      ((secp256k1Z.preΨ' m).resultant (secp256k1Z.preΨ' n) dm dn :
        ZMod Secp256k1.p) := by
  rw [← secp256k1Z_map]
  rw [WeierstrassCurve.map_preΨ', WeierstrassCurve.map_preΨ']
  exact Polynomial.resultant_map_map
    (secp256k1Z.preΨ' m) (secp256k1Z.preΨ' n) dm dn
    (Int.castRingHom (ZMod Secp256k1.p))

/-- A stronger exact version of the missing general arithmetic assertion.  It
deliberately has no instance and no proof attached: consumers must pass a proof
explicitly.

For distinct odd primes `m,n`, the fixed-size integral resultant equals the predicted
power of the integral discriminant. -/
def Secp256k1IntegralResultantFormula : Prop :=
  ∀ {m n : ℕ}, Nat.Prime m → Nat.Prime n → Odd m → Odd n → m ≠ n →
    (secp256k1Z.preΨ' m).resultant (secp256k1Z.preΨ' n)
        (oddDivisionDegree m) (oddDivisionDegree n) =
      secp256k1Z.Δ ^ divisionResultantExponent m n

/-- The exact universal bad-prime-support statement requested for the integral
resultants.  This is a proposition to be supplied explicitly, not a global assumption
or instance. -/
def Secp256k1IntegralResultantBadPrimeSupport : Prop :=
  ∀ {m n : ℕ}, Nat.Prime m → Nat.Prime n → Odd m → Odd n → m ≠ n →
    HasOnlySecp256k1BadPrimeDivisors
      ((secp256k1Z.preΨ' m).resultant (secp256k1Z.preΨ' n)
        (oddDivisionDegree m) (oddDivisionDegree n))

/-- The missing exact formula implies the requested universal bad-prime-support
statement. -/
theorem secp256k1_integral_resultant_bad_prime_support_of_formula
    (hformula : Secp256k1IntegralResultantFormula) :
    Secp256k1IntegralResultantBadPrimeSupport := by
  intro m n hm hn hmOdd hnOdd hmn
  rw [hformula hm hn hmOdd hnOdd hmn]
  exact secp256k1Z_discriminant_pow_bad_prime_support _

/-- Bad-prime support of the integral resultant is sufficient for coprimality after
reduction modulo the secp256k1 characteristic. -/
theorem secp256k1_isCoprime_preΨ'_of_integral_resultant_bad_prime_support
    {m n : ℕ} (hm : Nat.Prime m) (hmOdd : Odd m) (hnOdd : Odd n)
    (hsupport : HasOnlySecp256k1BadPrimeDivisors
      ((secp256k1Z.preΨ' m).resultant (secp256k1Z.preΨ' n)
        (oddDivisionDegree m) (oddDivisionDegree n))) :
    IsCoprime (secp256k1.preΨ' m) (secp256k1.preΨ' n) := by
  apply isCoprime_of_isUnit_resultant
  · exact natDegree_preΨ'_le_odd secp256k1 hmOdd
  · exact natDegree_preΨ'_le_odd secp256k1 hnOdd
  · exact Or.inl (oddDivisionDegree_ne_zero_of_prime hm hmOdd)
  · rw [secp256k1_resultant_eq_intCast, isUnit_iff_ne_zero]
    intro hzero
    have hpdiv : (Secp256k1.p : ℤ) ∣
        (secp256k1Z.preΨ' m).resultant (secp256k1Z.preΨ' n)
          (oddDivisionDegree m) (oddDivisionDegree n) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
    -- The imported primality certificate is kernel-checked (`decide +kernel`).
    have hbad := hsupport Secp256k1.p Ecdlp.Primality.secp256k1_p_prime hpdiv
    norm_num [Secp256k1.p] at hbad

/-- Universal integral bad-prime support implies the requested secp256k1 coprimality
theorem for all distinct odd primes. -/
theorem secp256k1_isCoprime_preΨ'_odd_primes_of_integral_resultant_bad_prime_support
    (hsupport : Secp256k1IntegralResultantBadPrimeSupport)
    {m n : ℕ} (hm : Nat.Prime m) (hn : Nat.Prime n)
    (hmOdd : Odd m) (hnOdd : Odd n) (hmn : m ≠ n) :
    IsCoprime (secp256k1.preΨ' m) (secp256k1.preΨ' n) := by
  exact secp256k1_isCoprime_preΨ'_of_integral_resultant_bad_prime_support
    hm hmOdd hnOdd (hsupport hm hn hmOdd hnOdd hmn)

/-- Assuming exactly the integral resultant formula above, all distinct odd prime-index
division polynomials for secp256k1 are coprime.  Everything after that single hypothesis,
including reduction modulo `p` and extraction of a Bezout identity, is proved here. -/
theorem secp256k1_isCoprime_preΨ'_odd_primes_of_integral_resultant_formula
    (hformula : Secp256k1IntegralResultantFormula)
    {m n : ℕ} (hm : Nat.Prime m) (hn : Nat.Prime n)
    (hmOdd : Odd m) (hnOdd : Odd n) (hmn : m ≠ n) :
    IsCoprime (secp256k1.preΨ' m) (secp256k1.preΨ' n) := by
  exact secp256k1_isCoprime_preΨ'_odd_primes_of_integral_resultant_bad_prime_support
    (secp256k1_integral_resultant_bad_prime_support_of_formula hformula)
    hm hn hmOdd hnOdd hmn

end Ecdlp.Curve
