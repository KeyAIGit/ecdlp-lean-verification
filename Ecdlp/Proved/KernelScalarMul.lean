import Mathlib
import Ecdlp.Proved.Secp256k1Curve
import Ecdlp.Proved.KernelPowMod

/-!
# Kernel-evaluable secp256k1 scalar multiplication and its bridge to Mathlib's point group

Mathlib's point group `secp256k1.toAffine.Point` cannot be evaluated by the Lean kernel at
256-bit size: `nsmul` unfolds through `ZMod` arithmetic and inversion goes through
well-founded `Nat.xgcd`. This file gives an affine double-and-add on reduced `ℕ`
coordinates that the kernel evaluates with its built-in big-number arithmetic, and proves
that it computes Mathlib's scalar multiple:

* `invN a = a ^ (p - 2) mod p` (Fermat inverse, via `Ecdlp.Kernel.powMod`);
* `addN` — affine addition on `Option (ℕ × ℕ)` (`none` is `O`), branching with
  `Nat.beq`/`cond`;
* `mulN Q f k` — double-and-add on the low bit of `k`, structural in the fuel `f`;
* `Rep R A` — the `ℕ` point `R` represents the Mathlib point `A`;
* `addN_rep : Rep R A → Rep S B → Rep (addN R S) (A + B)` (every branch of the group law:
  `O`, `P + (-P)`, doubling, distinct `x`);
* `mulN_rep : Rep Q A → k < 2 ^ f → Rep (mulN Q f k) (k • A)`.

The concrete evaluations `mulN G0 256 n = none` and
`mulN G0 256 λ = some (β·Gx mod p, Gy mod p)` are checked by the kernel
(`decide +kernel`, a few seconds each); `GeneratorOrder.lean` transports them to
`n • G = 0` and `glvPoint G = λ • G` on Mathlib's point group. No `native_decide`.
-/

namespace Ecdlp.Kernel

open WeierstrassCurve.Affine Ecdlp.Curve

local notation "𝔽" => ZMod Secp256k1.p

/-- Field inverse by Fermat: `a ^ (p - 2) mod p`. -/
def invN (a : ℕ) : ℕ := powMod Secp256k1.p 256 a (Secp256k1.p - 2)

/-- Affine addition on reduced `ℕ` coordinates; `none` is `O`. Branch tests use
`Nat.beq`/`cond` so that the kernel evaluates them directly. -/
def addN : Option (ℕ × ℕ) → Option (ℕ × ℕ) → Option (ℕ × ℕ)
  | none, q => q
  | some a, none => some a
  | some (x1, y1), some (x2, y2) =>
    bif Nat.beq x1 x2 then
      (bif Nat.beq ((y1 + y2) % Secp256k1.p) 0 then none else
        let l := 3 * x1 * x1 % Secp256k1.p * invN (2 * y1 % Secp256k1.p) % Secp256k1.p
        let x3 := (l * l + 2 * (Secp256k1.p - x1)) % Secp256k1.p
        some (x3, (l * (x1 + (Secp256k1.p - x3)) + (Secp256k1.p - y1)) % Secp256k1.p))
    else
      let l := (y2 + (Secp256k1.p - y1)) * invN ((x2 + (Secp256k1.p - x1)) % Secp256k1.p)
        % Secp256k1.p
      let x3 := (l * l + (Secp256k1.p - x1) + (Secp256k1.p - x2)) % Secp256k1.p
      some (x3, (l * (x1 + (Secp256k1.p - x3)) + (Secp256k1.p - y1)) % Secp256k1.p)

/-- Double-and-add on the low bit, structural in the fuel `f` (bits of `k`). The `let`
shares the recursive result, so the kernel evaluates it once. -/
def mulN (Q : Option (ℕ × ℕ)) : ℕ → ℕ → Option (ℕ × ℕ)
  | 0, _ => none
  | f + 1, k =>
    bif Nat.beq k 0 then none else
    let R := mulN Q f (k / 2)
    let D := addN R R
    bif Nat.beq (k % 2) 0 then D else addN D Q

/-- The secp256k1 base point on reduced `ℕ` coordinates. -/
def G0 : Option (ℕ × ℕ) := some (Secp256k1.Gx % Secp256k1.p, Secp256k1.Gy % Secp256k1.p)

/-- Kernel evaluation: `[n]G = O` on `ℕ` coordinates. -/
theorem mulN_G0_n : mulN G0 256 Secp256k1.n = none := by decide +kernel

/-- Kernel evaluation: `[λ]G = (β·Gx, Gy)` on `ℕ` coordinates. -/
theorem mulN_G0_lam : mulN G0 256 Secp256k1.lam =
    some (Secp256k1.beta * Secp256k1.Gx % Secp256k1.p, Secp256k1.Gy % Secp256k1.p) := by
  decide +kernel

theorem p_gt_two : 2 < Secp256k1.p := by decide +kernel

theorem n_lt_two_pow_256 : Secp256k1.n < 2 ^ 256 := by decide +kernel

theorem lam_lt_two_pow_256 : Secp256k1.lam < 2 ^ 256 := by decide +kernel

theorem cast_sub_p {a : ℕ} (h : a ≤ Secp256k1.p) : ((Secp256k1.p - a : ℕ) : 𝔽) = -(a : 𝔽) := by
  rw [Nat.cast_sub h, ZMod.natCast_self, zero_sub]

theorem cast_inj {a b : ℕ} (ha : a < Secp256k1.p) (hb : b < Secp256k1.p) :
    (a : 𝔽) = (b : 𝔽) ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem negY_eq (x y : 𝔽) : secp256k1.toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, secp256k1]

theorem some_congr {x y x' y' : 𝔽} (h : secp256k1.toAffine.Nonsingular x y) (hx : x = x')
    (hy : y = y') : ∃ h', (Point.some _ _ h : secp256k1.toAffine.Point) = Point.some x' y' h' := by
  subst hx; subst hy; exact ⟨h, rfl⟩

variable [Fact (Nat.Prime Secp256k1.p)]

/-- `invN` computes the field inverse of a nonzero residue. -/
theorem cast_invN {a : ℕ} (ha : (a : 𝔽) ≠ 0) : ((invN a : ℕ) : 𝔽) = (a : 𝔽)⁻¹ := by
  rw [invN, ← zmod_pow_natCast _ (by decide +kernel) 256 a _ (by decide +kernel)]
  have h1 := ZMod.pow_card_sub_one_eq_one ha
  have he : Secp256k1.p - 1 = (Secp256k1.p - 2) + 1 := by decide +kernel
  rw [he, pow_succ] at h1
  exact eq_inv_of_mul_eq_one_left h1

/-- `R` represents the Mathlib point `A`: `none` represents `0`, and `some (x, y)` with
reduced coordinates represents the affine point `(x, y)`. -/
def Rep : Option (ℕ × ℕ) → secp256k1.toAffine.Point → Prop
  | none, A => A = 0
  | some (x, y), A => x < Secp256k1.p ∧ y < Secp256k1.p ∧
      ∃ h : secp256k1.toAffine.Nonsingular (x : 𝔽) (y : 𝔽), A = Point.some _ _ h

/-- **`addN` computes Mathlib's group law** on represented points (all branches). -/
theorem addN_rep {R S : Option (ℕ × ℕ)} {A B : secp256k1.toAffine.Point} (hR : Rep R A)
    (hS : Rep S B) : Rep (addN R S) (A + B) := by
  rcases R with _ | ⟨x1, y1⟩ <;> rcases S with _ | ⟨x2, y2⟩
  · simp only [addN, Rep] at hR hS ⊢; rw [hR, hS, add_zero]
  · simp only [Rep] at hR; simp only [addN]; rw [hR, zero_add]; exact hS
  · simp only [Rep] at hS; simp only [addN]; rw [hS, add_zero]; exact hR
  obtain ⟨hx1, hy1, h1, rfl⟩ := hR
  obtain ⟨hx2, hy2, h2, rfl⟩ := hS
  have hp := p_gt_two
  simp only [addN, Nat.beq_eq, cond_eq_ite]
  by_cases hx : x1 = x2
  · subst hx
    rw [if_pos rfl]
    by_cases hy : (y1 + y2) % Secp256k1.p = 0
    · rw [if_pos hy]
      show _ = 0
      apply Point.add_of_Y_eq rfl
      rw [negY_eq, eq_neg_iff_add_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero hy
    · rw [if_neg hy]
      have hyne : (y1 : 𝔽) ≠ secp256k1.toAffine.negY x1 y2 := by
        rw [negY_eq, Ne, eq_neg_iff_add_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
        exact fun h => hy (Nat.mod_eq_zero_of_dvd h)
      have hyy : (y1 : 𝔽) = y2 := by
        rcases Y_eq_of_X_eq h1.1 h2.1 rfl with h | h
        · exact h
        · exact absurd h hyne
      have hyy' : y1 = y2 := (cast_inj hy1 hy2).mp hyy
      subst hyy'
      rw [Point.add_of_Y_ne hyne]
      have h2y' : (2 * (y1 : 𝔽)) ≠ 0 := by
        intro h0; apply hyne; rw [negY_eq]; linear_combination h0
      have h2y : ((2 * y1 % Secp256k1.p : ℕ) : 𝔽) ≠ 0 := by
        rw [ZMod.natCast_mod, Nat.cast_mul]; push_cast; exact h2y'
      have hS : secp256k1.toAffine.slope x1 x1 y1 y1 = 3 * (x1 : 𝔽) ^ 2 / (2 * y1) := by
        rw [slope_of_Y_ne rfl hyne, negY_eq]; simp only [secp256k1]; ring
      generalize hlN : 3 * x1 * x1 % Secp256k1.p * invN (2 * y1 % Secp256k1.p) % Secp256k1.p
        = lN
      have hL : (lN : 𝔽) = secp256k1.toAffine.slope x1 x1 y1 y1 := by
        rw [← hlN, hS, ZMod.natCast_mod, Nat.cast_mul, cast_invN h2y, ZMod.natCast_mod,
          ZMod.natCast_mod]
        push_cast; rw [div_eq_mul_inv]; ring
      generalize hx3 : (lN * lN + 2 * (Secp256k1.p - x1)) % Secp256k1.p = x3
      have hX : (x3 : 𝔽) =
          secp256k1.toAffine.addX x1 x1 (secp256k1.toAffine.slope x1 x1 y1 y1) := by
        rw [← hx3, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
          cast_sub_p hx1.le, hL]
        simp only [WeierstrassCurve.Affine.addX, secp256k1]; push_cast; ring
      have hx3lt : x3 < Secp256k1.p := hx3 ▸ Nat.mod_lt _ (by omega)
      refine ⟨hx3lt, Nat.mod_lt _ (by omega), ?_⟩
      apply some_congr _ hX.symm
      rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_add, cast_sub_p hx3lt.le,
        cast_sub_p hy1.le, hL, hX]
      simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, negY_eq]
      ring
  · rw [if_neg hx]
    have hxne : (x1 : 𝔽) ≠ x2 := fun h => hx ((cast_inj hx1 hx2).mp h)
    rw [Point.add_of_X_ne hxne]
    have hd : ((x2 + (Secp256k1.p - x1)) % Secp256k1.p : ℕ) = ((x2 : 𝔽) - x1 : 𝔽) := by
      rw [ZMod.natCast_mod, Nat.cast_add, cast_sub_p hx1.le]; ring
    have hd0 : (((x2 + (Secp256k1.p - x1)) % Secp256k1.p : ℕ) : 𝔽) ≠ 0 := by
      rw [hd, sub_ne_zero]; exact fun h => hxne h.symm
    generalize hlN : (y2 + (Secp256k1.p - y1)) * invN ((x2 + (Secp256k1.p - x1)) % Secp256k1.p)
      % Secp256k1.p = lN
    have hL : (lN : 𝔽) = secp256k1.toAffine.slope x1 x2 y1 y2 := by
      rw [← hlN, slope_of_X_ne hxne, ZMod.natCast_mod, Nat.cast_mul, cast_invN hd0, hd,
        Nat.cast_add, cast_sub_p hy1.le, div_eq_mul_inv,
        show (x1 : 𝔽) - x2 = -((x2 : 𝔽) - x1) by ring, inv_neg]
      ring
    generalize hx3 : (lN * lN + (Secp256k1.p - x1) + (Secp256k1.p - x2)) % Secp256k1.p = x3
    have hX : (x3 : 𝔽) =
        secp256k1.toAffine.addX x1 x2 (secp256k1.toAffine.slope x1 x2 y1 y2) := by
      rw [← hx3, ZMod.natCast_mod, Nat.cast_add, Nat.cast_add, Nat.cast_mul, cast_sub_p hx1.le,
        cast_sub_p hx2.le, hL]
      simp only [WeierstrassCurve.Affine.addX, secp256k1]; ring
    have hx3lt : x3 < Secp256k1.p := hx3 ▸ Nat.mod_lt _ (by omega)
    refine ⟨hx3lt, Nat.mod_lt _ (by omega), ?_⟩
    apply some_congr _ hX.symm
    rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_add, cast_sub_p hx3lt.le,
      cast_sub_p hy1.le, hL, hX]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, negY_eq]
    ring

/-- **`mulN` computes Mathlib's scalar multiple** `k • A` whenever `k < 2 ^ f`. -/
theorem mulN_rep {Q : Option (ℕ × ℕ)} {A : secp256k1.toAffine.Point} (hQ : Rep Q A) :
    ∀ (f k : ℕ), k < 2 ^ f → Rep (mulN Q f k) (k • A)
  | 0, k, hk => by
    have : k = 0 := by simpa using hk
    subst this; simp only [mulN, Rep, zero_nsmul]
  | f + 1, k, hk => by
    have ih := mulN_rep hQ f (k / 2) (by rw [Nat.pow_succ] at hk; omega)
    simp only [mulN, Nat.beq_eq, cond_eq_ite]
    by_cases h0 : k = 0
    · subst h0; simp only [if_true, Rep, zero_nsmul]
    rw [if_neg h0]
    have hk2 := Nat.div_add_mod k 2
    by_cases h2 : k % 2 = 0
    · rw [if_pos h2]
      have : k • A = (k / 2) • A + (k / 2) • A := by
        rw [← add_nsmul]; congr 1; omega
      rw [this]; exact addN_rep ih ih
    · rw [if_neg h2]
      have : k • A = ((k / 2) • A + (k / 2) • A) + A := by
        rw [← add_nsmul, ← succ_nsmul]; congr 1; omega
      rw [this]; exact addN_rep (addN_rep ih ih) hQ

end Ecdlp.Kernel
