# POINT_COUNTING_KEYSTONE.md — scoping `#E(𝔽_p) = n`

> **STATUS UPDATE (2026-07-13): CLOSED for secp256k1.** The strong keystone
> `#E(𝔽_p) = n` is **proved** — without Hasse or Schoof — by a curve-specific
> certificate (`Ecdlp/Proved/CurveCardinalityExact.lean`: `n ∣ #E` and
> `#E ≤ 2p+1 < 3n` pin `#E ∈ {n, 2n}`, and `E[2] = {O}` excludes `2n`), and
> the full-group upgrade landed
> (`CurveFullGroup.lean`: `E(𝔽_p) = ⟨G⟩`, cyclic; unconditional GLV `[λ]`).
> This note is kept as the honest scoping/history of the gap. Still open:
> the geometric `E[n] ≅ (ℤ/n)²` (extension-field points) and the **P-256**
> cardinality (the certificate exploits `j = 0`, which P-256 lacks).
>
> **STATUS UPDATE (2026-10-16): CLOSED for P-256.** `p256_card_point_eq_n`
> (`Ecdlp/Proved/P256CardinalityExact.lean`) proves `#E(𝔽_p) = n` for P-256, again
> without Hasse or Schoof. The `j = 0` non-cube step is replaced by a curve-generic
> theorem (`PrimeOrderCardinality.lean`: `#E ≤ 2p+1 < 3n` and no rational 2-torsion)
> and a kernel-checked certificate that `x³ − 3x + b` has no root in `𝔽_p`
> (`CubicNoRootCertificate.lean`). The count inherits `native_decide` trust from
> `n • G = 0` and the Pratt certificates. The route needs cofactor 1; the memo below
> predates it. Prior art: pyca/verified-garbage proves `#E = n` for P-256/P-384/P-521 for
> its own specification curve type, and kernel-checks the same no-root certificates; this
> repository's result is for `Ecdlp.P256.P256` over Mathlib's `WeierstrassCurve`
> (`THIRD_PARTY_NOTICES.md`). The release node `p256-exact-cardinality` stays outside
> `release.required_nodes` by the owner's ruling of 2026-10-22.

## The successor gap (TASK-005 memo, 2026-07-16): geometric `E[n] ≅ (ℤ/n)²`

**Decision.** Of TASK-005's two branches, this memo takes the **geometric torsion
structure** (the Weil-pairing feeder). The **P-256 cardinality stays parked** — its
blocker is unchanged (Hasse, or a P-256-specific certificate that cannot reuse the
`j = 0` trick; see §5 below and `BARRIERS.md`).

**Where the full decomposition lives** (one place per fact — this section only records
the current frontier and the decision): the lemma DAG is
`notes/DIVISION_POLY_TORSION_MAP.md` (nodes N1–N13, critical path
`N5 → N7 → N10 → N11 → N13`), the route comparison is `notes/SEPARABILITY_ROUTES.md`
(Route B, via division polynomials — recommended), and the N5/B1 sub-plan is
`notes/B1_COPRIMALITY_PLAN.md` + `notes/B1_TRACTABILITY_MAP.md`.

**Frontier moved — what is now kernel-verified** (beyond what those maps recorded when
drafted): L1 (`CoprimeCommonRoot.lean`), the L2/L3 eval bridge + descent
(`DivisionPolynomialEvalBridge.lean`, PR #171: `¬IsCoprime(Φₙ,ΨSqₙ)` over `𝔽_p` ⟹ two
*consecutive* scalar-`normEDS` zeros over `𝔽̄_p`), the pairwise degenerate-case
certificates L5/L6/L6b (`CoprimePsi2Psi3/CoprimePsi3PrePsi4/CoprimePsi2PrePsi4.lean`),
N12 (`TorsionCoprime.lean`), the N10(iii) kernel-structure lemma for **prime** `n`
(`TorsionStructure.lean`, PR #170 — exactly the case secp256k1 needs), the N4 monic
half (`secp256k1_Φ_monic`), **and the L4 layer itself**: `normEDS_isEllSequence`
(`NormEDSIsElliptic.lean` — the open Mathlib TODO, ported net-relation proof,
unconditional over any `CommRing`), `normEDS_somos4` (`NormEDSSomos4.lean`), and the
`isEllSequence_of_rec_one` bridge (`EllSequenceRecOne.lean`).

**The smallest missing piece, named.** With L4 landed, the next gap on the critical
path is **no longer missing Mathlib theory** — it is one concrete lemma, the **N5
scalar obligation**:

> for `x₀, β ∈ 𝔽̄_p` with `β² = Ψ₂Sq(x₀)` and `w := normEDS β (Ψ₃(x₀)) (preΨ₄(x₀))`:
> `w(n)` and `w(n+1)` never vanish simultaneously for `n ≥ 1`.

Machine-readable statement: open stem `Ecdlp/Targets/normeds_no_consecutive_zero.lean`
(registry `targets/normeds_no_consecutive_zero.json`). Via the landed descent
(contrapositive of `secp256k1_exists_normEDS_consecutive_eq_zero_of_not_isCoprime`)
it closes **N5** `IsCoprime (Φ n) (ΨSq n)` for secp256k1; N5 feeds the N10 degree
input and N11's counting route, and — with the prime-case N10(iii) already proved —
the assembly N13 gives `#E[n] = n²` and `E[n] ≅ (ℤ/n)²` over `𝔽̄_p`, the
non-degeneracy substrate for the Weil pairing (W5 in `notes/FOUNDATIONS.md`).

**Proof shape (why it is reachable):** anchor `w(1) = 1`; the pairwise certificates
kill the degenerate corner (`β = 0 ⟺ Ψ₂Sq(x₀) = 0` forces `Ψ₃(x₀) ≠ 0` by L5 and
`preΨ₄(x₀) ≠ 0` by L6b; L6 excludes `Ψ₃(x₀) = preΨ₄(x₀) = 0`); a consecutive-zero
pair then propagates to lower indices through `normEDS_somos4` / instances of the
`IsEllSequence` three-term identity, descending to a contradiction with `w(1) = 1`
(strong induction, parity case splits). Pure algebra over an integral domain — no new
geometry, no scheme theory.

**Honest effort estimate.** MID-node, single-file scale (~150–400 lines with case
splits) — days of focused kernel-checked work, not the multi-month grade of N7
(the general multiplication formula, still CORE-by-effort, upstream only as stalled
PR #13782) or Route A separability. Risk: the induction bookkeeping over ℤ-indices
and the parity splits may be tedious; the statement itself is classical EDS
rank-of-apparition rigidity specialized by the coprimality triangle.

**What this does *not* claim:** closing N5 does not by itself give `E[n] ≅ (ℤ/n)²` —
N7 (multiplication formula) remains the big effort item between N5 and the counting
route. The claim is precise: N5-scalar is the *smallest missing piece*, it is
*unblocked now*, and everything before it on the critical path is kernel-verified.

> **UPDATE (2026-07-16, same day):** the sibling draft **PR #172** (head `5f61fa5`,
> unmerged) contains a candidate proof of exactly this scalar statement
> (`NormEDSConsecutiveZeros.lean`), a general-`n` N5 (`DivisionPolynomialCoprime.lean`),
> N7@{2,3,5}, B4@{3,5,7}, closure bridges, and per-ℓ structure theorems
> `E[ℓ](𝔽̄_p) ≅ (ℤ/ℓ)²` for `ℓ ∈ {3,5,7}` — CI-green on its branch but **not yet
> merged, reviewed, or counted**. Until a human merges it, the open stem
> `Ecdlp/Targets/normeds_no_consecutive_zero.lean` remains the on-`main` registry
> target; at merge time the target must be reconciled per the standard lifecycle
> (status → verified, stem consumed). The adversarial audit of #172 lives in
> `notes/reviews/GEOMETRIC_TORSION_AUDIT.md`.
>
> **SUPERSEDED (2026-07-18):** the work was split, reviewed, reconciled, and landed on
> `main` through PRs #179–#186; commit `404c99a` closes the structure family. The paragraph
> above is retained as provenance for the state at the time of the audit, not as current status.

The single arithmetic-geometry fact that the whole "instantiate the crypto at the
*real* secp256k1 group" story hangs on is the curve cardinality

> **`#E(𝔽_p) = n`** — the group of 𝔽_p-rational points of `y² = x³ + 7` has
> **exactly** `n` elements (cofactor `h = 1`), where `n` is the machine-checked prime
> base-point order (`Secp256k1.n`, `Secp256k1PrimeN.lean`).

This note (a) states the keystone precisely and separates a **weak** from a **strong**
form, (b) gives the dependency DAG showing which downstream results it gates, and
(c) gives an honest formalizability assessment at 256 bits — is Schoof/Hasse in
Mathlib, is a *certificate* route more tractable than computing `#E` from scratch,
what is the smallest Lean lemma that unlocks the most, and a concrete next step.

The headline, stated up front so nothing below oversells: **the literal `#E = n`
(cofactor 1) is gated on the Hasse bound, which is not in Mathlib and is a multi-month,
research-grade port.** But a large fraction of what the notes *attribute* to `#E = n`
actually only needs a much weaker, certificate-shaped fact about the base-point
subgroup `⟨G⟩` — and that weaker fact is bounded engineering, gated on one empirical
unknown (whether Mathlib's `Point` arithmetic reduces under `native_decide`), not on
point-counting at all. Getting that distinction right is the main content here.

---

## 1. The keystone, stated precisely — weak vs strong

Two different statements are conflated in `ABSTRACT_SCOPE.md` / `GLV_LAMBDA.md` /
`GlvEigenvalue.lean` under the single banner "point counting". They have *very*
different costs and gate *different* things.

| | **Weak keystone** (subgroup) | **Strong keystone** (whole group) |
|---|---|---|
| Statement | `n • G = 0` for the base point `G` (⇒ `⟨G⟩` is cyclic of order `n`, since `n` prime and `G ≠ 0`) | `#E(𝔽_p) = n`, i.e. `E(𝔽_p) = ⟨G⟩`, cofactor `h = 1` |
| Group it describes | the crypto subgroup `⟨G⟩` (order `n`) | the **entire** rational point group |
| Needs point counting? | **No.** A single scalar-multiplication identity. | **Yes.** Needs the Hasse bound to rule out `h > 1`. |
| What certifies it | a computable `n • G = 0` check (double-and-add) | order-`n` point + Hasse interval + uniqueness (below) |
| Tractability | bounded engineering, one empirical gate | multi-month (Hasse absent from Mathlib) |

The cryptographically load-bearing objects — the ECDLP instance, the Schnorr/Pedersen
protocol algebra, the GLV `[λ]` speed-up — all live **in `⟨G⟩`**, not in the ambient
`E(𝔽_p)`. So the *weak* keystone is what the cryptography actually needs; the *strong*
keystone only upgrades "true on `⟨G⟩`" to "true on all of `E(𝔽_p)`", which is
mathematically satisfying but crypto-inessential. The existing notes bill everything at
the strong-keystone price. That is the overstatement this document corrects.

---

## 2. Why point counting is "the keystone" — the dependency DAG

Three downstream consumers are each said (in the notes named in the task) to be blocked
"behind `#E(𝔽_p) = n`". Here is the DAG, with each consumer split into the part that
truly needs the strong keystone and the part that only needs the weak one.

```
                          ┌──────────────────────────────────────────┐
                          │  STRONG keystone:  #E(𝔽_p) = n  (h = 1)   │
                          │  = E(𝔽_p) = ⟨G⟩ = E[n](𝔽_p)              │
                          └───────────────┬──────────────────────────┘
                                          │ needs
                          ┌───────────────┴───────────────┐
                          │  HASSE BOUND  |#E − (p+1)| ≤ 2√p│  ⟵ NOT in Mathlib
                          └───────────────┬───────────────┘
                                          │  +
        ┌─────────────────────────────────┴───────────────────────────────┐
        │ n | #E  (order-n point ⟨G⟩ + Fintype E(𝔽_p) + Lagrange)          │
        │ + arithmetic:  2n > p+1+2√p  (native_decide)  ⇒ n unique in       │
        │   Hasse interval ⇒ #E = n                                          │
        └───────────────────────────────────────────────────────────────────┘

   ┌─────────────────────────────── WEAK keystone ───────────────────────────────┐
   │  C1:  n • G = 0        (⇒ ⟨G⟩ cyclic, order n)                               │
   │  C2:  glvPoint G = λ • G   (eigenvector at the generator; λ published)       │
   │  both are COORDINATE-LEVEL computable certificates — no cardinality needed   │
   └──────┬───────────────────────────┬───────────────────────────┬──────────────┘
          │                           │                           │
          ▼                           ▼                           ▼
 (b) Module (ℤ/n) on ⟨G⟩     (a) GLV eigenvalue φ = [λ]    (c) protocol algebra
     from C1: ∀P∈⟨G⟩, n•P=0      on ⟨G⟩, from C1 + C2 +        instantiated on ⟨G⟩
     ⇒ ℤ→End factors through     glv_root_mod_n_condition      (Schnorr/Pedersen/…
     ℤ/n  (AddCommGroup.zmod-     (GlvScalarAction.lean,        Module-level theorems
     Module-style)                already proved)               fire on G := ⟨G⟩)
          │                           │                           │
          └───────────── all three ALSO hold on the full E(𝔽_p) ──┘
                         but ONLY after the STRONG keystone
                         (which makes E(𝔽_p) = ⟨G⟩)
```

### The three consumers, precisely

**(a) GLV eigenvalue `glvPoint G = λ · G`.**
`GlvEigenvalue.lean` (`secp256k1_glvHom_eq_zsmul`) proves `φ = [k]` with `k²+k+1 ≡ 0`
*conditional on* `[IsAddCyclic secp256k1.toAffine.Point]` — cyclicity of the **whole**
group, i.e. the strong keystone. `GLV_LAMBDA.md` says the eigenvalue is "blocked behind
`#E = n`" because it needs "(i) `⟨G⟩` has order exactly `n` and `glvPoint` maps `⟨G⟩`
into `⟨G⟩`, which needs (ii) `#E(𝔽_p) = n`."

That attribution is stronger than necessary. `glvPoint G = (β·Gx, Gy)` is a *concrete
point with computable coordinates*. The eigenvector fact `glvPoint G = λ · G` (C2) is a
direct coordinate identity — compute `λ · G` by double-and-add and compare to
`(β·Gx, Gy)` — and it does **not** need the group order. Once you have C1 (`⟨G⟩` cyclic
of order `n`) and C2 (`φ` fixes the generator as a `λ`-eigenvector), the already-proved
`glv_root_mod_n_condition` (`GlvScalarAction.lean`) gives `φ = [λ]` on all of `⟨G⟩`:
C2 makes `φ` preserve `⟨G⟩` (`φ(k·G) = k·(λ·G) = (kλ)·G ∈ ⟨G⟩`), so the restriction
`φ|_{⟨G⟩} : ⟨G⟩ →+ ⟨G⟩` is well-defined and equals `[λ]`. Combined with the
already-proved `glv_lambda_eigenvalue` (`λ²+λ+1 ≡ 0 mod n`), **the full GLV eigenvalue
property on the cryptographic subgroup `⟨G⟩` is reachable without point counting.**
What genuinely needs the strong keystone is only the *whole-group* statement
`φ = [λ] on E(𝔽_p)` — because `φ(G) ∈ ⟨G⟩` for the whole group needs `E[n](𝔽_p) = ⟨G⟩`,
which is cofactor 1.

**(b) `Module (ℤ/n)` structure on the point group.**
`ABSTRACT_SCOPE.md` §3 identifies `Module (ZMod n) (secp256k1.toAffine.Point)` as the
one structural obstacle to firing the Module-level protocol theorems, and says it needs
`n • P = 0` for **every** `P` in the whole group — the strong keystone. But for the
subgroup `G := AddSubgroup.zmultiples secp256k1_G` (which is where the discrete log
actually lives), `n • P = 0 ∀ P ∈ ⟨G⟩` is immediate from C1: `P = k·G ⇒ n·P = k·(n·G) =
0`. So `Module (ZMod n) ⟨G⟩` is built from C1 alone, `AddCommGroup.zmodModule`-style —
**no point counting.** The whole-group `Module (ZMod n) (E(𝔽_p))` needs the strong
keystone; the crypto-relevant subgroup module does not.

**(c) Honest instantiation of the abstract protocol algebra.**
Every Module-level theorem in `DlogCompleteness.lean` / `DlogPrimitives.lean`
(`schnorr_verify`, `dh_agree`, `pedersen_homomorphic`, the `Finset` aggregates, …) is
quantified over `[AddCommGroup G] [Module (ZMod n) G]`. Instantiating them "at the real
secp256k1 group" is exactly consumer (b). Using `G := ⟨G⟩` with the C1-derived module,
they all fire on the prime-order subgroup — which *is* the honest home of these
protocols (Schnorr signs with a nonce in `⟨G⟩`, ECDLP is `Q = m·G` in `⟨G⟩`). The
whole-group instantiation is the strong-keystone version and buys nothing extra
cryptographically (as `ABSTRACT_SCOPE.md` itself argues: instantiation upgrades "true in
any module" to "true in this one module" with no new *security* content).

### Net of the DAG
- **Strong keystone `#E = n`** gates: the whole-group forms of (a), (b), (c), and the
  clean statement "`E(𝔽_p)` is cyclic of order `n`". It is the mathematically complete
  keystone and is genuinely blocked on the Hasse bound.
- **Weak keystone (C1, +C2 for GLV)** gates the `⟨G⟩`-forms of (a), (b), (c) — i.e.
  *everything the cryptography needs* — and is **not** blocked on point counting.

The reason `#E = n` reads as "*the* keystone" in the existing notes is that they always
work with the whole group `secp256k1.toAffine.Point`, never the subgroup `⟨G⟩`. Move to
`⟨G⟩` and the keystone splits, and most of its weight moves off point-counting.

---

## 3. Honest formalizability assessment at 256 bits

### 3.1 Is Schoof / Hasse in Mathlib? — No.

At the pinned toolchain (Lean v4.31.0, Mathlib per `lake-manifest.json`), Mathlib
**has**: Weierstrass curves, the affine/projective/Jacobian group law, division
polynomials (`ψₙ, φₙ, ωₙ`), the Abel–Jacobi map `toClass : E(F) ↪ Pic(F[W])` and the
class-group substrate, `j`-invariants, roots of unity `μₙ`. (See `FOUNDATIONS.md` for
the inventory.)

Mathlib **does not have**, for a general or a concrete curve:
- the **Hasse bound** `|#E(𝔽_q) − (q+1)| ≤ 2√q`;
- the **trace of Frobenius** as a developed invariant with its characteristic-polynomial
  identity `φ² − tφ + q = 0` on the Tate module;
- **Schoof's algorithm** (or any point-counting algorithm), CM point-counting, or the
  Weil conjectures for curves;
- a proven **cardinality** `#E(𝔽_p)` for any concrete curve.

Note what `TraceOfFrobenius.lean` actually does: it takes `#E = n` as a *pinned input*
and `native_decide`s the arithmetic sanity checks `t ≠ 0`, `t ≠ 1`, `t² ≤ 4p` over `ℤ`.
That is **not** a proof of Hasse — it is a numeric check that the *assumed* `n` is
consistent with Hasse. The theorem `t² ≤ 4p` there is about the integers `p` and `n`,
not about the curve's point set. So Hasse is genuinely absent, and every "cardinality"
statement in the tree is conditional on the same missing input.

### 3.2 Why `native_decide` cannot compute `#E` from scratch

`#E(𝔽_p)` is a count over a set of size `≈ 2^256`. You cannot enumerate `𝔽_p`
(`2^256` candidate `x`-values, each a quadratic-residue test) inside a kernel-trusted or
compiler-trusted computation — it is astronomically infeasible, not merely slow. So the
"just `native_decide` it" reflex that closes the coordinate-level facts (`β`, `λ`, `Δ`,
trace, curve membership — all `ZMod p` / `ℤ` scalars) **cannot** reach a cardinality.
This is why the strong keystone is qualitatively different from every `native_decide`
result already in the tree.

### 3.3 The certificate route — and where it actually helps

"Verify a given `n` divides `#E`, or use a Hasse-interval certificate" is **much** more
tractable than computing `#E` from scratch — but *how* much, and *whether it needs
Hasse*, depends on which keystone you are after.

**Weak keystone (C1, C2) — the reachable, crypto-sufficient route.**
Both are single scalar-multiplication identities over `ZMod p`:
- **C1** `n • G = 0` — `G` has order dividing `n`; with `n` prime and `G ≠ 0`
  (`secp256k1_G_ne_zero`), order `= n`.
- **C2** `glvPoint G = λ • G` — compute `λ · G` (λ ≈ 2^128, the published
  `Secp256k1.lam`, or `λ²`) and compare coordinates to `(β·Gx, Gy)`.

Neither needs cardinality, Fintype, or Hasse. Each is a `~128–256`-point-addition
computation. **The pivotal empirical unknown** is whether Mathlib's
`WeierstrassCurve.Affine.Point` arithmetic **reduces under `native_decide`**:
1. The default `AddMonoid.nsmul` is **unary** (`n` sequential additions), so
   `n • G` with `n ≈ 2^256` is infeasible *regardless*. You must supply a
   **double-and-add** function and prove it equals `nsmul` (a clean, bounded induction).
2. Even with fast nsmul, `Point.add` must actually *compute*. The affine addition
   formulas divide by `x₂ − x₁` (field inverse in `ZMod p`, which is computable), but
   the group law's data may route through `Classical`/noncomputable definitions or a
   `Decidable`-branching that does not reduce. **Circumstantial evidence it does not
   reduce:** this repo is aggressive with `native_decide` for every coordinate/scalar
   fact yet **never once** computes a `Point`-level `nsmul` — strongly suggesting
   `Point` arithmetic is not `native_decide`-friendly in this Mathlib version. If so,
   the workaround is to define a **computable affine model** on
   `Option (ZMod p × ZMod p)` with explicit add formulas and prove it agrees with
   Mathlib's `Point.add` (bounded, but real, engineering — a few hundred lines and some
   case bookkeeping).

So the weak keystone is *not blocked on mathematics* — it is blocked on a computable
point-arithmetic layer plus a fast-nsmul lemma. That is bounded, and it is the highest
value-per-unit-effort work available here.

**Strong keystone `#E = n` — the Hasse-interval certificate.**
The right formal route is **not** Schoof (computing `#E mod ℓ` for many small primes and
CRT — a formalization nightmare of division-polynomial arithmetic and modular Frobenius).
It is the **certificate/interval** argument:
1. `n | #E` — exhibit the order-`n` point `G` (weak keystone C1) and apply **Lagrange**
   (`Nat.card ⟨G⟩ ∣ Nat.card E(𝔽_p)`, Mathlib has this) — needs a **`Fintype`/`Finite`
   instance** on `E(𝔽_p)`. Finiteness is elementary (points inject into
   `(𝔽_p × 𝔽_p) ⊔ {O}`, a finite set); whether it is already packaged in Mathlib for
   `WeierstrassCurve.Affine.Point` should be checked, but the *value* of the count is
   not the issue — only that the set is finite, so `Lagrange` applies.
2. **Hasse** `#E ≤ p + 1 + 2√p`.
3. **Uniqueness in the interval** — arithmetic fact `2n > p + 1 + 2√p` (one
   `native_decide` on integers). Since `#E` is a positive multiple of `n` and
   `#E ≤ p+1+2√p < 2n`, the only such multiple is `n` itself, so `#E = n` and `h = 1`.

Step 3 is trivial; step 1 is bounded (order-`n` certificate + finiteness + Lagrange);
**step 2, Hasse, is the entire remaining cost.** The certificate route therefore
**reduces the strong keystone to exactly one reusable theorem — the Hasse bound —**
which is dramatically better than Schoof-from-scratch (Hasse is curve-*generic*:
proving it once yields `#E = n` for secp256k1, `#E = p+1−t` shapes for P-256,
Curve25519, every named curve, given each one's cheap order-point certificate).

### 3.4 What Hasse costs

Hasse is not a stepping-stone below the Weil pairing — it is a comparable-depth
arithmetic-geometry theorem. The standard proofs each need machinery Mathlib lacks:
- **Frobenius-endomorphism / Tate-module** proof: needs the endomorphism ring acting on
  `T_ℓ E`, the characteristic polynomial `φ² − tφ + q`, and the positivity/Cauchy–Schwarz
  argument `|t| ≤ 2√q`. Requires isogeny degree theory and the `ℓ`-adic Tate module — the
  same missing "curve/function-field depth" as the Weil pairing (`FOUNDATIONS.md` B3).
- **Riemann–Roch / zeta-function** proof: needs Riemann–Roch for curves and the
  functional equation — also absent.
- **Manin's elementary proof**: avoids cohomology but still needs a careful theory of the
  endomorphism ring `End(E)` as a lattice with a positive-definite norm form — not
  packaged in Mathlib.

Honest estimate: **Hasse is a multi-month, research-grade Mathlib contribution**, of the
same order as the Weil-pairing summit tracked in `FOUNDATIONS.md`. It is not an overnight
or a single-focused-session target, and it should not be presented as one.

---

## 4. Smallest Lean lemma that unlocks the most

Two answers, at two effort tiers — state both honestly rather than pick the flattering one.

**Reachable tier — the weak keystone certificates.** The smallest reachable lemmas that
unlock the most are:

> **C1.** `n • secp256k1_G = 0`  (⇒ `⟨G⟩` cyclic of order `n`)
> **C2.** `glvPoint secp256k1_G = Secp256k1.lam • secp256k1_G` (or `lam²`)

Together they unlock the **`⟨G⟩`-forms of all three consumers at once**: `Module (ℤ/n)`
on `⟨G⟩` (from C1), `IsAddCyclic ⟨G⟩` (from C1), `φ = [λ]` on `⟨G⟩` (from C1+C2 via the
already-proved `glv_root_mod_n_condition`), and protocol-algebra instantiation on `⟨G⟩`
(from C1's module). This is the crypto-relevant payload of "point counting", and it is
gated only on the computable point-arithmetic layer of §3.3, not on Hasse. **The truly
smallest enabling lemma is the fast-nsmul bridge** `∀ k P, doubleAndAdd k P = k • P`
(plus, if needed, the computable-model equivalence) — because once it exists, C1 and C2
are each one `native_decide`, and both consumers fall out.

**Deep tier — the strong keystone.** The single lemma that unlocks the most in absolute
terms is the **Hasse bound** `|#E(𝔽_p) − (p+1)| ≤ 2√p` as a general Mathlib theorem:
with the (reachable) order-`n` certificate and the trivial interval-uniqueness check it
yields `#E = n` outright, and hence the whole-group forms of every downstream result and
`E(𝔽_p) = ⟨G⟩`. But it is multi-month (§3.4). High leverage, low tractability.

---

## 5. Concrete next-step recommendation

**Do the weak keystone; do not start Hasse.** The honest, non-overstated plan:

1. **First, resolve the one empirical gate (a few hours, high information value).**
   Write a throwaway `example : (2 : ℕ) • secp256k1_G = secp256k1_G + secp256k1_G := by
   native_decide` (and a small `k`, e.g. `3 • G`) and see whether Mathlib's `Point.add`
   reduces under `native_decide` at this toolchain. This one experiment decides the
   entire route:
   - **If it reduces:** proceed to step 2 directly — the certificate route is open.
   - **If it does not:** the first deliverable becomes a **computable affine model**
     `secpAdd : Option (ZMod p × ZMod p) → …` with a proof `Point` ≃ model (bounded, but
     the real cost); then step 2 runs on the model.

2. **Land the fast-scalar-multiplication bridge.** Define double-and-add on the point
   type (or the model) and prove `doubleAndAdd k P = k • P` by induction on the binary
   expansion of `k`. This is the reusable engine both certificates need. Bounded and
   clean; no new mathematics.

3. **Land C1** `n • G = 0` (one `native_decide` via step 2) ⇒ promote
   `IsAddCyclic ⟨G⟩` and `addOrderOf secp256k1_G = n`. This alone discharges the
   `[IsAddCyclic …]`-style hypotheses for the **subgroup** and builds
   `Module (ZMod n) ⟨G⟩`, firing the protocol algebra on `⟨G⟩` — the "honest
   instantiation" that `ABSTRACT_SCOPE.md` names as the worthwhile target, delivered on
   the crypto-relevant group.

4. **Land C2** `glvPoint G = λ • G` (one `native_decide` via step 2) ⇒ with
   `glv_root_mod_n_condition` promote **`φ = [λ] on ⟨G⟩`** — the genuine GLV eigenvalue
   fact that `GLV_LAMBDA.md` currently lists as fully blocked. This is the single most
   satisfying honest win available: it moves GLV from "cube-root endomorphism only" to
   "verified `[λ]`-scalar on the crypto subgroup", with the *strong*-keystone/whole-group
   version explicitly still open.

5. **Explicitly park the strong keystone `#E = n` (Hasse).** Record it as blocked in the
   same tier as the Weil pairing: reduced (via §3.3) to the Hasse bound, which is a
   multi-month arithmetic-geometry port (Frobenius/Tate module or Riemann–Roch), not a
   near-term target. Do **not** take it as a hypothesis and call the whole-group results
   "done" — that would be the dishonesty the notes rightly warn against. The correct
   artifact is a conditional theorem `hasse_bound → #E = n → whole-group results`, with
   `hasse_bound` named as the open input, mirroring how `GlvEigenvalue.lean` already
   isolates `[IsAddCyclic …]`.

**One-line honest verdict.** The literal `#E(𝔽_p) = n` is genuinely multi-month /
blocked, because it needs the Hasse bound and Mathlib has no point-counting or Frobenius
trace. But most of what the notes charge to that keystone only needs the base-point
subgroup facts `n • G = 0` and `glvPoint G = λ • G`, which are bounded, certificate-shaped
`native_decide` computations — reachable now *if* a computable `Point`-arithmetic layer
exists, which is the one thing to test first. Recommend building the weak keystone
(steps 1–4) and formally parking the strong one behind an explicit `hasse_bound`
hypothesis.
