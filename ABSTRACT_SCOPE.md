# ABSTRACT_SCOPE.md — Honest scope map of the "discrete-log cryptography library"

> Counts here are a snapshot; the single canonical figure is **`STATUS.md`** (generated from `data/stats.json`). If they differ, STATUS.md wins.

> Answers `archive/docs/REVIEW_DOSSIER.md` **Finding 1** ("The 'discrete-log cryptography
> library' is abstract algebra mislabeled as cryptography").

## Canonical accounting

- **311 ledger rows / ~272 distinct kernel-verified results** (39 rows are
  alternate-form / supporting restatements of an already-counted result).
- **0 `sorry`** anywhere in the built (`Ecdlp/`-minus-`Targets/`) tree.
- **No CUSTOM axioms.** Everything depends only on Lean/Mathlib's standard
  trusted core `{propext, Classical.choice, Quot.sound}`. Results discharged by
  `native_decide` **additionally** trust the Lean compiler via the
  `Lean.ofReduceBool` axiom — a *real* extension of the trusted computing base,
  not a logical axiom. This is machine-enforced by the axiom-audit CI gate
  (the generated `Ecdlp/LedgerAxiomAudit.lean` / `ResearchOS/LedgerAxiomAudit.lean`
  + `scripts/check_axioms.py`), which fails the build if
  any other axiom (or a `sorryAx`) appears in a result's transitive dependencies.
- **TASK-025 is a conditional representation theorem, not an ECDLP
  algorithm.** Explicit local nonvanishing conditions reduce the 377 logical
  infinity masks to 129, 69, and 36, while an independent boundary-only
  refinement gives 60. Stronger balanced nonvanishing conditions force the
  empty mask and hence one affine chart, but their symbolic nonzeroness,
  nonemptiness, and genericity are not proved. The result proves no unique
  witness, relation yield or rank, solver improvement, runtime or memory
  reduction, total-cost bound, or secp256k1 discrete-log shortcut.

## 1. Honest framing (one paragraph)

This is a **verified abstract protocol algebra**, not a cryptographic security
proof. Every theorem in the four files audited below is a one-line algebraic
identity stated over an *arbitrary* `[AddCommGroup G] [Module (ZMod n) G]` module
or an *arbitrary* `[Field F]` — never over the concrete secp256k1 point group.
The proofs are correct, reusable, and faithfully capture the *equational* content
of the protocols (an honest Schnorr signature verifies; two transcripts pin down
the witness; Pedersen commitments add). But they encode **no security
definition**: there is no adversary, no random oracle / hash, no probability
space, no negligibility, and no reduction to discrete-log hardness. In
particular "special soundness" here is a *linear-algebra fact* —
`x = (s₁ − s₂)/(c₁ − c₂)` solves a linear system — that holds in **any** field,
including fields where the discrete-log problem is trivial. None of these results
is ever instantiated at the secp256k1 curve group; the only point where the
scalar field is specialized to `ZMod Secp256k1.n` (`secp256k1_schnorr_extract`)
still proves the same field-algebra identity, just with `F := ZMod n` plugged in,
and touches no group element. The right label is *"a verified, reusable
discrete-log protocol algebra"* — valuable verified engineering of textbook
identities, not new cryptography and not a curve-specific security theorem.

## 2. Theorem-by-theorem table

Legend for "abstract structure":
- **Module** = `{G} [AddCommGroup G] {n : ℕ} [Module (ZMod n) G]` (an abstract
  finite abelian group of exponent ∣ n, with `s • g` as scalar multiplication).
- **Field** = `{F} [Field F]` (an abstract field — the scalar field only).
- **Field@n** = the same Field result with `F` specialized to `ZMod Secp256k1.n`
  (still no curve group; just a different scalar field).

| Theorem | File | Abstract structure | What it proves | What it does NOT prove |
|---|---|---|---|---|
| `schnorr_verify` | DlogCompleteness | Module | Honest Schnorr/EdDSA sig verifies: `s•g = R + c•p` when `p=x•g, R=r•g, s=r+c·x`. | Nothing about an adversary/forgery; no hash/Fiat-Shamir; no probability; not at secp256k1. Completeness, not unforgeability. |
| `dh_agree` | DlogCompleteness | Module | Diffie–Hellman agreement: `a•(b•g) = b•(a•g)`. Proof is `mul_comm`. | Not the DH/CDH *assumption*; says nothing about a passive adversary's advantage; pure commutativity. |
| `threshold_schnorr_aggregate` | DlogCompleteness | Module + `Finset` | Aggregate (shared-challenge) Schnorr/MuSig/FROST sum verifies. | No rogue-key resistance, no adversary, no security model; just distributes `∑` over `•`. |
| `feldman_vss_verify` | DlogCompleteness | Module + `Finset` | Feldman VSS share `f(i)•g = ∑ⱼ (iʲ)•(aⱼ•g)`. | No secrecy / binding / soundness against a cheating dealer; an evaluation-vs-commitment identity. |
| `musig_key_aggregate` | DlogCompleteness | Module + `Finset` | MuSig coefficient-weighted key aggregate `∑ aᵢ•Pᵢ = (∑ aᵢ·xᵢ)•g`. | No key-aggregation security; no adversary choosing keys; algebra only. |
| `threshold_elgamal_combine` | DlogCompleteness | Module + `Finset` | Partial-decryption combine `∑ xᵢ•C₁ = (∑ xᵢ)•C₁`. | No threshold-security / robustness; `Finset.sum_smul`. |
| `schnorr_batch_verify` | DlogCompleteness | Module + `Finset` | Per-challenge batch verification equation holds. | No batch-forgery / soundness-error bound; an algebraic regrouping. |
| `adaptor_complete` | DlogCompleteness | Module | Adaptor pre-sig adapts: `((r+c·x)+t)•g = (R+T)+c•P`. | No atomicity / witness-hiding / extraction security; completeness identity. |
| `taproot_tweak_verify` | DlogCompleteness | Module | Taproot key-tweak spend verifies: `s•g = R + c•(P+t•g)`. Proof is `module`. | No BIP-341 security claim; no adversary; tactic-closed linear identity. |
| `elgamal_decrypt` | DlogPrimitives | Module | ElGamal decryption correctness `(m+r•(x•g)) − x•(r•g) = m`. | No IND-CPA / semantic security; correctness only. |
| `pedersen_homomorphic` | DlogPrimitives | Module | Pedersen additivity `Com(a,b)+Com(a',b') = Com(a+a',b+b')`. | No hiding, no binding (binding is a *separate* field lemma, see below); homomorphism only. |
| `elgamal_rerandomize_decrypt` | DlogPrimitives | Module | Re-randomized ciphertext still decrypts to `m`. | No unlinkability / IND-CPA-security claim; correctness. |
| `elgamal_additively_homomorphic` | DlogPrimitives | Module | `Enc(m₁;r₁)+Enc(m₂;r₂) = Enc(m₁+m₂;r₁+r₂)`. | No homomorphic-encryption security; component-wise identity. |
| `pedersen_vector_homomorphic` | DlogPrimitives | Module + `Finset` | Vector-Pedersen additivity over a `Finset`. | No vector-commitment binding / soundness; algebra. |
| `schnorr_extract` | SchnorrSoundness | **Field** | 2-transcript extractor: `x = (s₁−s₂)/(c₁−c₂)` from `sᵢ=r+cᵢ·x`, `c₁≠c₂`. | **Not** a reduction to DL-hardness; no adversary, no extractor-runtime/probability; holds in *any* field, incl. DL-trivial ones. Solving a linear equation. |
| `schnorr_witness_unique` | SchnorrSoundness | Field | The extracted witness is unique. | Uniqueness of a solution to a linear system; no knowledge-soundness machinery. |
| `pedersen_binding_extract` | SchnorrSoundness | Field | A binding collision yields the trapdoor `h=(a'−a)/(b−b')`. | Trapdoor `h = log_G H` is an *uninterpreted field element*; no actual group/DLP; no hardness assumption; no probability. "Binding ⇐ DLP" is *narrated*, not formalized. |
| `adaptor_extract` | SchnorrSoundness | Field | `t = s − s'`. Proof is `ring`. | No adaptor-signature security; subtraction. |
| `blind_unblind` | SchnorrSoundness | Field | `s = s' + α`. Proof is `ring`. | No blindness / one-more-unforgeability; subtraction. |
| `secp256k1_schnorr_extract` | SchnorrSoundness | **Field@n** (`ZMod Secp256k1.n`, needs `[Fact n.Prime]`) | Same extractor, scalar field set to the secp256k1 scalar field. | **Still no curve group.** Specializes `F`, not `G`; no point ever appears; same field algebra; no adversary/probability/security. The only "secp256k1" theorem here, and it is *not* about `E(𝔽_p)`. |
| `okamoto_extract` | DlogAdvanced | Field | Okamoto 2-witness extraction via two `schnorr_extract` calls. | Not a reduction; representation-problem hardness untouched; field algebra. |
| `chaum_pedersen_verify` | DlogAdvanced (`DLEQ` ns) | Module | DLEQ completeness: both `s•g=R₁+c•a` and `s•h=R₂+c•b`. | No DLEQ soundness/zero-knowledge; no adversary; completeness identity. |

**Summary of the column "what it does NOT prove," in one line:** none of these
21 theorems contains an adversary, a hash/random oracle, a probability space, a
security game, or a discrete-log hardness assumption — and none is stated over
`secp256k1.toAffine.Point`. The Field-level "soundness" theorems are linear
algebra true in every field.

## 3. Instantiation feasibility at the real secp256k1 group

**Setup that already exists in the repo.** `Ecdlp/Proved/Secp256k1Curve.lean`
defines `secp256k1 : WeierstrassCurve (ZMod Secp256k1.p)`, proves it is an
`EllipticCurve` / `IsElliptic`, and thereby gives Mathlib's group law on
`G := secp256k1.toAffine.Point`, which carries an `AddCommGroup` instance.
`Ecdlp/Proved/Secp256k1PrimeN.lean` discharges `[Fact (Nat.Prime Secp256k1.n)]`
via a full Pratt certificate. So the curve group object and the primality of the
group order both genuinely exist; what is missing is the bridge that lets the
abstract protocol theorems *fire* on that group.

**The one structural obstacle: `Module (ZMod n) G` is not available.** Every
Completeness/Primitives theorem is quantified over `[Module (ZMod n) G]`. To
instantiate any of them at `G = secp256k1.toAffine.Point` with `n = Secp256k1.n`,
you must supply a `Module (ZMod Secp256k1.n) (secp256k1.toAffine.Point)` instance
— i.e. exhibit the point group as a vector-space-like module over the scalar
*ring* `ZMod n`. Mathlib does **not** provide this for `WeierstrassCurve.Point`.
What Mathlib gives for free is only the `ℤ`-module structure (every
`AddCommGroup` is a `Module ℤ`), with `zsmul`. There is no general theorem
"a finite abelian group whose exponent divides `n` is a `ZMod n`-module," and
`WeierstrassCurve.Point` is not equipped with one. Concretely, the missing facts
are:

1. **Order/exponent fact.** You need `n • P = 0` for every `P`
   (`secp256k1.toAffine.Point` has order `n`, cofactor 1). Mathlib has no proof
   that this Mathlib-defined point group is cyclic of order `n`; establishing the
   group order of `E(𝔽_p)` is itself a substantial theorem (point counting /
   Hasse), absent from Mathlib and absent here. Without `n • P = 0` you cannot
   even *define* the `ZMod n`-action `(a : ZMod n) • P` coherently.
2. **The `ZMod n`-action.** Given `n • P = 0`, the action `ZMod n → End(G)`
   factors `ℤ → End(G)` through `ZMod n`. Building this `Module (ZMod n) G`
   instance from `AddMonoid.zsmul` + the exponent fact is a real (if mechanical)
   Mathlib development — `AddCommGroup.zmodModule`-style — but it *requires* fact
   (1), which is the hard part.

**How hard, concretely?**

- *Instantiating a Field-level theorem* (`schnorr_extract`, `okamoto_extract`,
  `pedersen_binding_extract`, `adaptor_extract`, `blind_unblind`) at the real
  curve is **trivial and already essentially done**: `secp256k1_schnorr_extract`
  shows the pattern — set `F := ZMod Secp256k1.n`, supply `[Fact n.Prime]`
  (we have it), done. But this is *not* an instantiation "at the curve group" —
  it never mentions `E(𝔽_p)`. It instantiates the scalar field, which proves
  nothing new cryptographically. So it is cheap and unilluminating.
- *Instantiating a Module-level theorem* (`schnorr_verify`, `dh_agree`,
  `pedersen_homomorphic`, the `Finset` aggregates, …) at `E(𝔽_p)` is **the real
  task**, and it is blocked on obstacle (1) above: proving
  `#(secp256k1.toAffine.Point) = n` (equivalently `n • P = 0` for all `P`).
  That is a curve-cardinality / torsion result that Mathlib does not have for a
  concrete 256-bit curve and that `native_decide` cannot reach (the group is
  astronomically large; you cannot enumerate it). It would need genuine
  arithmetic-geometry machinery (a verified Schoof-style or
  division-polynomial-based order argument). This is the same class of missing
  fact that blocks the GLV `glvPoint = [λ]` claim (see below) and is the true
  bottleneck — not the protocol algebra itself.

**Is it worth doing?** Two honest answers:

> **Resolved since this analysis was written.** `#E(𝔽_p) = n` is now proved
> curve-specifically (`CurveCardinalityExact.lean`, no Schoof), the protocol suite is
> instantiated at the concrete `⟨G⟩` (`ProtocolInstantiation.lean`), and `glvPoint = [λ]`
> on `⟨G⟩` is proved (`GlvSubgroupEigenvalue.lean`). The reasoning below is the original
> assessment that (correctly) named the curve-order lemma as the keystone; the "next target"
> it identifies has since been achieved.

- **For the protocol theorems specifically: no, low value.** Instantiating, say,
  `schnorr_verify` at `E(𝔽_p)` would not produce a security theorem — it would
  still be the completeness identity `s•g = R + c•p`, now with `•` being curve
  scalar-mul. The cryptographic content (unforgeability, knowledge-soundness
  against an adversary, Fiat–Shamir in the ROM) is *absent at the abstract level
  and would remain absent after instantiation.* You would pay a large
  proof-engineering cost (the group-order theorem) to upgrade "true in any
  module" to "true in this one module," with no new security guarantee. Not worth
  it as a way to make the library "real cryptography."
- **For the curve-cardinality lemma itself: yes, high value — but as its own
  deliverable.** A verified `#E(𝔽_p) = n` (and the resulting
  `Module (ZMod n) (secp256k1.toAffine.Point)` instance) is exactly the missing
  keystone that (a) would let *all* Module-level protocol theorems instantiate at
  once, and (b) is the prerequisite for the genuinely interesting GLV claim
  `glvPoint = [λ]` on `⟨G⟩`. That theorem is reusable, absent from Mathlib, and
  mathematically substantive. The right framing is: *the protocol algebra is
  finished scaffolding; the worthwhile next target is the curve-order / module
  instance, after which instantiation is a one-liner and the GLV eigenvalue fact
  becomes reachable.*

## Cross-reference: the GLV map (Finding 3 context)

The GLV endomorphism is genuinely proved to be an **additive** endomorphism:
`glvPoint_add` (`Ecdlp/Proved/GlvHom.lean`) proves
`glvPoint (P + Q) = glvPoint P + glvPoint Q` over the real curve group
`secp256k1.toAffine.Point`, and it is bundled as
`glvHom : Point →+ Point` (an `AddMonoidHom`). This is a real, delicate
full-branch affine-slope proof and the most substantive new result in the tree.
The eigenvalue identity `glvPoint = [λ]` — that `glvPoint P = λ • P` — is **now proved on all of
`⟨G⟩ = E(𝔽_p)`** (`secp256k1_glvPoint_eq_lam_on_zmultiples`: `glvPoint G = λ • G` at the generator,
propagated by additivity; extended to the whole point group via `grp_eq_top`, since `#E = n` makes
`⟨G⟩ = E(𝔽_p)`). Only the identity on the full *geometric* `n`-torsion `E[n](F̄_p)` remains open
(it needs `E[n] ≅ (ℤ/n)²`, a distinct object from the rational `#E = n`).
