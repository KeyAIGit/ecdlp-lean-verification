# UORC-056 C56: cross-cycle carry cocycle and endpoint character-degree barrier

Date: 2026-08-22

Status: exact scalar arithmetic, exact secp256k1 quotient certificates, and a conditional analytic lower bound from a published character-sum theorem. No parity oracle, no ECDLP shortcut, and no circuit-size lower bound are claimed.

## 1. Position after C55

C55 isolated the exact doubling-cycle quotient for secp256k1:

\[
M=\operatorname{ord}_n(2)=\frac{n-1}{64},\qquad
L(k)=k^M\pmod n.
\]

The label `L(k)` has 64 possible oriented values, but no public endpoint evaluator for `L(k)` was found. C55 also proved that a decoder depending only on a doubling-cycle label cannot recover scalar parity because every odd-length doubling cycle contains both canonical parities.

C56 therefore needs a transport that crosses doubling cycles, a public within-cycle phase, or a sublinear evaluator for a dynamical norm. This note studies the smallest odd public multipliers and proves a barrier for a broad endpoint grammar.

## 2. Scalar parity carry

Let `n` be odd, let `0 <= k < n`, and write

\[
\sigma_n(k)=(-1)^k.
\]

For a positive odd multiplier `a`, define the parity transport

\[
\tau_a(k)=\frac{\sigma_n([ak]_n)}{\sigma_n(k)}\in\{\pm1\}.
\]

Write

\[
ak=q n+r,\qquad q=\left\lfloor\frac{ak}{n}\right\rfloor,
\qquad r=[ak]_n.
\]

Because `a` and `n` are odd,

\[
r-k=(a-1)k-qn\equiv q\pmod 2.
\]

Hence the transport is exactly the wrap carry:

\[
\boxed{\tau_a(k)=(-1)^{\lfloor ak/n\rfloor}.}
\]

It obeys the exact multiplicative-action cocycle law

\[
\boxed{\tau_{ab}(k)=\tau_a([bk]_n)\tau_b(k)}
\]

for positive odd `a,b`.

This is the first exact C56 reduction: any cross-cycle parity transport for an odd scalar multiplier is not an unspecified sign. It must compute a canonical interval carry.

## 3. Action on the 64 C55 cycle labels

For the C55 label,

\[
L(ak)=a^M L(k)\pmod n.
\]

Thus `a^M` is the induced action of multiplier `a` on the 64-element quotient `F_n^*/<2>`.

The replay certificate gives:

| multiplier `a` | order of `a^M` in the 64-label quotient | consequence |
|---:|---:|---|
| 3 | 32 | crosses doubling cycles but leaves two quotient orbits |
| 5 | 64 | acts transitively on all 64 oriented cycle labels |

Since `<2>` has order `M` and the image of `5` has quotient order 64,

\[
\boxed{\langle 2,5\rangle=\mathbb F_n^*.}
\]

Therefore `a=5` is a complete cross-cycle connector for the C55 quotient. It does not by itself solve within-cycle phase, but it eliminates the possibility that the remaining obstruction is merely disconnected cycle labels.

## 4. Exact carry bias

For odd `a`, the number of canonical nonzero scalars with

\[
\left\lfloor\frac{ak}{n}\right\rfloor=q
\]

is

\[
N_q=\left\lfloor\frac{(q+1)n-1}{a}\right\rfloor-
    \left\lfloor\frac{qn}{a}\right\rfloor,
\qquad 0\le q<a.
\]

Hence the complete nonzero carry sum is

\[
B_a(n)=\sum_{k=1}^{n-1}\tau_a(k)
      =\sum_{q=0}^{a-1}(-1)^q N_q.
\]

For secp256k1:

\[
B_3(n)=\frac{n-1}{3}
=38597363079105398474523661669562635950945854759691634794201721047172720498112,
\]

and

\[
B_5(n)
=23158417847463239084714197001737581570567512855814980876521032628303632298868.
\]

The large nonzero bias is the input to the endpoint degree barrier below.

## 5. Endpoint quadratic-character barrier

Let `E/F_p` be secp256k1, let `H=<G>=E(F_p)` have order `n`, and let `chi` be the quadratic character of `F_p` extended by `chi(0)=0`.

Assume a rational function

\[
f\in\mathbb F_p(E)
\]

is finite and nonzero on every nonidentity point of `H`, satisfies the Kummer non-power hypothesis for the quadratic character, and exactly decodes the carry:

\[
\chi(f([k]G))=\tau_a(k),\qquad 1\le k<n.
\]

Let `d=deg(f)` as a function on `E`. Lemma 5 of Shparlinski and Stange bounds the complete subgroup character sum by

\[
\left|\sum_{P\in H}^{*}\chi(f(P))\right|\le 2d\sqrt p.
\]

The identity point contributes either nothing or one value of absolute size at most one. Therefore

\[
|B_a(n)|-1\le 2d\sqrt p,
\]

so

\[
\boxed{
 d\ge
 \left\lceil\frac{|B_a(n)|-1}{2\sqrt p}\right\rceil.
}
\]

The exact secp256k1 instantiations are:

| multiplier | quotient coverage | exact lower bound on `deg(f)` | bits |
|---:|---:|---:|---:|
| 3 | 32 of 64 labels per orbit | 56713727820156410577229101238628035243 | 126 |
| 5 | all 64 labels transitively | 34028236692093846346337460743176821146 | 125 |

Thus no fixed-degree, polylog-degree, or total-degree `o(sqrt(n))` quadratic-character endpoint expression can compute these exact carries.

For a product grammar

\[
\prod_i\chi(f_i(Q))=\chi\!\left(\prod_i f_i(Q)\right),
\]

the same conclusion applies to the degree of the combined Kummer-primitive product. Splitting the expression into many low-degree character atoms does not evade the bound.

## 6. Stronger bound for exact rational values

Suppose instead that a nonconstant rational function `F in F_p(E)` is regular on all nonidentity subgroup points and takes the exact field values

\[
F([k]G)=\tau_a(k)\in\{+1,-1\}.
\]

Both signs occur for `a=3` and `a=5`. Then `F^2-1` has at least `n-1` distinct zeros. If `D=deg(F)`, its pole degree is at most `2D`, so

\[
\boxed{D\ge\frac{n-1}{2}}
\]

unless `F^2-1` is identically zero. In the latter case the function-field domain identity `(F-1)(F+1)=0` forces `F` to be globally constant, contradicting the occurrence of both signs.

For secp256k1 the exact lower bound is

\[
57896044618658097711785492504343953926418782139537452191302581570759080747168,
\]

a 255-bit degree.

## 7. Relation to EDS transport

Division polynomials satisfy

\[
\Psi_{am}(G)=\Psi_a([m]G)\Psi_m(G)^{a^2}.
\]

For odd `a`, quadratic character therefore gives the exact local EDS edge law

\[
\chi(\Psi_{am}(G))
=\chi(\Psi_a([m]G))\chi(\Psi_m(G)).
\]

This is a real endpoint-computable cocycle for EDS residue. It is not yet a scalar-parity carry. Any proposed low-degree rational bridge from this EDS edge state to `tau_a` falls under the barrier in Section 5.

This separation is important: the known composition law supplies transport, but the missing object is a parity-aligned transport.

## 8. What this closes

This result closes the following C56 subfamilies for exact decoding:

1. Any exact rational-valued carry function of degree below `(n-1)/2`.
2. Any Kummer-primitive quadratic-character endpoint function of degree `o(sqrt(n))`.
3. Any finite product of character atoms whose combined rational degree is below the same bound.
4. The idea that multiplier 5 fails merely because it cannot connect all C55 cycle labels. It connects them transitively.

It does not close:

1. High-degree functions with low arithmetic-circuit complexity.
2. Non-character bounded states, additive-character constructions, or extension-field branch data.
3. A sublinear evaluator for the full doubling-orbit norm.
4. A public within-cycle phase.
5. The half-index Miller residual square-root branch.

Degree and circuit size are not interchangeable. A degree near `2^125` can in principle arise from a short repeated-squaring circuit, so the online cost gate remains open.

## 9. Next admissible C56 test

The next search should be restricted to candidates that can survive the new theorem:

\[
\boxed{\text{high-degree low-circuit carry transport or non-character state}.}
\]

A candidate must provide:

1. A public endpoint circuit for `Q -> tau_5(Q)` or a richer state that determines it.
2. Exact behavior under doubling, halving, negation, GLV, and multiplication by 5.
3. Symbolic circuit cost, not only algebraic degree.
4. Held-out toy-curve validation with frozen formulas.
5. A demonstration that any advice does not encode a table per subgroup point.

The first concrete grammar to audit is the closure of:

- `x(Q), y(Q)` and the C54 tangent-transfer pair,
- `Psi_3(Q), Psi_5(Q)` and low-index Miller quotients,
- GLV transforms and their conjugates,
- repeated Frobenius, squaring, multiplication, and inversion,
- one explicit branch bit only when its public extraction cost is charged.

Candidates whose combined character degree is below the theorem threshold are rejected symbolically without running a statistical screen.

## 10. Replay

Run:

```bash
python3 experiments/uorc056_cross_cycle_carry_c56/validate.py \
  --output artifacts/uorc056_cross_cycle_carry_c56/secp256k1_certificate.json
```

The replay checks:

- 10,000 deterministic random secp256k1 transport and cocycle identities,
- exhaustive identities for 668 odd primes up to 5,000,
- quotient orders 32 and 64 for multipliers 3 and 5,
- exact carry biases,
- exact integer arithmetic for both character-degree lower bounds.

## References

1. I. E. Shparlinski and K. E. Stange, *Character Sums with Division Polynomials*, Canadian Mathematical Bulletin 55 (2012), 850-857, arXiv:0912.5246v4. Lemmas 2, 4, and 5.
2. K. E. Lauter and K. E. Stange, *The Elliptic Curve Discrete Logarithm Problem and Equivalent Hard Problems for Elliptic Divisibility Sequences*, SAC 2008, arXiv:0803.0728v2.
3. `notes/UORC056_CYCLE_LABEL_OPEN_TRANSLATION_C55.md`.
4. `notes/UORC056_DYNAMICAL_NORM_CROSS_CYCLE_C56_CONTRACT.md`.
