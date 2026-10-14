# COCYCLE-INTEGRATION-001: from public local EDS ratios to a global phase

Date: 2026-08-11

Status: **isolated theorem-only research line with bounded synthetic
validation**. This note is not canonical ECDLP evidence, targets no unknown
secp256k1 scalar, and claims neither an oracle nor an asymptotic improvement.

## 1. The object in plain language

Let

```text
Q = [k]G
```

in an odd prime-order subgroup. Put

```text
W_G(j) = psi_j(G),
rho_G([j]G) = chi(W_G(j)),
```

where `chi` is the quadratic character. The hidden value `rho_G(Q)` is one
bit.

Lauter and Stange prove that, although `rho_G(Q)` itself is unknown, the
adjacent ratio

```text
delta_G(Q)
  = rho_G(Q+G) * rho_G(Q)
  = chi(W_G(k+1) / W_G(k))
```

is computable from public `G,Q` in polynomial time. Thus the local change of
the hidden bit is public.

The remaining problem is global:

> Can the absolute value at `Q` be reconstructed from these public local
> changes without walking the unknown `k` steps from `G` to `Q`?

This is the exact local-to-global question behind a canonical theta phase lift.

## 2. Exact discrete integration

Because `W_G(1)=1`, one has

```text
rho_G(G)=+1.
```

For `1 <= k < n`,

```text
rho_G([k]G)
  = product_(i=1)^(k-1) delta_G([i]G).                 (1)
```

Equation (1) is an exact algorithm when `k` is known. It is not an ECDLP
algorithm because the path length and endpoint index are precisely the unknown
discrete logarithm.

The elementary theorem package in

```text
Ecdlp/Proved/CocycleIntegration.lean
```

formalizes the abstract content of (1):

1. a base value plus all local edges uniquely determines the path potential;
2. without the base value, potentials with the same edges differ by one global
   additive constant, the gauge ambiguity;
3. closing a path into a cycle forces the total edge integral to vanish.

For sign values, the additive coefficient group is `ZMod 2`.

## 3. The public point function removes all local mystery

Let

```text
u(P) = chi(phi_raw(P)),
c    = chi(phi_raw(G)).
```

Using the raw periodic-point-function normalization,

```text
phi_raw([k]G) = phi_raw(G)^(k^2) W_G(k),
```

and the fact that `k^2` has the same parity as `k`, one obtains

```text
u([k]G) = c^k rho_G([k]G).                            (2)
```

Consequently,

```text
delta_G(Q) = c * u(Q+G) * u(Q).                       (3)
```

Equation (3) says that the public local EDS cocycle is a public coboundary
multiplied by one constant sign.

This yields a complete two-case classification at this level:

```text
c = +1  ->  rho_G(Q) = u(Q), so the EDS residue bit is public;
c = -1  ->  rho_G([k]G) = (-1)^k u([k]G).
```

For the fixed secp256k1 generator, the independently frozen branch replay
records `c=-1`. Therefore the only hidden factor remaining after the public
point function is removed is exactly canonical scalar parity.

This is a reduction of the unknown, not a shortcut.

## 4. Source-normalization audit

Theorem 3.1 of Lauter and Stange defines the ratio-root point function and
prints

```text
phi([k]P) = phi(P)^(k^2-1) W_P(k).
```

Taken literally at `k=1`, the display gives `phi(P)=W_P(1)=1`, which is not
true for the raw ratio-root function in the fixed replays. The surrounding
text describes `alpha^(k^2-1)W(k)` as the normalized perfectly periodic
sequence.

The consistent distinction is:

```text
raw point function:
phi_raw([k]P) = phi_raw(P)^(k^2) W_P(k);

normalized sequence:
phi_raw([k]P) / phi_raw(P)
  = phi_raw(P)^(k^2-1) W_P(k).
```

The paper's adjacent-ratio Proposition 4 is unaffected because the omitted
global factor cancels in the ratio. This note records a source-level
normalization discrepancy; it does not claim an author-confirmed erratum.

Primary source:

```text
K. E. Lauter and K. E. Stange,
The elliptic curve discrete logarithm problem and equivalent hard problems
for elliptic divisibility sequences,
SAC 2008 / LNCS 5381, arXiv:0803.0728v2,
Theorem 3.1 and Proposition 4.
```

## 5. What a canonical theta phase lift must now mean

On secp256k1, a useful phase lift is no longer an unspecified change of
coordinates. It must provide a public, directly evaluable function `L_G`
satisfying

```text
L_G([k]G) = (-1)^k
```

or, equivalently, a public Kummer observable for `rho_G(Q)` which combines with
`u(Q)` through (2).

A local law alone is insufficient. The lift must be a **succinct global
primitive** of the known edge cocycle.

Because the subgroup order `n` is odd, the equation

```text
L_G(Q+G) = -L_G(Q)
```

cannot hold on every edge of the full cycle: after `n` translations it would
change sign while returning to the same point. Canonical parity therefore has
one wrap defect:

```text
ordinary edges:  L_G(Q+G) = -L_G(Q);
wrap edge -G -> O: no sign change.
```

In geometric language the lift needs an explicit branch cut or exceptional
locus. A projective theta vector without a canonical nonprojective
normalization does not supply this information.

## 6. The constructive target

The highest-value positive question is:

```text
SEGMENT-PRIMITIVE-002
```

> Is there a rational, theta, sigma, EDS, p-adic, or other structured circuit
> which evaluates the prefix product in (1) from the endpoints `(G,Q)` in
> sub-square-root online cost, without a table or preprocessing of
> square-root size?

A positive candidate must include:

1. an explicit public map;
2. a canonical branch/gauge normalization;
3. exact treatment of `O`, `-G`, zeros, poles, and extension fields;
4. a proof that its output is `rho_G(Q)` or `(-1)^k`;
5. a full preprocessing, memory, precision, and online-cost theorem;
6. independent replay and formalization of every load-bearing identity.

## 7. The negative target

The corresponding restricted lower-bound problem is:

```text
GENERIC-COCYCLE-INTEGRATION-003
```

> In a generic cyclic-group model augmented only with an oracle for adjacent
> edge labels, prove that evaluating the normalized potential at an arbitrary
> target still requires square-root-scale queries.

The expected mechanism is component connection: local edge queries determine
a potential only inside queried path components; the component containing the
known base value must collide with the component containing the target. This
resembles the collision argument behind generic DLP lower bounds.

No such lower bound is claimed in this branch yet. It would apply only to the
local-cocycle oracle model and would leave open any non-generic algebraic
structure of the concrete EDS point function.

## 8. Bounded validator

Run:

```bash
python3 experiments/parity_lift_000/cocycle_integration_verify.py \
  --out experiments/parity_lift_000/cocycle_integration_results.json
```

The frozen validator checks every odd cycle order from `5` through `127`:

- prefix reconstruction;
- global gauge invariance of local edges;
- cycle closure;
- the single wrap defect of odd-cycle parity;
- impossibility of the constant nontrivial edge as a global odd-cycle
  coboundary;
- removal of a public coboundary leaving the constant secp-like sign factor.

These are finite algebraic checks, not asymptotic evidence.

## 9. Current answer and progress

| obligation | status |
|---|---|
| identify the exact public local EDS ratio | source-backed |
| reduce local ratios to public coboundary times one constant sign | exact derivation |
| formalize path integration, gauge ambiguity, uniqueness, and cycle closure | Lean package added; CI required |
| bounded synthetic replay | complete |
| specify what a theta phase lift must add | complete for this formulation |
| prove a generic cocycle-oracle square-root lower bound | not proved |
| construct a sub-square-root segment primitive | no positive evidence |
| solve secp256k1 ECDLP | not achieved |

Approximate completion measures the stated subproblem, not the probability of
breaking ECDLP:

```text
local-to-global formulation:        about 95%
elementary formal substrate:        about 90% before CI, 100% after green CI
source normalization audit:         about 90%, author confirmation absent
restricted generic lower bound:     about 10%
positive theta/EDS primitive:       0% positive evidence
full ECDLP algorithm:               no demonstrated progress in complexity
```

## 10. Decision

The original phrase "canonical nonprojective theta lift" is now operationally
defined:

> a succinct, publicly evaluable, branch-normalized global primitive of the
> public EDS edge cocycle.

The research should reject candidates that merely reproduce local ratios,
change coordinates, lower polynomial degree, or hide a path walk in
preprocessing. It should prioritize either:

1. a genuine segment primitive with a complete cost theorem; or
2. a square-root lower bound for a precisely defined cocycle-integration
   circuit/oracle class.
