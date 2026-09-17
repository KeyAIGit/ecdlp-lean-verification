# GLV C6 relative-phase norm: next-stage handoff

Date: 2026-08-11

Status: `design_only_non_executable`

Route context: `R-GLV-SEMAEV`

This document converts the current bounded result into one exact next question. It does not authorize execution, promote a route, modify the Research Engine, or target a secp256k1 discrete logarithm.

## 1. Position in the wider research map

Three currently separate surfaces must be joined rather than duplicated.

1. Draft PR #356, `research/theta-screen-002`, studies the theta/Kummer/Jacobi direction. Its bounded screen shows that the simple genus-one theta/Kummer coordinate is not an independent GLV quotient mechanism. It still requires an independent Sage replay and an owner disposition.
2. Draft PR #361, this intake, studies exact elimination of relative GLV and sign phases through the full `C6` orbit norm. Its 52-system msolve result is positive but bounded.
3. `ECDLP-LAB-001` is the canonical future execution environment. P00 is complete and P01 is the next engineering phase. Any larger matrix campaign must enter through that lab after its contracts, catalog adapter, validators and safety boundary exist. This intake must not create a parallel runner.

The scientific north star remains the plain single-target problem

\[
Q=[d]G \quad\longmapsto\quad d,
\]

with no leakage, interval promise, auxiliary powers or real-world key material. The current work addresses only one possible relation-generation representation inside a much larger index-calculus cost chain.

## 2. Exact algebraic family

Let

\[
E_b/\mathbb F_p:y^2=x^3+b,
\qquad
H=\langle\phi,-1\rangle\simeq C_6,
\qquad
\phi(x,y)=(\beta x,y).
\]

Choose representatives `R_1,...,R_k` of free `H`-orbits and define

\[
\mathcal F_k=\bigcup_{j=1}^k H\cdot R_j,
\qquad
q(P)=y(P)^2=x(P)^3+b,
\]

\[
f_k(T)=\prod_{j=1}^k\bigl(T-q(R_j)\bigr).
\]

The exact local orbit relation is encoded by the degree-12 polynomial `U3` satisfying

\[
U_{3,b}(x_1^3+b,x_2^3+b,x_3^3+b)
=
\prod_{a,c\in\mathbb Z/3\mathbb Z}
S_{3,b}(x_1,\beta^a x_2,\beta^c x_3).
\]

For an `m`-term decomposition, use a fixed balanced binary relation tree. Every leaf variable `q_i` is constrained by `f_k(q_i)=0`; every internal node with children `a_v,b_v` and parent `c_v` contributes

\[
U_{3,b}(a_v,b_v,c_v)=0;
\]

the root is fixed to `q(Q)` up to the declared sign/orbit convention. Denote the resulting ideal by

\[
J_q^{(m)}(p,k,Q).
\]

Every baseline must encode exactly the same factor-base points, target orbit, relation tree and exceptional-locus policy.

## 3. The one high-quality question

> Does exact elimination of all local `C6` phases through `U3` preserve complete relation semantics and polynomially bounded phase recovery while reducing the growth rate of end-to-end algebraic cost per independently verified relation, as both factor-base orbit count `k` and relation-tree size `m` increase, relative to every faithful Semaev/GLV presentation?

This is stronger than asking whether one polynomial has lower degree or one tiny fixture runs faster.

## 4. Primary quantity

For a presentation `A`, define

\[
W_A(p,k,m,Q)
=
\sum_d \operatorname{nnz}\bigl(M_d(J_A^{(m)})\bigr),
\]

where `M_d` is the F4/Macaulay matrix printed or independently reconstructed at degree `d`.

Let

\[
V_A(p,k,m,Q)
=
\#\{\text{independently verified, nonduplicate relations recovered}\}.
\]

Price phase recovery and validation in explicit operation counters:

\[
P_A=\text{phase-recovery work},
\qquad
D_A=\text{independent validation work}.
\]

The primary end-to-end representation metric is

\[
C_A(p,k,m,Q)
=
\frac{W_A+P_A+D_A}{\max(1,V_A)}.
\]

The paired comparison is

\[
R(p,k,m,Q)
=
\frac{C_q(p,k,m,Q)}
{\min\{C_x,C_y,C_{u\text{-faithful}}\}}.
\]

Secondary metrics are peak matrix nonzeros, F4 rounds, critical pairs, reduced rows, solving degree, wall time, RSS, solution multiplicity, phase collisions, missing relations and spurious relations.

## 5. Staged matrix

Execution must use deterministic, digest-bound toy inputs of at most 32 subgroup bits through `ECDLP-LAB-001`.

### Stage A: exact replay

Reproduce the existing 52 fixtures from their permanent raw logs and input hashes. A new implementation must recover the same exit classification and normalized matrix metrics before extending the matrix.

### Stage B: factor-base scaling

Hold `m=3` fixed and add

```text
k in {5, 6, 8}
```

on at least three admissible `j=0` toy curves and at least three independently derived targets per curve. Compare all four exact presentations.

### Stage C: relation-tree scaling

Use

```text
m in {4, 5}
k in {2, 3, 4, 5}
```

with balanced trees, the same paired curves and targets, and the same four presentations. Later `m` values remain blocked until Stage C is interpretable.

### Stage D: independent solver replication

Any retained matrix advantage must be replayed by a second algebraic solver or an independently implemented Macaulay reducer. A shared parser or shared decisive matrix-generation code does not count as source independence.

## 6. Required controls

- ordinary `x_plain` Semaev presentation;
- `y_c3_quotient` presentation;
- faithful lifted `x,u` presentation with `u=x^3`;
- at least one coefficient/term-count matched null that destroys the orbit identity while retaining approximate syntactic size;
- generic targets outside the exact collision locus and separately labelled collision-locus fixtures;
- free-orbit factor bases and separately labelled exceptional/short-orbit fixtures;
- independent brute-force relation enumeration whenever the toy size permits it.

Field size alone is not the main scaling variable. The decisive variables are `k`, `m`, solution multiplicity, degree, sparsity and phase-recovery branching.

## 7. Preregistered interpretations

### Representation-supported

All exact semantic and recovery checks pass, and on both new scaling axes:

- `q` wins the primary paired metric on at least 80 percent of nonexceptional fixtures;
- the upper 95 percent interval for the median `R` is below `0.75`;
- no two consecutive new rungs show median `R >= 1`;
- phase-recovery branching per relation remains bounded by a polynomial in `m` and `k` on the tested family.

This remains bounded empirical support, not an asymptotic theorem.

### Bounded negative

Any of the following closes the current mechanism at its tested scope:

- missing or spurious relations after independent enumeration;
- nonrecoverable orbit tags outside a preregistered exceptional locus;
- median `R >= 1` on two consecutive new `k` or `m` rungs;
- recovery branches grow exponentially with tree size;
- saturation of exceptional components removes the matrix advantage;
- an independent solver reverses the claimed advantage on the same frozen fixtures.

### Inconclusive or resource exhausted

The budget ends before paired systems reach comparable terminal states, or solver-specific telemetry cannot be normalized. This result must be retained and must not be relabelled as support or falsification.

### Asymptotic-candidate gate

Only after at least three successive new scales on both axes and independent replication may the project fit a descriptive slope. A possible exponent claim requires a separately reviewed mathematical mechanism proving why the observed slope should persist. A regression alone cannot promote the route.

## 8. Longer cost chain

Even a persistent F4 advantage is only one component. A sub-Pollard result would require

\[
C_{\mathrm{relations}}
+C_{\mathrm{phase\ recovery}}
+C_{\mathrm{sparse\ linear\ algebra}}
+C_{\mathrm{target\ decomposition}}
=o(\sqrt n).
\]

The present candidate has no result for the sparse linear system, full-rank relation yield, target decomposition or secp256k1 resource estimate.

## 9. Retention rule

Every positive, negative, inconclusive, resource-exhausted and operational result must be retained with:

- exact source commit and clean/dirty state;
- canonical input and configuration hashes;
- producer and validator dependency hashes;
- raw logs and normalized metrics;
- explicit scope and forbidden interpretations;
- immutable outcome label and reopening condition.

Infrastructure failures are operational evidence, not scientific negatives. They must be preserved separately so that a failed installation is never confused with a failed mathematical mechanism.

## 10. Handoff destination

After P01 and the required catalog/validator phases of `ECDLP-LAB-001` are green, this document should be translated into lab `campaign_config`, `work_unit`, `method_request`, `method_result`, `telemetry`, `validation_receipt` and `analysis_summary` records. It must not write directly to Research Engine outcomes or canonical route decisions.

A later owner-reviewed task may use the retained lab evidence to propose a decision delta. Until then, PR #356 and PR #361 remain complementary bounded research maps: the first narrows the simple theta/Kummer hypothesis, and the second tests exact relative-phase elimination.