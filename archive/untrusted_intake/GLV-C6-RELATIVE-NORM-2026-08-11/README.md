# GLV C6 relative-phase norm intake

Date: 2026-08-11

Status: `untrusted_non_executable_bounded_evidence`

Route context: `R-GLV-SEMAEV`

This directory preserves a toy-only structural candidate, its positive and negative evidence, the complete raw msolve record, and the exact next-stage question. It does not authorize a scientific experiment, promote the route, target a secp256k1 discrete logarithm, or make an asymptotic claim.

## 1. Correction to the original theta direction

On

\[
E_b:y^2=x^3+b,
\]

the coordinate

\[
q(P)=y(P)^2=x(P)^3+b
\]

is invariant under

\[
H=\langle\phi,-1\rangle\simeq C_6,
\qquad
\phi(x,y)=(\beta x,y).
\]

However,

\[
q-b=x^3.
\]

Thus `q` is a translation of the already studied GLV invariant `u=x^3`, not a new independent theta coordinate. The potentially different mechanism is the exact elimination of relative GLV phases before polynomial solving.

## 2. Exact local relations

Set

\[
e_1=y_1+y_2+y_3,
\quad
e_2=y_1y_2+y_1y_3+y_2y_3,
\quad
e_3=y_1y_2y_3.
\]

Define

\[
T_{3,b}=e_2(e_2+9b)^2-27(e_3+b e_1)^2.
\]

For three intersections with a line `y=mx+c`, coefficient comparison gives

\[
e_1=m^3+3c,
\quad
e_2=3c^2,
\quad
e_3=c^3-bm^3,
\]

so `T3=0`.

On the regular branch `D=e_2+9b\ne0`, recover

\[
c=3(e_3+b e_1)/D,
\quad
m^3=e_1-3c,
\quad
x_i=(y_i-c)/m.
\]

On the exceptional branch `D=0`, use

\[
c^2=-3b,
\quad
m^3=e_1-3c.
\]

All 760 tested exceptional zeros were constructively recovered.

## 3. Full C6 orbit polynomial

Define

\[
U_{3,b}(q_1,q_2,q_3)
=
\prod_{\epsilon_2,\epsilon_3\in\{\pm1\}}
T_{3,b}(y_1,\epsilon_2y_2,\epsilon_3y_3),
\qquad q_i=y_i^2.
\]

Exact properties:

- multidegree `(6,6,6)`;
- total degree `12`;
- `183` expanded terms;
- leading coefficient in `q3` equal to `(q1-q2)^6`.

In the ring with `beta^2+beta+1=0`, exact sparse arithmetic verifies

\[
\boxed{
U_{3,b}(x_1^3+b,x_2^3+b,x_3^3+b)
=
\prod_{a,c\in\mathbb Z/3\mathbb Z}
S_{3,b}(x_1,\beta^a x_2,\beta^c x_3).
}
\]

The nine factors represent

\[
C_3^3/\Delta C_3\cong C_3^2.
\]

Both independently constructed sparse sides have SHA-256

```text
4c9975adce8af4f2ef56743a2df2a9b42e20299caa44ce0299cf55c9e142c0f6
```

This presentation differs from the naive independent cube quotient because it existentially combines the relative phases into one exact equation and permits local orbit-tag recovery afterward.

## 4. Exact semantic checks

For points in distinct free `C6` orbits,

\[
U_{3,b}(q(P),q(Q),Z)
=
(q(P)-q(Q))^6
\prod_{h\in C_6}(Z-q(P+hQ)).
\]

The retained checks include:

- 35 toy curve instances for `T3`;
- 42,508 `T3` zeros;
- zero `T3` false positives and false negatives;
- all 760 exceptional zeros constructively recovered;
- 1,760 exact orbit-factorization checks;
- nine recursive x/y/q configurations with zero false and zero missing relations;
- 87 of 87 coordinate relations constructively converted to group relations;
- 6,484 ordered distinct-orbit pairs in the phase-collision screen;
- maximum observed toy local-tag multiplicity equal to 3.

Exact enumeration in the secp256k1 scalar ring gives 42 nonzero local collision ratios, of which 6 are same-orbit cases and 36 are distinct-orbit cases. The uniform random ratio bound below `2^-250.83` is conditional; factor-base uniformity is not proved.

## 5. Optimized F4 result

The frozen 52-system msolve campaign compared four exact presentations of the same bounded relation task:

1. ordinary `x_plain` Semaev;
2. `y_c3_quotient`;
3. direct `q_c6_orbit` with `U3`;
4. faithful lifted `u_faithful_glv` retaining both `x` and `u=x^3`.

Execution identity:

- GitHub Actions run `31537739286`;
- workflow head `ee1c70e8915b24c4b6a71bbf9c65f07ef701b570`;
- msolve `0.10.1`, four threads, `-v 2 -g 1`;
- 52 of 52 systems completed;
- zero timeouts and zero nonzero exits.

For every one of the 11 fixtures with `k>=2`, `q_c6_orbit` used fewer F4 rounds, critical pairs, reduced rows, peak estimated matrix nonzeros and cumulative estimated matrix nonzeros than the best of the other three presentations.

The median peak-nonzero ratio was

\[
0.227,
\]

with range `0.153 .. 0.351`; the median cumulative ratio was `0.258`. This is positive bounded evidence for the representation.

The negative facts are equally important:

- at `k=1`, the dense degree-12 norm paid a real startup penalty;
- the campaign held the relation-tree size fixed;
- no full relation-yield, sparse-global-linear-algebra or target-decomposition cost was measured;
- no asymptotic exponent change was established.

For `p=823,k=4`, the maximum printed matrix data were:

| Presentation | Maximum matrix | Density | Pairs | Rows | Max F4 degree |
|---|---:|---:|---:|---:|---:|
| `q_c6_orbit` | 625 x 621 | 0.992% | 575 | 1,156 | 13 |
| `y_c3_quotient` | 847 x 837 | 2.064% | 1,566 | 3,136 | 14 |
| `x_plain` | 1,124 x 1,992 | 5.078% | 2,489 | 4,982 | 19 |
| `u_faithful_glv` | 4,760 x 6,041 | 3.208% | 5,547 | 11,165 | 12 |

The faithful lifted system reached lower maximum degree than the q-system while being substantially more expensive. Degree alone is therefore not a valid representation-quality metric.

## 6. Permanent evidence

The complete evidence no longer depends on the expiring GitHub Actions artifact. The branch permanently contains

```text
msolve_52/
  README.md
  RESULTS_RAW.md
  combined_summary.json
  combined_summary.csv
  glv-msolve-all-52.zip
  raw_shards.tar.gz
  provenance.json
  SHA256SUMS
```

The byte-identical Actions ZIP has SHA-256

```text
051d132852b739aa7f814af9f54c2c09a65e105b4a82d1007bf9cdac5bfc3e63
```

Positive, negative and inconclusive scientific findings must be retained. Operational failures are retained separately and must not be mislabeled as mathematical negatives.

## 7. Current exact question

Let `J_q^(m)(p,k,Q)` be the balanced relation-tree ideal built from `U3`, factor-base equations `f_k(q_i)=0`, and root target `q(Q)`.

The live question is:

> Does exact elimination of all local `C6` phases through `U3` preserve complete relation semantics and polynomially bounded phase recovery while reducing the growth rate of end-to-end algebraic cost per independently verified relation as both factor-base orbit count `k` and relation-tree size `m` grow, relative to every faithful Semaev/GLV presentation?

The primary cost must include cumulative F4 matrix work, phase recovery, independent validation and verified relation yield, not only wall time or final degree.

The precise staged matrix, controls, outcome thresholds, death criteria and integration boundary are frozen in:

- `NEXT_STAGE_HANDOFF.md`;
- `next_stage_handoff.json`.

## 8. Integration boundary

This intake is complementary to draft PR #356, not a replacement for it. PR #356 narrows the simple theta/Kummer/Jacobi mechanism. This intake tests exact relative-phase elimination.

Future campaigns must use `ECDLP-LAB-001` after its contract, catalog and validator phases are green. They must not create a separate runner or write directly to Research Engine outcomes.

## 9. Allowed interpretation

The current evidence supports only:

> An exact `C6` relative-phase norm presentation exists, preserves the tested toy relation semantics, supports constructive local recovery, and produced consistently smaller optimized F4 matrix work than three faithful baselines for all tested `k>=2` fixtures.

It does not support a secp256k1 break, a sub-Pollard algorithm, a polynomial-time ECDLP algorithm, a changed asymptotic exponent, route promotion or established global novelty.

## 10. Reproduction

Structural checks:

```bash
python relative_phase_norm_identity.py
python phase_collision_ratios.py
```

The complete msolve execution, normalized data and raw logs are retained under `msolve_52/`.