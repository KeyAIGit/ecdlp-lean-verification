# msolve 52-system bounded structural result

Date: 2026-08-11

Status: **untrusted, non-executable bounded evidence**

This note does not alter the ECDLP decision substrate, execution queue, route disposition, or experiment authorization. It targets no secp256k1 discrete-log instance.

## Frozen execution

- GitHub Actions run: `31537739286`
- Workflow head: `ee1c70e8915b24c4b6a71bbf9c65f07ef701b570`
- msolve: `0.10.1`, four threads, DRL/F4, `-v 2 -g 1`
- Frozen input archive SHA-256: `6e96df7baa54536d868bcb7894e047e49a2e737471563e2e22cf27b9607cd5c0`
- Combined artifact id: `9119474335`
- Combined artifact SHA-256: `051d132852b739aa7f814af9f54c2c09a65e105b4a82d1007bf9cdac5bfc3e63`
- Systems completed: `52 / 52`
- Timeouts: `0`
- Nonzero exits: `0`

The 52 inputs compare four presentations of the same bounded three-point relation task:

1. ordinary x-coordinate Semaev chain;
2. y-coordinate quotient by the GLV `C3` action;
3. direct full-`C6` orbit coordinate `q = y^2 = x^3+b` with the relative-phase norm `U3`;
4. faithful lifted `x,u` system with `u=x^3`.

## Primary result

For all `11 / 11` configurations with at least two full free `C6` factor-base orbits (`k >= 2`), the direct `q_c6_orbit` system had fewer:

- F4 rounds;
- reduced critical pairs;
- reduced rows;
- estimated nonzero entries in the largest printed F4 round;
- estimated nonzero entries summed over all printed F4 rounds

than the best of the other three tested presentations.

Across those eleven configurations, the median ratio

```text
peak_estimated_nonzeros(q) / peak_estimated_nonzeros(best competitor)
```

was `0.227`, with range `0.153 .. 0.351`. The corresponding median cumulative ratio was `0.258`. Internal msolve elapsed time gave nine wins and two ties for the q-system against the fastest competitor, although the sub-second timings are secondary to the matrix data.

The dense degree-12 relative norm has a real startup cost: at `k=1` its matrices were larger than the y-coordinate quotient. The crossover appeared by `k=2` in every tested field.

## Largest input: p=823, k=4

| Presentation | msolve elapsed | Maximum matrix data | Density | Pairs reduced | Rows reduced | Max F4 degree | Max RSS |
|---|---:|---:|---:|---:|---:|---:|---:|
| `q_c6_orbit` | 0.08 s | 625 x 621 | 0.992% | 575 | 1,156 | 13 | 14,696 KB |
| `y_c3_quotient` | 0.16 s | 847 x 837 | 2.064% | 1,566 | 3,136 | 14 | 19,456 KB |
| `x_plain` | 0.35 s | 1,124 x 1,992 | 5.078% | 2,489 | 4,982 | 19 | 22,464 KB |
| `u_faithful_glv` | 1.02 s | 4,760 x 6,041 | 3.208% | 5,547 | 11,165 | 12 | 34,624 KB |

The faithful `u/x` presentation reached lower maximum degree than the plain x-system but was substantially more expensive. Degree alone is therefore not an adequate representation-quality criterion.

## Exact bounded question

Let

```text
E_b / F_p : y^2 = x^3 + b,
H = <phi,-1> ~= C6,
F_k = union_{j=1}^k H.R_j,
q(P) = y(P)^2,
f_k(T) = product_j (T-q(R_j)).
```

Define

```text
J_q(p,k,Q) = <
  U3(q1,q2,r),
  U3(r,q3,q(Q)),
  f_k(q1), f_k(q2), f_k(q3)
>.
```

The live representation question is whether `J_q` preserves exact relation semantics and polynomial-time phase recovery while having asymptotically lower F4 Macaulay complexity per verified relation than every faithful Semaev/GLV presentation.

A primary ratio is

```text
R(p,k,m) = max_d nnz(M_d(J_q))
           / min_presentation max_d nnz(M_d(J_presentation)).
```

A meaningful positive result requires `R < 1` persistently as both factor-base orbit count `k` and relation-tree size `m` grow. A changed attack exponent would require a stronger end-to-end result including relation yield, phase recovery, sparse linear algebra, and target decomposition.

## Scope boundary

This run is positive bounded evidence for one representation mechanism. It is not:

- a secp256k1 ECDLP recovery;
- a claim below Pollard rho;
- an asymptotic result;
- a route promotion;
- an authorized native Research Engine experiment.

The next informative tests must scale `k` beyond four and increase the relation-tree size `m`; increasing only the toy field prime mostly probes coefficient/rank robustness rather than the dominant monomial-combinatorics growth.
