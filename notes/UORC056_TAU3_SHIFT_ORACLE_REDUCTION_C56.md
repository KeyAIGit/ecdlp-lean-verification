# UORC-056 C56: exact tau_3 shift-oracle reduction to ECDLP

Date: 2026-08-22

Status: exact constructive reduction and deterministic replay. No fast evaluator for the carry is constructed, and no unconditional lower bound on its evaluation cost is claimed.

## 1. Target bit

Let `n > 3` be odd with `3` not dividing `n`, let `G` have order `n`, and let

\[
Q=[k]G,\qquad 0\le k<n.
\]

Define the odd-multiplier parity transport

\[
\tau_3(k)=\frac{(-1)^{[3k]_n}}{(-1)^k}
         =(-1)^{\lfloor 3k/n\rfloor}.
\]

Because `0 <= k < n`, the quotient `floor(3k/n)` is one of `0,1,2`. Therefore

\[
\tau_3(k)=-1
\]

exactly on the single canonical interval

\[
I_n=
\left\{
\left\lceil\frac n3\right\rceil,
\ldots,
\left\lceil\frac{2n}{3}\right\rceil-1
\right\}.
\]

Write its cardinality as

\[
s=|I_n|
 =\left\lceil\frac{2n}{3}\right\rceil
  -\left\lceil\frac n3\right\rceil.
\]

Thus an exact `tau_3` evaluator is an exact membership oracle for one interval of length approximately `n/3`.

## 2. Public shifts give every translated interval

Suppose a uniform public algorithm evaluates `tau_3(r)` from `(G,[r]G)` for every subgroup point.

For any public `t`, query it at

\[
Q_t=Q+[t]G=[k+t]_nG.
\]

The answer is negative exactly when

\[
[k+t]_n\in I_n,
\]

or equivalently when `k` lies in the cyclic translate `I_n-t`.

As `t` varies, this realizes membership queries for every cyclic interval of the fixed length `s`.

## 3. Exact recovery algorithm

Represent the current candidate set by a cyclic interval

\[
A=[a,a+L)
\]

of length `L` known to contain `k`.

### Initial query

Query the untranslated interval `I_n`.

- If the answer is negative, set `A=I_n`, so `L=s`.
- Otherwise set `A` to the cyclic complement, so `L=n-s`.

In both branches,

\[
L\le n-s.
\]

### Halving step

For `L>1`, set

\[
r=\left\lfloor\frac L2\right\rfloor.
\]

Choose a translated interval `J` of length `s` whose intersection with `A` is exactly the first `r` elements of `A`. One explicit choice is

\[
J=[a-(s-r),\ a+r).
\]

This is feasible because:

\[
r\le s
\]

and

\[
s-r\le n-L.
\]

The part of `J` before `a` therefore lies entirely in the known complement of `A`.

- If the oracle says `k in J`, retain the prefix of length `r`.
- Otherwise retain the suffix of length `L-r`.

Both branches remain cyclic intervals, and the new length is at most

\[
\left\lceil\frac L2\right\rceil.
\]

Iteration ends at a singleton, which is the exact canonical scalar `k`.

## 4. Query complexity

The initial branch has size at most `n-s`. Every later query halves the candidate interval. Hence the total number of oracle evaluations is at most

\[
\boxed{
1+\left\lceil\log_2(n-s)\right\rceil.
}
\]

For secp256k1,

\[
s=
38597363079105398474523661669562635950945854759691634794201721047172720498112,
\]

and

\[
n-s=
77194726158210796949047323339125271901891709519383269588403442094345440996225.
\]

Therefore the exact bound is

\[
\boxed{257\text{ calls to a uniform }\tau_3\text{ evaluator}.}
\]

The remaining work consists of public additions of known multiples of `G` and ordinary integer bookkeeping.

## 5. Consequence

A uniform exact endpoint algorithm

\[
A_3(G,[r]G)=\tau_3(r)
\]

on all subgroup points yields a complete secp256k1 discrete-log algorithm by the reduction above.

This is stronger than saying that `tau_3` correlates with parity. It is a direct chosen-shift reduction:

\[
\boxed{
\text{exact uniform }\tau_3\text{ evaluation}
\Longrightarrow
\text{full ECDLP recovery}.
}
\]

The reduction does not prove that one call costs square-root time, and it does not exclude a non-generic breakthrough. It shows that `tau_3` is not a harmless auxiliary side bit: any uniform exact shortcut for it is already an ECDLP shortcut.

## 6. Relation to the character-degree barrier

The companion C56 character-sum result proves that a Kummer-primitive quadratic-character realization of `tau_3` must have degree at least

\[
56713727820156410577229101238628035243.
\]

The present result is orthogonal:

- the character-sum theorem restricts a concrete endpoint grammar;
- the shift reduction applies to any uniform exact evaluator, regardless of its internal representation;
- neither result alone is a circuit lower bound.

## 7. Replay

Run:

```bash
python3 experiments/uorc056_cross_cycle_carry_c56/recover_tau3.py \
  --output artifacts/uorc056_cross_cycle_carry_c56/tau3_recovery_certificate.json
```

The frozen replay checks:

- 10,000 deterministic random secp256k1 scalars;
- exact recovery in at most 257 oracle calls;
- exhaustive recovery of every scalar for every odd prime from 5 through 5,000;
- 667 prime orders and 1,548,131 exhaustive small-order scalar cases;
- exact interval and query-bound arithmetic.

## 8. Next boundary

The useful positive search is now narrower. A proposed cross-cycle state must either:

1. fail to give a uniform exact `tau_3` evaluator;
2. be approximate or distributional, with a separately proved amplification analysis;
3. evade the low-degree character grammar through a high-degree low-circuit or non-character construction;
4. expose why its evaluation cost does not already implement the 257-query ECDLP reduction.

No exact evaluator has been found.
