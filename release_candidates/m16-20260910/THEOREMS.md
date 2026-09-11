# Mathematical scope of the M16 intake

Written arguments, not Lean certificates. The public executable checks only
finite instances of statements 1 and 2. Statement 3 and the norm-map connection
remain review/formalization candidates. None establishes global search cost.

## 1. Root support with multiplicities

Let k have characteristic zero or characteristic p > q. Let g be monic of
positive degree q, and let F be a polynomial. Then

```
g divides F^q  <=>  g divides F*g'.
```

Over an algebraic closure, let alpha have multiplicity e in g. Its multiplicity
in g' is exactly e-1, since 1 <= e <= q is nonzero in k. Consequently F*g' is
divisible by g exactly when F vanishes at every root of g. This is equivalent
to g dividing F^q since no multiplicity of g exceeds q. Divisibility descends
to k by monic polynomial division. F need not be squarefree for this statement.
The equivalent radical criterion is `g/gcd(g,g') divides F`.

Counterexample without the characteristic guard: over F_3, take g=X^3 and
F=X-1. The derivative is zero, but g does not divide F^3.

This is a classical use of squarefree factorization, not a claimed new general
identity. See Ben Lynn's [polynomial-root notes](https://crypto.stanford.edu/pbc/notes/ep/root.html).

## 2. The derivative presentation is locally reduced

Now assume F is nonzero and squarefree, and define `S(g)=rem(F*g',g)` as q equations in the
q nonleading coefficients of g. At a solution put H=F*g'/g. For a coefficient
variation h of degree less than q, differentiation of the division identity
gives

```
dS_g(h) = rem(F*h' - H*h, g).
```

Write `g=product_i (X-alpha_i)^e_i`. In the local ring at alpha_i, with
T=X-alpha_i, we have `F=F'(alpha_i)*T+O(T^2)` and
`H=e_i*F'(alpha_i)+O(T)`. On the filtration with basis T^j,
0 <= j < e_i, the diagonal of this linear map is
`(j-e_i)*F'(alpha_i)`. All entries are nonzero. Thus

```
det dS_g = (-1)^q * product_i e_i! * F'(alpha_i)^e_i != 0.
```

This gives rank q, even when g has repeated roots. If F=X^D-1 and its roots
are simple, the determinant simplifies to
`D^q * product_i e_i! / g(0)`.

Squarefreeness is essential for this rank statement. For example,
F=(X-1)^2 and g=X-1 satisfy the support condition but have zero derivative of
the remainder map. The public tests retain this negative case.

For comparison, at a solution of `P(g)=rem(F^q,g)`,
`dP_g(h)=-rem((F^q/g)*h,g)`. If g is squarefree, g divides F and q>=2,
this derivative vanishes. This comparison concerns a powered presentation;
it does not claim an improvement over every squarefree solver.

## 3. Conditional connection to the norm chart

For E:y^2=x^3+7, even q=2s, and R=(r,z), consider

```
deg a <= s;  b monic of degree s-1;  a(r)=z*b(r)
g=((X^3+7)*b^2-a^2)/(X-r), monic of degree q.
```

Retain the admissibility assumptions: characteristic > q and not 2, 3 or 7,
z != 0, r is outside the permitted coordinate support, F is nonzero,
squarefree, splits over the base field, has no root in common with X^3+7,
and gcd(g,b)=1. Supported roots recover
signed points as `(alpha,-a(alpha)/b(alpha))`, with their multiplicities.
The function a+y*b has divisor consisting of those points and -R, minus
(q+1) times the point at infinity. The divisor/group-law correspondence
therefore gives their sum R. The converse and uniqueness use the fixed pole
order and normalization. See [Snowden's elliptic-curve notes](https://websites.umich.edu/~asnowden/teaching/2013/679/L02.html)
for the classical divisor and Riemann-Roch background.

The linearization of the parameter-to-g map is
`delta_g=2*((X^3+7)*b*delta_b-a*delta_a)/(X-r)`.
At an admissible solution, a is coprime to `(X^3+7)*b`: a common root would
contradict either gcd(g,b)=1, the simple excluded target root, or the support
assumptions. If delta_g=0, then `(X^3+7)*b` divides delta_a. Its degree s+2
exceeds the maximum degree s of delta_a. Hence delta_a=delta_b=0.
Composing this injective derivative with statement 2 gives rank q-1 in the
norm parameters, including rank 15 for q=16. This is conditional on the full
admissibility assumptions, not a statement about the unsaturated ideal.

## 4. What has not followed

Local full rank is not a bound on solving degree, global elimination, memory,
or time to find a component. It does not establish Newton convergence from a
random start in a finite field. Factoring a known small certificate is not
searching for the certificate. More examples are not evidence of asymptotic
improvement unless their scaling and cost model support that inference.

For the relation-collection scheme under discussion, an estimate must include

```
C_pre + (B+1)*C_try/delta_alg + C_LA,
```

with a justified algorithmic success probability, consistent cost units,
matching target distributions and verified recovery. No such end-to-end
advantage is established by this intake. The intended research context is the
prime-field generalized-root-finding problem of Petit, Kosters and Messeng,
[PKC 2016](https://people.maths.ox.ac.uk/petit/files/16PKC_primeECDLP.pdf), not a
claim that an extension-field complexity estimate transfers to secp256k1.
