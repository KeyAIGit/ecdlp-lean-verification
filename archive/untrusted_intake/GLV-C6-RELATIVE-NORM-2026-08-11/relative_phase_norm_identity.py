#!/usr/bin/env python3
"""Exact sparse certificate for the relative-phase GLV norm identity.

For E_b: y^2=x^3+b and beta^2+beta+1=0, verify

  U3(x1^3+b,x2^3+b,x3^3+b)
    = product_{a,c in Z/3} S3(x1,beta^a*x2,beta^c*x3).

The nine factors index C3^3 / diagonal(C3). No ECDLP target is used.
"""
from __future__ import annotations

from collections import defaultdict
import hashlib
import itertools
import json
from pathlib import Path
import sympy as sp

HERE = Path(__file__).resolve().parent
Mon = tuple[int, int, int, int]  # powers of x1,x2,x3,b
Coeff = tuple[int, int]          # c0+c1*beta, beta^2+beta+1=0


def cmul(a: Coeff, b: Coeff) -> Coeff:
    a0, a1 = a; b0, b1 = b
    return (a0*b0-a1*b1, a0*b1+a1*b0-a1*b1)


def cadd(a: Coeff, b: Coeff) -> Coeff:
    return (a[0]+b[0], a[1]+b[1])


def beta_pow(k: int) -> Coeff:
    return ((1,0),(0,1),(-1,-1))[k % 3]


def pmul(A: dict[Mon,Coeff], B: dict[Mon,Coeff]) -> dict[Mon,Coeff]:
    out: dict[Mon,Coeff] = {}
    for ma, ca in A.items():
        for mb, cb in B.items():
            m = tuple(x+y for x,y in zip(ma,mb))
            v = cadd(out.get(m,(0,0)), cmul(ca,cb))
            if v == (0,0): out.pop(m,None)
            else: out[m] = v
    return out


def base_s3_terms() -> dict[Mon,int]:
    x1,x2,x3,b=sp.symbols('x1 x2 x3 b')
    expr=(x1-x2)**2*x3**2-2*((x1+x2)*x1*x2+2*b)*x3+(x1*x2)**2-4*b*(x1+x2)
    return {tuple(map(int,m)):int(c) for m,c in sp.Poly(sp.expand(expr),x1,x2,x3,b).terms()}


def transformed_s3(a:int,c:int) -> dict[Mon,Coeff]:
    out={}
    for m,z in base_s3_terms().items():
        ph=beta_pow(a*m[1]+c*m[2])
        out[m]=(z*ph[0],z*ph[1])
    return out


def relative_norm() -> tuple[dict[Mon,Coeff],list[int]]:
    P={(0,0,0,0):(1,0)}; counts=[]
    for a,c in itertools.product(range(3),repeat=2):
        P=pmul(P,transformed_s3(a,c)); counts.append(len(P))
    return P,counts


def load_u3_shifted() -> sp.Poly:
    x1,x2,x3,b,u1,u2,u3=sp.symbols('x1 x2 x3 b u1 u2 u3')
    raw=(HERE/'u3_raw.txt').read_text().strip()
    U=sp.sympify(raw,locals={'u1':u1,'u2':u2,'u3':u3,'b':b})
    shifted=sp.expand(U.subs({u1:x1**3+b,u2:x2**3+b,u3:x3**3+b},simultaneous=True))
    return sp.Poly(shifted,x1,x2,x3,b)


def main():
    norm,counts=relative_norm()
    beta_terms={m:c for m,c in norm.items() if c[1]}
    norm_int={m:c[0] for m,c in norm.items() if c[0]}
    shifted=load_u3_shifted()
    shifted_dict={tuple(map(int,m)):int(c) for m,c in shifted.terms()}
    exact=(not beta_terms and norm_int==shifted_dict)

    q1,q2,q3,b=sp.symbols('q1 q2 q3 b')
    raw=(HERE/'u3_raw.txt').read_text().strip()
    U=sp.Poly(sp.sympify(raw,locals={'u1':q1,'u2':q2,'u3':q3,'b':b}),q1,q2,q3,b)
    lc=sp.factor(sp.Poly(U.as_expr(),q3).LC())
    result={
      'scope':'exact sparse identity over Z[beta]/(beta^2+beta+1); no ECDLP target',
      'identity':'U3(x1^3+b,x2^3+b,x3^3+b)=product_{a,c in Z/3} S3(x1,beta^a*x2,beta^c*x3)',
      'relative_phase_group':'C3^3 / diagonal(C3) isomorphic to C3^2',
      'number_of_S3_factors':9,
      'intermediate_term_counts':counts,
      'beta_coefficient_terms_remaining':len(beta_terms),
      'relative_norm_integer_terms':len(norm_int),
      'shifted_U3_terms':len(shifted_dict),
      'exact_identity':exact,
      'U3_terms':len(U.terms()),
      'U3_multidegree_q':[int(U.degree(v)) for v in (q1,q2,q3)],
      'U3_total_degree':int(U.total_degree()),
      'U3_leading_coefficient_in_q3':str(lc),
      'leading_coefficient_derivation':'product_a (x1-beta^a*x2)^6=(x1^3-x2^3)^6=(q1-q2)^6',
      'q_translation':'q=y^2=x^3+b, hence q-b is the existing invariant u=x^3',
      'full_coordinatewise_norm_consequence':'product_{e1,e2,e3 in Z/3} S3(beta^e1*x1,beta^e2*x2,beta^e3*x3)=U3(x1^3+b,x2^3+b,x3^3+b)^3',
      'norm_sparse_sha256':hashlib.sha256(json.dumps(sorted((m,c) for m,c in norm_int.items()),separators=(',',':')).encode()).hexdigest(),
      'shifted_u3_sparse_sha256':hashlib.sha256(json.dumps(sorted((m,c) for m,c in shifted_dict.items()),separators=(',',':')).encode()).hexdigest(),
    }
    (HERE/'relative_phase_norm_identity_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    if not exact: raise SystemExit('identity failed')

if __name__=='__main__': main()
