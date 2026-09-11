# SPDX-License-Identifier: Apache-2.0
"""Exact checks of equation projection; no remote calls or secret-key input.

The q4 census enumerates every coefficient assignment. It is a ground-truth
check, NOT a proposed scalable algorithm. NumPy is only used for that census.
The independent polynomial evaluator and point oracle use integer arithmetic.
"""
from __future__ import annotations
import hashlib
import itertools
import json
import math
from collections import Counter
from fractions import Fraction
from pathlib import Path
import time
import sys
from functools import lru_cache

HERE = Path(__file__).resolve().parent


def projective_points(p: int, dimension: int):
    for pivot in range(dimension):
        for suffix in itertools.product(range(p), repeat=dimension-pivot-1):
            yield (0,)*pivot + (1,) + suffix


@lru_cache(maxsize=64)
def checked_small_prime(p):
    if type(p) is not int or not 2 <= p <= 10000:
        raise ValueError('this verification program accepts only small prime fields')
    if any(p % d == 0 for d in range(2, math.isqrt(p)+1)):
        raise ValueError('prime modulus required')
    return p


def project(s, v, p):
    checked_small_prime(p)
    if any(type(x) is not int for x in (*s, *v)):
        raise ValueError('integer coefficients required')
    if len(s) != len(v) or len(s) < 2:
        raise ValueError('equal lengths >= 2 required')
    v = [x % p for x in v]
    pivot = next((i for i, x in enumerate(v) if x), None)
    if pivot is None:
        raise ValueError('zero selector is forbidden')
    return [(v[pivot]*s[i]-v[i]*s[pivot]) % p
            for i in range(len(v)) if i != pivot]


def rank(a, p):
    a = [[x % p for x in row] for row in a]
    r = 0
    for c in range(len(a[0])):
        pivot = next((i for i in range(r,len(a)) if a[i][c]),None)
        if pivot is None:
            continue
        a[r],a[pivot]=a[pivot],a[r]
        inv=pow(a[r][c],-1,p)
        a[r]=[x*inv%p for x in a[r]]
        for i in range(len(a)):
            if i != r:
                t=a[i][c]
                a[i]=[(x-t*y)%p for x,y in zip(a[i],a[r])]
        r+=1
        if r==len(a):break
    return r


def linear_exhaustive(p):
    # Two genuine nonsingular zeros, plus independently classified nonzeros.
    residual = lambda x,y: ((x*x-x)%p,(y*y-y)%p,(x-y)%p)
    true = {(x,y) for x,y in itertools.product(range(p),repeat=2)
            if not any(residual(x,y))}
    assert true == {(0,0),(1,1)}
    selectors=list(projective_points(p,3))
    extra_total=0
    regular=Counter()
    for v in selectors:
        zeros={(x,y) for x,y in itertools.product(range(p),repeat=2)
               if not any(project(residual(x,y),v,p))}
        assert true <= zeros
        extra_total += len(zeros-true)
        for x,y in true:
            j=[[2*x-1,0],[0,2*y-1],[1,-1]]
            cols=[project([row[c] for row in j],v,p) for c in range(2)]
            aj=[[cols[c][i] for c in range(2)] for i in range(2)]
            regular[(x,y)]+=rank(aj,p)==2
    assert extra_total==p*p-len(true)
    assert set(regular.values())=={p*p}
    return {'p':p,'projective_selectors':len(selectors),
            'assignments_per_selector':p*p,'original_zeros':len(true),
            'total_extra_zeros':extra_total,
            'expected_extra_zeros':str(Fraction(extra_total,len(selectors))),
            'regular_selectors_per_original_zero':p*p,
            'regular_probability':str(Fraction(p*p,len(selectors)))}


def trim(a,p):
    a=[x%p for x in a]
    while len(a)>1 and a[-1]==0:a.pop()
    return a or [0]


def mul(a,b,p):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%p
    return trim(c,p)


def divmod_poly(a,b,p):
    a=trim(a,p);b=trim(b,p)
    if b==[0]:raise ValueError('zero divisor')
    q=[0]*max(1,len(a)-len(b)+1)
    while len(a)>=len(b) and a!=[0]:
        i=len(a)-len(b);v=a[-1]*pow(b[-1],-1,p)%p;q[i]=v
        for j,x in enumerate(b):a[i+j]=(a[i+j]-v*x)%p
        a=trim(a,p)
    return trim(q,p),a


def scalar_residual(a1,a2,b0,p,r,z):
    a0=(z*(r+b0)-a1*r-a2*r*r)%p
    norm=mul([7,0,0,1],mul([b0,1],[b0,1],p),p)
    a2poly=mul([a0,a1,a2],[a0,a1,a2],p)
    for i,c in enumerate(a2poly):norm[i]=(norm[i]-c)%p
    g,rem=divmod_poly(norm,[-r,1],p);assert rem==[0]
    dg=[i*g[i]%p for i in range(1,len(g))]
    _,rem=divmod_poly(mul([-1,0,0,1],dg,p),g,p)
    return g,rem+[0]*(4-len(rem))


def evaluate(a,x,p):
    ans=0
    for c in reversed(a):ans=(ans*x+c)%p
    return ans


def ec_add(a,b,p):
    if a is None:return b
    if b is None:return a
    x,y=a;u,v=b
    if x==u and (y+v)%p==0:return None
    slope=((v-y)*pow((u-x)%p,-1,p) if x!=u
           else 3*x*x*pow(2*y%p,-1,p))%p
    xx=(slope*slope-x-u)%p
    return xx,(slope*(x-xx)-y)%p


def norm_census(plan, diagnostic_selector=None):
    import numpy as np
    p=plan['fixture']['p'];r,z=plan['fixture']['R']
    assert (p,plan['fixture']['D'],plan['fixture']['q'])==(97,3,4)
    assert (z*z-r*r*r-7)%p==0 and pow(r,3,p)!=1
    count=p**3
    idx=np.arange(count,dtype=np.int64)
    a1=idx%p;a2=(idx//p)%p;b0=idx//(p*p)
    a0=(z*(r+b0)-a1*r-a2*r*r)%p
    g3=(2*b0-a2*a2+r)%p
    g2=(b0*b0-2*a1*a2+r*g3)%p
    g1=(7-a1*a1-2*a0*a2+r*g2)%p
    g0=(14*b0-2*a0*a1+r*g1)%p
    assert np.all((7*b0*b0-a0*a0+r*g0)%p==0)
    gs=[g0,g1,g2,g3]
    # (X^3-1)g', followed by exact monic division, vectorized.
    h=[-g1%p,-2*g2%p,-3*g3%p,(g1-4)%p,2*g2%p,3*g3%p,
       np.full(count,4,dtype=np.int64)]
    for degree in (6,5,4):
        lead=h[degree]
        for j in range(4):h[degree-4+j]=(h[degree-4+j]-lead*gs[j])%p
    s=np.asarray(h[:4])
    allowed=(g0-b0*g1+b0*b0*g2-b0**3*g3+b0**4)%p!=0
    zero=np.all(s==0,axis=0)
    true=zero&allowed
    nonzero_allowed=allowed&~zero
    sample=set(np.linspace(0,count-1,plan['independent_residual_samples'],dtype=np.int64).tolist())
    sample.update(np.flatnonzero(zero).tolist())
    for i in sorted(sample):
        gg,ss=scalar_residual(int(a1[i]),int(a2[i]),int(b0[i]),p,r,z)
        assert gg==[int(g[i]) for g in gs]+[1]
        assert ss==s[:,i].tolist()
    # Every nonzero residual corresponds to exactly one projective selector.
    non=s[:,nonzero_allowed]
    piv=np.argmax(non!=0,axis=0)
    inverse=np.array([0]+[pow(i,-1,p) for i in range(1,p)],dtype=np.int64)
    scale=inverse[non[piv,np.arange(non.shape[1])]]
    keys=np.zeros(non.shape[1],dtype=np.int64)
    for j in range(4):keys+=((non[j]*scale)%p)*p**j
    directions,mults=np.unique(keys,return_counts=True)
    line_count=sum(p**i for i in range(4))
    histogram=Counter(map(int,mults))
    histogram[0]=line_count-len(directions)
    assert sum(histogram.values())==line_count
    assert sum(k*v for k,v in histogram.items())==int(nonzero_allowed.sum())
    roots=[x for x in range(p) if pow(x,3,p)==1]
    points=[(x,y) for x in roots for y in range(p) if (y*y-x*x*x-7)%p==0]
    oracle=set()
    for inds in itertools.combinations_with_replacement(range(len(points)),4):
        pts=tuple(sorted(points[i] for i in inds));s0=None
        if any((x,(-y)%p) in pts for x,y in pts):continue
        for point in pts:s0=ec_add(s0,point,p)
        if s0==(r,z):oracle.add(pts)
    recovered=set();certificates=[]
    for i in map(int,np.flatnonzero(true)):
        gg=[int(g[i]) for g in gs]+[1];remain=gg[:];pts=[]
        for x in roots:
            while len(remain)>1:
                quo,rem=divmod_poly(remain,[-x,1],p)
                if rem!=[0]:break
                y=-evaluate([int(a0[i]),int(a1[i]),int(a2[i])],x,p)*pow((x+int(b0[i]))%p,-1,p)%p
                assert (y*y-x*x*x-7)%p==0
                pts.append((x,y));remain=quo
        assert remain==[1] and len(pts)==4
        point=None
        for pt in pts:point=ec_add(point,pt,p)
        assert point==(r,z)
        recovered.add(tuple(sorted(pts)))
        certificates.append({'parameters':[int(a1[i]),int(a2[i]),int(b0[i])],'g':gg,'points':[list(pt) for pt in sorted(pts)]})
    assert recovered==oracle and len(certificates)==len(oracle)
    report = {'fixture':plan['fixture'],'assignments_checked':count,
            'admissible_assignments':int(allowed.sum()),'raw_original_zeros':int(zero.sum()),
            'admissible_original_zeros':int(true.sum()),'selector_count':line_count,
            'extra_root_histogram':{str(k):v for k,v in sorted(histogram.items())},
            'expected_extra_admissible_roots':str(Fraction(int(nonzero_allowed.sum()),line_count)),
            'probability_of_no_extra_admissible_root':str(Fraction(histogram[0],line_count)),
            'independent_scalar_checks':len(sample),'multiset_oracle_agrees':True,
            'certificates':certificates,
            'scope':'Full enumeration for validation, not scalable search.'}
    if diagnostic_selector is not None:
        project([0]*4, diagnostic_selector, p)
        v=[x%p for x in diagnostic_selector]
        j=next(i for i,x in enumerate(v) if x)
        same=np.ones(count,dtype=bool)
        for i in range(4):
            if i!=j:same &= (v[j]*s[i]-v[i]*s[j])%p==0
        report['selected_projection']={
            'selector':v,'rational_roots_before_admissibility':int(same.sum()),
            'admissible_rational_roots':int((same&allowed).sum()),
            'extra_admissible_rational_roots':int((same&nonzero_allowed).sum()),
            'all_original_roots_retained':bool(np.all(same[true]))}
    return report


def main():
    start=time.perf_counter()
    plan=json.loads((HERE/'PLAN.json').read_text())
    linear=[linear_exhaustive(x['p']) for x in plan['linear_projection_checks']]
    census=norm_census(plan)
    p=2**256-2**32-977
    n=int('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141',16)
    a=567054;m=math.comb(a+15,16)
    result={'schema':'m16-equation-projection-check/v1','status':'PASS',
            'plan_sha256':hashlib.sha256((HERE/'PLAN.json').read_bytes()).hexdigest(),
            'linear_exhaustive':linear,'norm_census':census,
            'conditional_mean_certificate_upper':str(Fraction(m,n-a-1)),
            'random_parameter_slice_bound_log2':math.log2(m)-math.log2(n-a-1)-math.log2(p),
            'elapsed_seconds':time.perf_counter()-start,
            'lean_checked':False,'external_review':False,'new_256_bit_targets_solved':0,
            'original_research_archives_modified':False}
    if '--check' in sys.argv:
        saved=json.loads((HERE/'RESULTS.json').read_text())
        stable=lambda r: {k:v for k,v in r.items() if k!='elapsed_seconds'}
        if stable(saved)!=stable(result):
            raise RuntimeError('computed evidence differs from the saved report')
        print('PASS: exact structural report reproduced; timing is not an invariant')
    else:
        if '--write' in sys.argv:
            (HERE/'RESULTS.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
        print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
