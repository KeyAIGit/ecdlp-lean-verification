#!/usr/bin/env python3
"""Measured q=4 square-free norm-system probe; no q16 extrapolation.
Uses SymPy and materializes Groebner bases, so it is a control of a specifically
bounded presentation, not the intended one-root scalable implementation.
"""
from pathlib import Path
from itertools import combinations,product
import json,time,hashlib,sys
import sympy as sp
import norm_bridge as nb
from run_q2_benchmark import allpoints
X=sp.Symbol('X');a1,a2,b0=sp.symbols('a1 a2 b0');V=(a1,a2,b0)

def system(p,D,R,usable=False):
    r,z=R;B=X+b0;A=(z*(r+b0)-a1*r-a2*r*r)+a1*X+a2*X*X
    g=sp.Poly(sp.div((X**3+7)*B**2-A**2,X-r,X)[0],X)
    # Target r,z lie on E modulo p, so only the quotient is needed here.
    coeff=[sp.Poly(g.nth(i),*V,modulus=p).as_expr()for i in range(4)]
    h=[sp.Integer(1),sp.Integer(0),sp.Integer(0),sp.Integer(0)]
    if usable:
        F=sorted(set(P[0] for P in allpoints(p) if pow(P[0],D,p)==1))
        poly=[1]
        for root in F:poly=nb.pm(poly,[-root,1],p)
        accum=[sp.Integer(poly[0]),sp.Integer(0),sp.Integer(0),sp.Integer(0)]
        max_power=len(poly)-1
    else:max_power=D
    for power in range(1,max_power+1):
        lead=h[3];h=[-lead*coeff[0],h[0]-lead*coeff[1],h[1]-lead*coeff[2],h[2]-lead*coeff[3]]
        h=[sp.Poly(t,*V,modulus=p).as_expr()for t in h]
        if usable:
            accum=[sp.Poly(accum[j]+poly[power]*h[j],*V,modulus=p).as_expr()for j in range(4)]
    if usable:h=accum
    else:h[0]-=1
    eqs=[sp.Poly(t,*V,modulus=p).as_expr()for t in h]
    return eqs

def roots_fp(expr,v,p):
    f=sp.Poly(expr,v,modulus=p)
    co=[int(c)%p for c in reversed(f.all_coeffs())]
    h=nb.pgcd(co,nb.ps(nb.ppow([0,1],p,co,p),[0,1],p),p)
    return nb.split_linear_roots(h,p) if len(h)>1 else []

def solve_lex(expressions,vars,p):
    if not vars:return [{}] if all(int(e)%p==0 for e in expressions)else []
    expressions=[sp.Poly(e,*vars,modulus=p).as_expr()for e in expressions]
    if any(not e.free_symbols and int(e)%p!=0 for e in expressions):return []
    expressions=[e for e in expressions if e!=0]
    if not expressions:raise ValueError('positive-dimensional branch')
    G=sp.groebner(expressions,*vars,modulus=p,order='lex')
    if len(G.polys)==1 and G.polys[0].total_degree()==0:return []
    last=vars[-1]
    uni=[g.as_expr()for g in G.polys if g.as_expr().free_symbols<={last}]
    if not uni:raise ValueError('no finite elimination polynomial')
    f=sp.Poly(uni[0],last,modulus=p)
    for e in uni[1:]:f=sp.gcd(f,sp.Poly(e,last,modulus=p))
    out=[]
    for c in roots_fp(f.as_expr(),last,p):
        reduced=[g.as_expr().subs(last,c)for g in G.polys]
        for sol in solve_lex(reduced,vars[:-1],p):out.append({**sol,last:c})
    return out

def run(p,D,index,usable=False):
    pts=allpoints(p);n=len(pts)+1;G=pts[0]
    k=int.from_bytes(hashlib.sha256(f'm16-next-q4:{p}:{index}'.encode()).digest(),'big')%n
    R=nb.ec_mul(k,G,p)
    if R is None or pow(R[0],D,p)==1:return {'status':'SEPARATE_TARGET','p':p,'D':D,'index':index}
    t=time.perf_counter();eqs=system(p,D,R,usable=usable);build=time.perf_counter()-t
    profile=[{'degree':sp.Poly(e,*V,modulus=p).total_degree(),'terms':len(sp.Poly(e,*V,modulus=p).terms())}for e in eqs]
    print('START',p,D,index,'profile',profile,flush=True)
    t=time.perf_counter();gb=sp.groebner(eqs,*V,modulus=p,order='grevlex');gbt=time.perf_counter()-t
    print('GB',gbt,'size',len(gb.polys),'zero_dim',gb.is_zero_dimensional,flush=True)
    t=time.perf_counter();solutions=solve_lex([g.as_expr()for g in gb.polys],V,p);lex_t=time.perf_counter()-t
    accepted=[];rejected=[]
    for sol in solutions:
        r,z=R;t1,t2,u=[int(sol[v])for v in V]
        A=[(z*(r+u)-t1*r-t2*r*r)%p,t1,t2];B=[u,1]
        N=nb.ps(nb.pm([7,0,0,1],nb.pm(B,B,p),p),nb.pm(A,A,p),p)
        g,rem=nb.pd(N,[-r,1],p);assert rem==[0]
        c={'p':p,'D':D,'q':4,'R':list(R),'A':A,'B':B,'g':g,'generation':'UNPLANTED_Q4_SQUAREFREE_GROEBNER_SEARCH'}
        try:got=nb.verify_and_recover(c)
        except ValueError as e:rejected.append(str(e));continue
        assert len(set(x for x,y in got))==4
        c['recovered_points']=[list(P)for P in got];c['distinct_x_count']=4;accepted.append(c)
    F=[P for P in pts if pow(P[0],D,p)==1];byx={}
    for x,y in F:byx.setdefault(x,[]).append(y)
    expected=set()
    for xs in combinations(sorted(byx),4):
        for ys in product(*(byx[x]for x in xs)):
            Ps=tuple(zip(xs,ys))
            if nb.ec_sum(list(Ps),p)==R:expected.add(Ps)
    got={tuple(sorted(tuple(P)for P in c['recovered_points']))for c in accepted}
    assert expected==got
    return {'status':'PASS_COMPLETE_SQUAREFREE_Q4','membership_encoding':'usable' if usable else 'full_H','p':p,'D':D,'n':n,'index':index,'R':R,
            'target_scalar_harness_only':k,'profile':profile,'build_seconds':build,
            'grevlex_seconds':gbt,'lex_and_extract_seconds':lex_t,'gb_size':len(gb.polys),
            'gb_max_output_degree':max(g.total_degree()for g in gb.polys),
            'parameter_solutions':len(solutions),'accepted':accepted,'rejected':rejected,
            'scope':'Unplanted q4 search, all base-field solutions in square-free chart. Not solving-degree measurement.'}

if __name__=='__main__':
    p,D,i=map(int,sys.argv[1:4]);usable=len(sys.argv)>4 and sys.argv[4]=='usable';out=run(p,D,i,usable=usable)
    Path(__file__).with_name(f'q4_{p}_{D}_{i}'+('_usable' if usable else '')+'.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items()if k not in ['accepted']},indent=2))
