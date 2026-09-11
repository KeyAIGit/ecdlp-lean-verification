#!/usr/bin/env python3
"""Small exact search benchmark for radical-support derivative equations.
Targets are SHA256-selected independently of the factor base. The solver receives
only p,D,q,R. Root enumeration is a separate, post-solver validation path.
"""
from __future__ import annotations
import argparse, hashlib, json, time, sys
from pathlib import Path
from itertools import combinations_with_replacement
from collections import Counter
import sympy as s
from sympy.polys.rings import ring
from sympy.polys.domains import GF
import norm_bridge as nb

ROOT=Path(__file__).resolve().parent
OLD=ROOT/'input/M16_next_100_nodes'
sys.path.insert(0,str(OLD))
from q4_symbolic_probe import solve_lex

def allpoints(p):
    sq={}
    for y in range(p): sq.setdefault(y*y%p,[]).append(y)
    return [(x,y) for x in range(p) for y in sq.get((x*x*x+7)%p,[])]

def target(p,index):
    pts=allpoints(p)
    h=int.from_bytes(hashlib.sha256(f'M16-derivative-unplanted-v1:{p}:{index}'.encode()).digest(),'big')
    return pts[h%len(pts)]

def systems(p,D,q,R,encoding='derivative',membership='usable'):
    assert q>=2 and q%2==0 and p>q and (p-1)%D==0
    r,z=R; ss=q//2
    assert pow(r,D,p)!=1
    names=[f'a{i}' for i in range(1,ss+1)]+[f'b{i}' for i in range(ss-1)]
    rr,*v=ring(','.join(names),GF(p)); one=rr.one; zero=rr.zero
    aa=[zero]+list(v[:ss]);bb=list(v[ss:])+[one]
    aa[0]=sum((z*bb[i]*pow(r,i,p) for i in range(ss)),zero)-sum((aa[i]*pow(r,i,p) for i in range(1,ss+1)),zero)
    def mul(a,b):
        out=[zero]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):out[i+j]+=x*y
        return out
    N=mul([rr(7),zero,zero,one],mul(bb,bb));a2=mul(aa,aa)
    for i,a in enumerate(a2):N[i]-=a
    gg=[zero]*(q+1); gg[q]=N[q+1]
    for i in range(q-1,-1,-1):gg[i]=N[i+1]+r*gg[i+1]
    assert N[0]+r*gg[0]==0 and gg[q]==one
    if membership=='usable':
        xs=sorted({x for x,y in allpoints(p) if pow(x,D,p)==1})
        F=[1]
        for x in xs:F=nb.pm(F,[-x,1],p)
    else:
        F=[-1]+[0]*(D-1)+[1]
    def mx(a):
        lead=a[q-1]
        return [-lead*gg[0]]+[a[i-1]-lead*gg[i] for i in range(1,q)]
    def rem_numeric(coeff):
        out=[zero]*q
        for c in reversed(coeff):out=mx(out);out[0]+=int(c)
        return out
    def modmul(a,b):
        out=mul(a,b)
        for i in range(len(out)-1,q-1,-1):
            t=out[i]
            if t:
                for j in range(q):out[i-q+j]-=t*gg[j]
        return out[:q]
    if encoding=='quotient':
        L=len(F)-1
        if L<1: raise ValueError('empty factor base')
        symbols=s.symbols(' '.join(names),seq=True)
        hs=s.symbols(' '.join(f'h{i}'for i in range(L-1)),seq=True) if L>1 else ()
        ggex=[t.as_expr()for t in gg]
        HH=list(hs)+[s.Integer(q)]
        gp=[(i+1)*ggex[i+1]for i in range(q)]
        out=[s.Integer(0)]*(q+L)
        for i,f in enumerate(F):
            for j,g in enumerate(gp):out[i+j]+=int(f)*g
        for i,h in enumerate(HH):
            for j,g in enumerate(ggex):out[i+j]-=h*g
        assert s.expand(out[-1])==0
        vs=tuple(hs)+tuple(symbols)
        out=[s.Poly(e,*vs,modulus=p).as_expr()for e in out[:-1]]
        return out,vs,[a.as_expr()for a in aa],[b.as_expr()for b in bb],ggex,F
    h=rem_numeric(F)
    if encoding=='derivative':eqs=modmul(h,[(i+1)*gg[i+1]for i in range(q)])
    elif encoding=='power':
        eqs=[one]+[zero]*(q-1)
        for _ in range(q):eqs=modmul(eqs,h)
    elif encoding=='squarefree':eqs=h
    else:raise ValueError(encoding)
    symbols=s.symbols(' '.join(names),seq=True)
    out=[e.as_expr()for e in eqs]
    return out,symbols,[a.as_expr()for a in aa],[b.as_expr()for b in bb],[g.as_expr()for g in gg],F

def rank_mod(A,p):
    A=[[int(a)%p for a in r]for r in A];k=0
    for c in range(len(A[0]) if A else 0):
        j=next((j for j in range(k,len(A))if A[j][c]),None)
        if j is None:continue
        A[k],A[j]=A[j],A[k];z=pow(A[k][c],-1,p);A[k]=[a*z%p for a in A[k]]
        for j in range(k+1,len(A)):
            z=A[j][c]
            A[j]=[(a-z*b)%p for a,b in zip(A[j],A[k])]
        k+=1
        if k==len(A):break
    return k

def run(p,D,q,index,encoding,membership):
    if p<=17 or not s.isprime(p) or q not in range(2,17,2) or D<=0 or (p-1)%D:
        raise ValueError('Require prime p>17, even 2<=q<=16, and D dividing p-1')
    if any(y==0 and pow(x,D,p)==1 for x,y in allpoints(p)):
        raise ValueError('Ramified factor-base points are outside this norm-chart benchmark')
    R=target(p,index)
    result={'p':p,'D':D,'q':q,'index':index,'R':R,'encoding':encoding,'membership':membership,'target_rule':'SHA256-selected from all affine curve points independently of A, before search'}
    if pow(R[0],D,p)==1:
        return dict(result,status='SEPARATE_TARGET_BRANCH')
    start=time.perf_counter()
    eqs,vs,aa,bb,gg,F=systems(p,D,q,R,encoding,membership)
    result.update(build_seconds=time.perf_counter()-start,profile=[{'degree':s.Poly(e,*vs,modulus=p).total_degree(),'terms':len(s.Poly(e,*vs,modulus=p).terms())}for e in eqs],F=F)
    print(json.dumps({'stage':'built',**result}),flush=True)
    start=time.perf_counter(); gb=s.groebner(eqs,*vs,modulus=p,order='grevlex');result['grevlex_seconds']=time.perf_counter()-start
    result['gb_size']=len(gb.polys);result['gb_output_max_degree']=max((g.total_degree()for g in gb.polys),default=0)
    print(json.dumps({'stage':'grevlex','seconds':result['grevlex_seconds'],'gb_size':len(gb.polys)}),flush=True)
    start=time.perf_counter();sols=solve_lex([g.as_expr()for g in gb.polys],vs,p);result['extract_seconds']=time.perf_counter()-start
    accepted=[];rejected=[]
    J=[[s.diff(e,v)for v in vs]for e in eqs]
    for sol in sols:
        A=[int(e.subs(sol))%p for e in aa];B=[int(e.subs(sol))%p for e in bb];g=[int(e.subs(sol))%p for e in gg]
        cert={'p':p,'D':D,'q':q,'R':R,'A':A,'B':B,'g':g,'generation':'UNPLANTED_DERIVATIVE_NORM_SOLVER' if encoding in ['derivative','quotient'] else 'UNPLANTED_CONTROL_NORM_SOLVER'}
        try:P=nb.verify_and_recover(cert)
        except (ValueError,ArithmeticError) as exc:
            rejected.append({'parameters':[int(sol[v])for v in vs],'reason':str(exc)});continue
        jacrank=rank_mod([[int(e.subs(sol))%p for e in row]for row in J],p)
        cert.update(points=P,parameters=[int(sol[v])for v in vs],jacobian_rank=jacrank)
        accepted.append(cert)
    result.update(accepted=accepted,rejected=rejected,raw_solutions=len(sols),status='SOLVER_FINISHED')
    print(json.dumps({'stage':'done','accepted':len(accepted),'rejected':len(rejected),'ranks':sorted({c['jacobian_rank']for c in accepted})}),flush=True)
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--p',type=int,required=True);ap.add_argument('--D',type=int,required=True);ap.add_argument('--q',type=int,required=True);ap.add_argument('--index',type=int,default=0);ap.add_argument('--encoding',choices=['derivative','power','squarefree','quotient'],default='derivative');ap.add_argument('--membership',choices=['usable','full_H'],default='usable');args=ap.parse_args()
    result=run(args.p,args.D,args.q,args.index,args.encoding,args.membership)
    fn=ROOT/'results'/f'probe_{args.p}_{args.D}_{args.q}_{args.index}_{args.encoding}_{args.membership}.json'
    fn.write_text(json.dumps(result,indent=2));print('SAVED',fn)
