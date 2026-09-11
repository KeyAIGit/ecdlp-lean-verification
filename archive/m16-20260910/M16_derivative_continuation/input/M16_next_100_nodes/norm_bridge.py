#!/usr/bin/env python3
"""Exact certificates, NOT a fast search algorithm, for E: y^2=x^3+7.
Interpolation consumes an existing witness. verify_and_recover does not.
Python 3.10+, standard library only; field must be prime, p>17.
"""
from __future__ import annotations
from collections import Counter
import hashlib, json, math, random
from typing import Optional
Poly = list[int]
Point = Optional[tuple[int,int]]

def tr(a:Poly,p:int)->Poly:
    a=[x%p for x in a]
    while len(a)>1 and a[-1]==0:a.pop()
    return a or [0]
def pa(a:Poly,b:Poly,p:int)->Poly:
    c=[0]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]+=x
    for i,x in enumerate(b):c[i]+=x
    return tr(c,p)
def ps(a:Poly,b:Poly,p:int)->Poly:return pa(a,[-x for x in b],p)
def scale(a:Poly,s:int,p:int)->Poly:return tr([s*x for x in a],p)
def pm(a:Poly,b:Poly,p:int)->Poly:
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%p
    return tr(c,p)
def pd(a:Poly,b:Poly,p:int)->tuple[Poly,Poly]:
    a=tr(a,p);b=tr(b,p)
    if b==[0]:raise ZeroDivisionError('zero polynomial divisor')
    q=[0]*max(1,len(a)-len(b)+1);inv=pow(b[-1],-1,p)
    while a!=[0] and len(a)>=len(b):
        j=len(a)-len(b);c=a[-1]*inv%p;q[j]=c
        for i,x in enumerate(b):a[i+j]=(a[i+j]-c*x)%p
        a=tr(a,p)
    return tr(q,p),a
def mod(a:Poly,b:Poly,p:int)->Poly:return pd(a,b,p)[1]
def monic(a:Poly,p:int)->Poly:
    a=tr(a,p)
    return scale(a,pow(a[-1],-1,p),p) if a!=[0] else [0]
def pgcd(a:Poly,b:Poly,p:int)->Poly:
    while tr(b,p)!=[0]:a,b=b,mod(a,b,p)
    return monic(a,p)
def pinv(a:Poly,g:Poly,p:int)->Poly:
    oldr,r=g,mod(a,g,p);olds,s=[0],[1]
    while r!=[0]:
        q,newr=pd(oldr,r,p);oldr,r=r,newr
        olds,s=s,ps(olds,pm(q,s,p),p)
    if len(oldr)!=1 or oldr==[0]:raise ValueError('polynomial not invertible')
    return mod(scale(olds,pow(oldr[0],-1,p),p),g,p)
def ppow(a:Poly,e:int,g:Poly,p:int)->Poly:
    if e<0:raise ValueError('negative exponent')
    out=[1];a=mod(a,g,p)
    while e:
        if e&1:out=mod(pm(out,a,p),g,p)
        e>>=1
        if e:a=mod(pm(a,a,p),g,p)
    return out
def pe(a:Poly,x:int,p:int)->int:
    z=0
    for c in reversed(a):z=(z*x+c)%p
    return z
def deriv(a:Poly,p:int)->Poly:return tr([i*a[i] for i in range(1,len(a))],p)

def ec_add(P:Point,Q:Point,p:int)->Point:
    if P is None:return Q
    if Q is None:return P
    x,y=P;u,v=Q
    if x==u:
        if (y+v)%p==0:return None
        s=3*x*x*pow(2*y,-1,p)%p
    else:s=(v-y)*pow(u-x,-1,p)%p
    z=(s*s-x-u)%p
    return z,(s*(x-z)-y)%p

def ec_sum(points:list[tuple[int,int]],p:int)->Point:
    R=None
    for P in points:R=ec_add(R,P,p)
    return R

def ec_mul(k:int,P:Point,p:int)->Point:
    if k<0:return ec_mul(-k,None if P is None else(P[0],-P[1]%p),p)
    R=None
    while k:
        if k&1:R=ec_add(R,P,p)
        P=ec_add(P,P,p);k>>=1
    return R

def cancel_pairs(points:list[tuple[int,int]],p:int)->tuple[list[tuple[int,int]],int]:
    C=Counter(points);out=[];removed=0
    for x in sorted(set(x for x,y in C)):
        ys=sorted({min(y,p-y) for xx,y in C if xx==x})
        if len(ys)!=1 or ys[0]==0:raise ValueError('not ordinary curve points')
        y=ys[0];c,d=C[(x,y)],C[(x,p-y)]
        removed+=min(c,d)
        out.extend([(x,y)]*max(c-d,0));out.extend([(x,p-y)]*max(d-c,0))
    assert len(out)+2*removed==len(points)
    return out,removed

def nullspace(M:list[list[int]],p:int)->list[list[int]]:
    if not M:return []
    A=[[x%p for x in r]for r in M];n=len(A[0]);row=0;piv=[]
    for col in range(n):
        t=next((t for t in range(row,len(A)) if A[t][col]),None)
        if t is None:continue
        A[row],A[t]=A[t],A[row];iv=pow(A[row][col],-1,p)
        A[row]=[x*iv%p for x in A[row]]
        for j in range(len(A)):
            if j!=row and A[j][col]:
                c=A[j][col];A[j]=[(x-c*y)%p for x,y in zip(A[j],A[row])]
        piv.append(col);row+=1
        if row==len(A):break
    free=[j for j in range(n)if j not in piv];basis=[]
    for f in free:
        v=[0]*n;v[f]=1
        for i,c in enumerate(piv):v[c]=-A[i][f]%p
        basis.append(v)
    return basis

def y_series(x:int,y:int,length:int,p:int)->list[int]:
    if not y:raise ValueError('ramified x-coordinate')
    coeff=[y];f=[(x**3+7)%p,3*x*x%p,3*x%p,1]
    for k in range(1,length):
        s=sum(coeff[i]*coeff[k-i] for i in range(1,k))
        coeff.append(((f[k] if k<len(f) else 0)-s)*pow(2*y,-1,p)%p)
    return coeff

def jet_rows(P:tuple[int,int],multiplicity:int,s:int,p:int)->list[list[int]]:
    x,y=P;ys=y_series(x,y,multiplicity,p);rows=[]
    for k in range(multiplicity):
        aa=[math.comb(i,k)*pow(x,i-k,p)%p if i>=k else 0 for i in range(s+1)]
        bb=[sum(math.comb(j,l)*pow(x,j-l,p)*ys[k-l]
                  for l in range(min(j,k)+1))%p for j in range(s)]
        rows.append(aa+bb)
    return rows

def interpolate_certificate(points:list[tuple[int,int]],R:tuple[int,int],p:int,D:int)->dict:
    """Convert an EXISTING non-cancelling witness to a normalized certificate."""
    q=len(points)
    if q<2 or q>16 or q%2 or p<=17:raise ValueError('unsupported length or characteristic')
    if D<=0 or (p-1)%D:raise ValueError('D must divide p-1')
    r,z=R
    if pow(r,D,p)==1:raise ValueError('target is in the separate factor-base branch')
    if ec_sum(points,p)!=R:raise ValueError('incorrect supplied witness')
    C=Counter(points)
    for P in C:
        x,y=P
        if (x,-y%p) in C:raise ValueError('cancel conjugate pairs first')
        if y==0 or (y*y-x**3-7)%p or pow(x,D,p)!=1:raise ValueError('bad factor point')
    M=[];s=q//2
    for P,c in sorted(C.items()):M.extend(jet_rows(P,c,s,p))
    M.extend(jet_rows((r,-z%p),1,s,p))
    ns=nullspace(M,p)
    if len(ns)!=1 or not ns[0][-1]:raise ValueError('unexpected interpolation rank/pole order')
    v=[a*pow(ns[0][-1],-1,p)%p for a in ns[0]];A=tr(v[:s+1],p);B=tr(v[s+1:],p)
    N=ps(pm([7,0,0,1],pm(B,B,p),p),pm(A,A,p),p)
    g,remainder=pd(N,[-r,1],p)
    if remainder!=[0]:raise ValueError('target constraint failed')
    return {'p':p,'D':D,'q':q,'R':list(R),'A':A,'B':B,'g':g,
            'generation':'INTERPOLATION_FROM_EXISTING_WITNESS_NOT_NEW_TARGET_SEARCH',
            'interpolation_nullity':len(ns),'matrix_rows':len(M),'matrix_columns':len(M[0])}

def split_linear_roots(f:Poly,p:int)->list[int]:
    """Las Vegas splitting of a square-free polynomial that splits over F_p.
    Deterministic PRNG seed is for reproducibility, not a worst-case guarantee.
    Raises on an unsplit component after a generous explicit attempt limit.
    """
    f=monic(f,p)
    if len(f)<=1:return []
    if pgcd(f,deriv(f,p),p)!=[1]:raise ValueError('square-free input required')
    if ps(ppow([0,1],p,f,p),mod([0,1],f,p),p)!=[0]:raise ValueError('not split over base field')
    seed=int.from_bytes(hashlib.sha256(json.dumps([p,f]).encode()).digest(),'big')
    rng=random.Random(seed);stack=[f];roots=[]
    while stack:
        h=stack.pop();d=len(h)-1
        if d==1:roots.append(-h[0]*pow(h[1],-1,p)%p);continue
        for _ in range(256):
            a=[rng.randrange(p) for _ in range(d)]
            z=pgcd(h,a,p)
            if not 1<len(z)<len(h):z=pgcd(h,ps(ppow(a,(p-1)//2,h,p),[1],p),p)
            if 1<len(z)<len(h):
                quo,rem=pd(h,z,p)
                if rem!=[0]:raise ArithmeticError('split division failure')
                stack.extend([monic(z,p),monic(quo,p)]);break
        else:raise RuntimeError('randomized root splitting exceeded attempt guard')
    if len(roots)!=len(set(roots)):raise ArithmeticError('duplicate square-free roots')
    return sorted(roots)

def verify_and_recover(cert:dict)->list[tuple[int,int]]:
    """Validate the norm certificate, then recover all q points without prior roots."""
    p=int(cert['p']);D=int(cert['D']);q=int(cert['q']);R=tuple(map(int,cert['R']))
    if p<=17 or p in (2,3,7) or q not in range(2,17,2) or D<=0 or (p-1)%D:
        raise ValueError('invalid domain parameters')
    r,z=R
    if not(0<=r<p and 0<z<p) or (z*z-r**3-7)%p or pow(r,D,p)==1:
        raise ValueError('invalid target or separately handled factor-base target')
    A=tr(list(map(int,cert['A'])),p);B=tr(list(map(int,cert['B'])),p);g=tr(list(map(int,cert['g'])),p)
    s=q//2
    if len(A)>s+1 or len(B)!=s or B[-1]!=1 or len(g)!=q+1 or g[-1]!=1:
        raise ValueError('degree/normalization failure')
    if (pe(A,r,p)-z*pe(B,r,p))%p:raise ValueError('wrong target sign')
    N=ps(pm([7,0,0,1],pm(B,B,p),p),pm(A,A,p),p)
    if N!=pm([-r,1],g,p):raise ValueError('norm identity failure')
    if pgcd(g,B,p)!=[1]:raise ValueError('common factor would permit conjugate/extension pairs')
    h=ps(ppow([0,1],D,g,p),[1],p)
    if ppow(h,q,g,p)!=[0]:raise ValueError('root support outside H')
    radical,rem=pd(g,pgcd(g,deriv(g,p),p),p)
    if rem!=[0]:raise ArithmeticError('radical construction failure')
    xs=split_linear_roots(radical,p);points=[];remaining=g[:]
    for x in xs:
        if pow(x,D,p)!=1 or pe(B,x,p)==0:raise ValueError('bad recovered root')
        y=-pe(A,x,p)*pow(pe(B,x,p),-1,p)%p
        if y==0 or (y*y-x**3-7)%p:raise ValueError('root has no accepted rational lift')
        multiplicity=0
        while True:
            quo,remainder=pd(remaining,[-x,1],p)
            if remainder!=[0]:break
            remaining=quo;multiplicity+=1
        points.extend([(x,y)]*multiplicity)
    if len(points)!=q or remaining!=[1] or ec_sum(points,p)!=R:
        raise ValueError('final exact recovery failure')
    return points

if __name__=='__main__':
    import argparse,pathlib
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('certificate',type=pathlib.Path)
    a=ap.parse_args();c=json.loads(a.certificate.read_text());pts=verify_and_recover(c)
    print(json.dumps({'status':'VALID','points':pts,'not_claimed':'search for a new target'},indent=2))
