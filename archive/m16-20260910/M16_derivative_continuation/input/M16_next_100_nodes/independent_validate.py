#!/usr/bin/env python3
"""Independent verifier: no import of norm_bridge or producer programs.
Polynomial arithmetic is delegated to SymPy; point arithmetic is Jacobian.
"""
from pathlib import Path
from collections import Counter
import json, math
import sympy as sp
HERE=Path(__file__).resolve().parent

def jd(A,p):
    X,Y,Z=A
    if Z==0 or Y==0:return (0,1,0)
    aa=X*X%p;bb=Y*Y%p;cc=bb*bb%p;dd=2*((X+bb)**2-aa-cc)%p
    ee=3*aa%p;ff=ee*ee%p;xx=(ff-2*dd)%p
    return xx,(ee*(dd-xx)-8*cc)%p,2*Y*Z%p

def ja(A,B,p):
    X,Y,Z=A;U,V,W=B
    if Z==0:return B
    if W==0:return A
    z2=Z*Z%p;w2=W*W%p;u1=X*w2%p;u2=U*z2%p;s1=Y*W*w2%p;s2=V*Z*z2%p
    if u1==u2:return jd(A,p) if s1==s2 else (0,1,0)
    h=(u2-u1)%p;i=(2*h)**2%p;j=h*i%p;r=2*(s2-s1)%p;v=u1*i%p
    xx=(r*r-j-2*v)%p
    return xx,(r*(v-xx)-2*s1*j)%p,((Z+W)**2-z2-w2)*h%p

def sumj(points,p):
    A=(0,1,0)
    for x,y in points:A=ja(A,(x,y,1),p)
    X,Y,Z=A
    if not Z:return None
    inv=pow(Z,-1,p)
    return X*inv*inv%p,Y*inv*inv*inv%p

def check(c):
    p,D,q=c['p'],c['D'],c['q'];r,z=c['R'];x=sp.Symbol('x')
    poly=lambda cs:sp.Poly.from_list(list(reversed(cs)),gens=x,modulus=p)
    A,B,g=poly(c['A']),poly(c['B']),poly(c['g'])
    f=poly([7,0,0,1]);xr=poly([-r,1])
    assert (f*B*B-A*A-xr*g).is_zero
    assert int(A.eval(r)-z*B.eval(r))%p==0
    assert A.degree()<=q//2 and B.degree()==q//2-1 and int(B.LC())%p==1
    assert g.degree()==q and int(g.LC())%p==1
    assert sp.gcd(B,g).degree()==0
    got=[tuple(P)for P in c['recovered_points']];assert len(got)==q
    C=Counter(got);prod=poly([1]);xx=set()
    for (a,b),m in C.items():
        assert a not in xx;xx.add(a)
        assert pow(a,D,p)==1 and b!=0 and (b*b-a*a*a-7)%p==0
        assert int(A.eval(a)+b*B.eval(a))%p==0
        assert int(B.eval(a))%p!=0
        prod*=poly([-a,1])**m
    assert prod==g and len(xx)==c['distinct_x_count']
    assert sumj(got,p)==(r,z)
    assert pow(r,D,p)!=1 and (z*z-r*r*r-7)%p==0
    # Independent inverse in F_p[x]/g verifies multiplicity-sensitive rational lifting.
    inv=sp.invert(B,g)
    Y=(-A*inv).rem(g)
    assert (Y*Y-f).rem(g).is_zero

def main():
    data=json.loads((HERE/'certificate_suite.json').read_text());count=0
    for c in data['toys']+data['planted_256']:check(c);count+=1
    b=json.loads((HERE/'quantitative_bounds.json').read_text());B=b['B'];n=int(b['n']);f=[1]
    for k in range(16):
        val=(6*B+1-3*k)*f[k]
        if k>=1:val+=(6*B+3*k+1)*f[k-1]
        if k>=2:val+=(k-1)*f[k-2]
        assert val%(k+1)==0;f.append(val//(k+1))
    assert f[14]==int(b['K14']) and f[16]==int(b['K16'])
    # Truncated polynomial powering, independent of the closed-form count.
    def mul(a,c):
        d=[0]*17
        for i,u in enumerate(a):
            for j,v in enumerate(c):
                if i+j<=16:d[i+j]+=u*v
        return d
    a=[1];base=[1,6,6];exp=B
    while exp:
        if exp&1:a=mul(a,base)
        exp//=2
        if exp:base=mul(base,base)
    repeated=f[16]-6**15*math.comb(B,15)-a[16]
    assert repeated==int(b['squarefree_chart_absolute_coverage_loss']['numerator'])
    out={'status':'PASS','certificates_checked':count,'toy_certificates':len(data['toys']),
         'planted_256_certificates':len(data['planted_256']),
         'polynomial_implementation':'SymPy, independent of producer',
         'group_implementation':'Jacobian, independent of producer affine arithmetic',
         'quantitative_counts':'independent differential recurrence and truncated powering',
         'not_claimed':['Lean proof','new-target 256-bit search','complexity improvement']}
    (HERE/'independent_validation.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()
