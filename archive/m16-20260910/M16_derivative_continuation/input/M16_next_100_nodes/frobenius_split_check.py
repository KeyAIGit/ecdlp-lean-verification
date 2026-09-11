#!/usr/bin/env python3
"""Exact F_{163^2} counterexample and checks for the Frobenius splitting lemma.
This is PLANTED and verifies the exceptional mechanism; no target-yield claim.
"""
from pathlib import Path
from itertools import combinations
import json
import norm_bridge as nb
from run_q2_benchmark import allpoints
p=163;D=9;pts=allpoints(p);n=len(pts)+1
H=[x for x in range(1,p)if pow(x,D,p)==1]
usable={x for x,y in pts if x in H};bad=[x for x in H if x not in usable]
assert n==139 and (n*(2*p+2-n))%2==1 and len(bad)==3
x0=bad[0];nu=(x0**3+7)%p;assert pow(nu,(p-1)//2,p)==p-1
zero=(0,0);one=(1,0)
def ad(a,b):return ((a[0]+b[0])%p,(a[1]+b[1])%p)
def neg(a):return(-a[0]%p,-a[1]%p)
def sub(a,b):return ad(a,neg(b))
def mu(a,b):return((a[0]*b[0]+nu*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
def inv(a):
    t=pow((a[0]*a[0]-nu*a[1]*a[1])%p,-1,p);return(a[0]*t%p,-a[1]*t%p)
def sc(k,a):return(k*a[0]%p,k*a[1]%p)
def ec(P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P;u,v=Q
    if x==u:
        if ad(y,v)==zero:return None
        slope=mu(sc(3,mu(x,x)),inv(sc(2,y)))
    else:slope=mu(sub(v,y),inv(sub(u,x)))
    z=sub(sub(mu(slope,slope),x),u)
    return z,sub(mu(slope,sub(x,z)),y)
def sm(Ps):
    out=None
    for P in Ps:out=ec(out,P)
    return out
beta=next(a for a in range(2,p)if pow(a,3,p)==1)
nonrat=[((x0*pow(beta,j,p)%p,0),(0,1))for j in range(3)]
assert {Q[0][0]for Q in nonrat}==set(bad) and sm(nonrat) is None
F=sorted((x,min(y for a,y in pts if a==x))for x in usable)
chosen=None
for Ps in combinations(F,3):
    R=nb.ec_sum(list(Ps),p)
    if R is not None and R[0] not in H:chosen=list(Ps);break
assert chosen is not None
r,z=R
# Degree-four-pole rational function for the three rational points and -R:
# A0=a0+a1*x+a2*x^2, B0=b0. Normalize a2=1.
M=[[1,x,x*x%p,y]for x,y in chosen+[(r,-z%p)]]
v=nb.nullspace(M,p);assert len(v)==1 and v[0][2]
v=[a*pow(v[0][2],-1,p)%p for a in v[0]];A0=v[:3];B0=v[3]
# (A0+y*B0)*(y-w): A=f*B0-w*A0, B=A0-w*B0.
A=[(7*B0%p,-A0[0]%p),(0,-A0[1]%p),(0,-A0[2]%p),(B0,0)]
B=[(A0[0],-B0%p),(A0[1],0),(1,0)]
def poly_mul(a,b):
    c=[zero]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]=ad(c[i+j],mu(x,y))
    return c
def evaluate(a,x):
    out=zero
    for c in reversed(a):out=ad(mu(out,x),c)
    return out
allPs=[((x,0),(y,0))for x,y in chosen]+nonrat
assert sm(allPs)==((r,0),(z,0))
for x,y in allPs:
    assert ad(evaluate(A,x),mu(y,evaluate(B,x)))==zero
    assert evaluate(B,x)!=zero
assert sub(evaluate(A,(r,0)),sc(z,evaluate(B,(r,0))))==zero
g=[1]
for x,y in chosen:g=nb.pm(g,[-x,1],p)
for Q in nonrat:g=nb.pm(g,[-Q[0][0],1],p)
assert nb.ppow([0,1],D,g,p)==[1]
FU=[1]
for x in sorted(usable):FU=nb.pm(FU,[-x,1],p)
assert nb.mod(FU,g,p)!=[0]
left=poly_mul([(7,0),zero,zero,one],poly_mul(B,B));aa=poly_mul(A,A)
for i,a in enumerate(aa):left[i]=sub(left[i],a)
right=poly_mul([(-r%p,0),one],[(a,0)for a in g]);assert left==right
# Frobenius fixes rational points and negates the imaginary-y points.
conjugate=[((x[0],-x[1]%p),(y[0],-y[1]%p))for x,y in allPs]
assert sm(conjugate)==((r,0),(z,0))
out={'status':'PASS','generation':'PLANTED_EXCEPTIONAL_Q6_OVER_Fp2','p':p,'D':D,'n':n,'group_order_Fp2':n*(2*p+2-n),
     'extension_w_square':nu,'R':R,'rational_points':chosen,'nonrational_points':nonrat,
     'A_over_Fp2':A,'B_over_Fp2':B,'g_over_Fp':g,'usable_polynomial':FU,
     'checks':['nonrational GLV triple sums to O','rational triple sums to target outside factorbase',
               'all six points have distinct x in H','norm identity','nonvanishing B at all roots',
               'full-H membership accepts; usable membership rejects',
               'Frobenius fixes target and negates nonsquare lifts'],
     'scope':'Demonstrates exceptional non-base-field norm solutions. Does not prove frequency; frequency bound is an analytic consequence.'}
Path(__file__).with_name('frobenius_split_check.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
