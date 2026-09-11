#!/usr/bin/env python3
"""A complete target-aware q=2 norm solver by univariate polynomial gcd.
This is a control algorithm, not a new q=16 solver. It takes no discrete logs,
no known decomposition, and no factor-base list as input.
"""
import norm_bridge as nb

def solve(p:int,D:int,R:tuple[int,int])->dict:
    r,z=R
    if D<=0 or (p-1)%D or pow(r,D,p)==1:raise ValueError('outside this chart')
    # g=X^2+u(t)X+v(t), t is the free slope parameter.
    u=[r,0,-1];v=[r*r%p,-2*z%p,r]
    # X^j mod g = a_j(t) X+b_j(t).
    a,b=[0],[1]
    for j in range(1,D+1):
        a,b=nb.ps(b,nb.pm(a,u,p),p),nb.scale(nb.pm(a,v,p),-1,p)
    assert len(a)-1==2*(D-1)
    h=nb.ps(b,[1],p);aa=nb.pm(a,a,p)
    e1=nb.ps(nb.scale(nb.pm(a,h,p),2,p),nb.pm(aa,u,p),p)
    e0=nb.ps(nb.pm(h,h,p),nb.pm(aa,v,p),p)
    common=nb.pgcd(e1,e0,p)
    # Retain F_p roots exactly, including tangent/repeated-coordinate cases.
    linear=nb.pgcd(common,nb.ps(nb.ppow([0,1],p,common,p),[0,1],p),p) if len(common)>1 else [1]
    slopes=nb.split_linear_roots(linear,p) if len(linear)>1 else []
    certificates=[]
    for t in slopes:
        A=[(z-r*t)%p,t];B=[1];g=[(r*r+r*t*t-2*z*t)%p,(r-t*t)%p,1]
        c={'p':p,'D':D,'q':2,'R':list(R),'A':A,'B':B,'g':g,
           'generation':'UNPLANTED_Q2_POLYNOMIAL_GCD_SEARCH'}
        got=nb.verify_and_recover(c)
        c['recovered_points']=[list(P)for P in got];c['distinct_x_count']=len(set(x for x,y in got))
        certificates.append(c)
    return {'certificates':certificates,'a_D_degree':len(a)-1,
            'membership_equation_degrees':[len(e1)-1,len(e0)-1],
            'gcd_degree':len(common)-1,'base_field_slope_count':len(slopes)}
