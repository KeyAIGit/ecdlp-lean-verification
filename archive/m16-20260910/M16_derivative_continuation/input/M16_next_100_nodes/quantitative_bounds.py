#!/usr/bin/env python3
"""Exact counting bounds. No uniformity of images in E(F_p) is assumed."""
from pathlib import Path
from fractions import Fraction
from itertools import product
import json,math
P=2**256-2**32-977
N=int('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141',16)
B=94509;U=283527;SIZE=567054;D=564522
UNITS=[(1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1)]
def norm(v):a,b=v;return max(abs(a),abs(b),abs(a-b))
def k_counts(B,m):
    # Shell convolution independent of the previous pass's differential recurrence.
    f=[1]+[0]*m
    # Exact integer binomial expansion of theta(t)^B /(1-t):
    # theta = 1 + 6t/(1-t)^2.
    return [sum(math.comb(B,j)*6**j*math.comb(m0+j,2*j)
                for j in range(min(B,m0)+1)) for m0 in range(m+1)]
def repeated_formal_count(B,m):
    if m<4:raise ValueError('formula stated for m>=4')
    K=k_counts(B,m)[m]
    shell_one=6**(m-1)*math.comb(B,m-1) if B>=m-1 else 0
    shell_two=sum(math.comb(B,a)*math.comb(B-a,m-2*a)*6**(m-a)
                  for a in range(m//2+1) if a<=B and 0<=m-2*a<=B-a)
    return K-shell_one-shell_two

def main():
    ks=k_counts(B,20)
    old=json.loads((Path(__file__).parent/'input/M16_cost_bridge_research_pass/exact_cost_bounds.json').read_text())
    for r in old['rows']:
        m=r['m'];assert int(r['glv_coefficient_vectors'])==(6*B if m==1 else ks[m])
    # Independent local geometry check through radius 32.
    local=0
    for a in range(-32,33):
        for b in range(-32,33):
            v=(a,b);r=norm(v)
            if r>32:continue
            best=r-min(norm((a-2*u,b-2*v0))for u,v0 in UNITS)
            expected=-2 if r==0 else 0 if r==1 else 1 if r==2 and (a,b)not in[(2*u,2*v0)for u,v0 in UNITS] else 2
            assert best==expected;local+=1
    # Direct union enumeration on two independent GLV-coordinate lattices.
    brute=[]
    for m in (4,5,6,8,10,12,16):
        pts=[(a,b)for a in range(-m,m+1)for b in range(-m,m+1)if norm((a,b))<=m]
        counted=0;allcount=0
        for v in pts:
            nv=norm(v)
            for w in pts:
                nw=norm(w)
                if nv+nw>m:continue
                allcount+=1
                hit=any(norm((v[0]-2*a,v[1]-2*b))+nw<=m-2 for a,b in UNITS) or any(norm((w[0]-2*a,w[1]-2*b))+nv<=m-2 for a,b in UNITS)
                counted+=int(hit)
        assert allcount==k_counts(2,m)[m]
        assert counted==repeated_formal_count(2,m)
        brute.append({'B':2,'m':m,'all_formal_vectors':allcount,'union_count':counted})
    bad=Fraction(repeated_formal_count(B,16),N)
    simple=Fraction(SIZE*ks[14],N)
    cancel=Fraction(ks[14],N)
    log_random=math.log2(math.comb(SIZE+15,16))-math.log2(N-SIZE-1)-15*math.log2(P)
    log_random_distinct=math.log2(math.comb(U,16))+16-math.log2(N-SIZE-1)-15*math.log2(P)
    out={'status':'PASS','p':str(P),'n':str(N),'D':D,'B':B,'U':U,'signed_size':SIZE,
         'K13':str(ks[13]),'K14':str(ks[14]),'K16':str(ks[16]),
         'non_base_field_noncancelling_exception_upper':{'numerator':str(ks[13]),'denominator':str(N),'upper':ks[13]/N,'scope':'Existence of a nonrational noncancelling norm solution; not rational solution probability.'},
         'q2_true_D_exact_remainder_slope_degree':2*D-2,
         'noncancelling_chart_absolute_coverage_loss':{'numerator':str(cancel.numerator),'denominator':str(cancel.denominator),'upper':float(cancel)},
         'squarefree_chart_absolute_coverage_loss':{'numerator':str(bad.numerator),'denominator':str(bad.denominator),'upper':float(bad),'coarser_union_upper':float(simple)},
         'random_15_coefficients_average_success_log2_upper':log_random,
         'random_squarefree_15_coefficients_average_success_log2_upper':log_random_distinct,
         'local_hex_lattice_vectors_checked':local,'direct_two_orbit_union_checks':brute,
         'scope':['Coverage losses are absolute probabilities, not conditional percentages of successful targets.',
                  'The K16/n mean is not an existence lower bound.',
                  'Random coefficient bound is for uniform parameters and uniform targets outside the separate branches.',
                  'Neither counting argument establishes a general root-finding lower bound.']}
    Path(__file__).with_name('quantitative_bounds.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()
