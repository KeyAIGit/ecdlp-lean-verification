#!/usr/bin/env python3
"""Exact finite counts and scoped bounds, not an ECDLP algorithm."""
import json, math
from fractions import Fraction
from pathlib import Path
P=2**256-2**32-977
N=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
A=567054
B=A//6

def orbit_ball_count(b:int,m:int)->int:
    # [t^m] (1+4t+t^2)^b/(1-t)^(2b+1).
    num=[]
    for s in range(m+1):
        z=0
        for k in range(s//2+1):
            j=s-2*k
            if j+k<=b:
                z+=math.comb(b,k)*math.comb(b-k,j)*4**j
        num.append(z)
    return sum(num[s]*math.comb(2*b+m-s,m-s) for s in range(m+1))

rows=[]
for m in range(1,21):
    raw=math.comb(A+m-1,m)
    # Ball formula includes zero for m=1, so exact-one count is A.
    canonical=A if m==1 else orbit_ball_count(B,m)
    bound=Fraction(min(canonical,N),N)
    rows.append({'m':m,'raw_multisets':str(raw),'glv_coefficient_vectors':str(canonical),
      'mean_vectors_per_uniform_target':float(Fraction(canonical,N)),
      'mean_raw_multisets_per_uniform_target':float(Fraction(raw,N)),
      'existence_probability_upper_bound':float(bound),
      'existence_bound_numerator':str(bound.numerator),'existence_bound_denominator':str(bound.denominator),
      'log2_reciprocal_upper_yield':max(0,math.log2(N)-math.log2(canonical)),
      'raw_to_canonical_ratio':float(Fraction(raw,canonical))})
# Independent power-series convolution for bounded b validates closed form.
for b in [1,2,3,7]:
    coeff=[1]+[0]*16
    for _ in range(b):
        coeff=[sum(coeff[i]* (1 if j==0 else 6*j) for i in range(k+1) for j in [k-i]) for k in range(17)]
    for m in range(17):
        assert sum(coeff[:m+1])==orbit_ball_count(b,m)
# Analytic one-orbit count.
for m in range(50): assert orbit_ball_count(1,m)==1+3*m*(m+1)
out={'p':str(P),'n':str(N),'signed_factorbase_size':A,'glv_orbits':B,'rows':rows,
 'one_point_completion_success_exact':str(Fraction(A,N)),
 'one_point_completion_log2_expected_trials':math.log2(N)-math.log2(A),
 'whole_relation_rejection_log2_expected_trials':math.log2(N),
 'one_output_per_query_cost_ceiling_log2':0.5*math.log2(N)-math.log2(B+1),
 'raw_8_multiset_list_log2':math.log2(math.comb(A+7,8)),
 'canonical_8_vector_list_log2':math.log2(orbit_ball_count(B,8)),
 'statuses':{'arithmetic':'exact integers; float fields are displays only',
             'probability_bound':'rigorous upper bound, not a lower bound',
             'glv_assumption':'factor base partitions into nonzero six-element orbits; known order-three automorphism',
             'one_point_completion':'target uniform and independent of chosen prefix',
             'cost_ceiling':'uncalibrated sqrt(n) reference, no constants, precomputation or linear algebra included',
             'asymptotics':'not inferred from this fixed curve'}}
Path(__file__).with_name('exact_cost_bounds.json').write_text(json.dumps(out,indent=2))
for row in rows[12:17]: print(row['m'], row['mean_vectors_per_uniform_target'], row['raw_to_canonical_ratio'], row['log2_reciprocal_upper_yield'])
print({k:v for k,v in out.items() if k not in ['rows','statuses']})
