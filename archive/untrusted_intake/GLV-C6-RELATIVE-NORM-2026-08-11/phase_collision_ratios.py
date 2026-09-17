#!/usr/bin/env python3
"""Exact C6 phase-collision ratio enumeration for secp256k1's scalar group.

No point target and no discrete logarithm are used. The calculation is entirely
inside Z/nZ using the published GLV eigenvalue lambda.
"""
from __future__ import annotations
import json, math
from pathlib import Path

HERE=Path(__file__).resolve().parent
N=int('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141',16)
LAMBDA=int('5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72',16)

def hset(n,lam):
    return sorted({(s*pow(lam,e,n))%n for e in range(3) for s in (1,-1)})

def ratios(n,lam):
    H=hset(n,lam); out={}
    for h1 in H:
      for h2 in H:
        if h1==h2: continue
        for g in H:
          den=(h1-g*h2)%n; num=(g-1)%n
          if den==0: continue
          r=num*pow(den,-1,n)%n
          if r==0: continue
          assert ((1-g)+(h1-g*h2)*r)%n==0
          out.setdefault(r,[]).append((h1,h2,g))
    return H,out

def main():
    assert (LAMBDA*LAMBDA+LAMBDA+1)%N==0
    H,R=ratios(N,LAMBDA)
    same=sorted(set(R)&set(H)); distinct=sorted(set(R)-set(H))
    denom=N-1-len(H)
    result={
      'scope':'scalar-ring structural calculation only; no ECDLP target',
      'group_order_n_hex':hex(N),
      'lambda_hex':hex(LAMBDA),
      'lambda_relation_mod_n':(LAMBDA*LAMBDA+LAMBDA+1)%N,
      'H_size':len(H),
      'H_hex':[hex(x) for x in H],
      'collision_equation':'q(P+h1 Q)=q(P+h2 Q) implies r=(g-1)/(h1-g*h2) for Q=[r]P and g,h1,h2 in H',
      'all_nonzero_collision_ratios':len(R),
      'same_orbit_ratios':len(same),
      'distinct_orbit_collision_ratios':len(distinct),
      'distinct_orbit_ratio_hex':[hex(x) for x in distinct],
      'uniform_ratio_exact_upper_fraction':f'{len(distinct)}/{denom}',
      'uniform_ratio_probability_upper_bound':len(distinct)/denom,
      'negative_log2_probability_bound':-math.log2(len(distinct)/denom),
      'interpretation':'For a fixed nonzero P and a uniformly random Q outside its C6 orbit, only 36 scalar ratios can cause a local phase collision.',
      'limitation':'Factor-base points are structured, not proven uniform; this is a collision-locus count, not an attack complexity theorem.'
    }
    (HERE/'phase_collision_ratios_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['lambda_relation_mod_n','H_size','all_nonzero_collision_ratios','same_orbit_ratios','distinct_orbit_collision_ratios','negative_log2_probability_bound']},indent=2))

if __name__=='__main__':main()
