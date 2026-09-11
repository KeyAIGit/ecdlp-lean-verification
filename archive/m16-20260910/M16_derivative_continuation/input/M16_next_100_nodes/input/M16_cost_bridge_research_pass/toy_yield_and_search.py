#!/usr/bin/env python3
"""Exhaustive small-field M16 coverage and target-blind point-list search.

The complete discrete-log table is used ONLY by ground-truth/validation.
The solver is passed curve arithmetic, factor-base POINTS and target POINT.
No secp256k1 solving performance is inferred from these small curves.
"""
from __future__ import annotations
import hashlib, json, math, random, time
from pathlib import Path
Point=tuple[int,int]|None
CONFIGS=[(4159,4243,[6,18,42,54,66,126,198]),(16879,17107,[6,174]),(64303,63799,[6,42]),(257107,257869,[6])]
SEED=20260910
N_TARGETS=64
class Curve:
 def __init__(self,p): self.p=p; self.calls=0
 def neg(self,P): return None if P is None else (P[0],-P[1]%self.p)
 def add(self,P,Q):
  self.calls+=1
  if P is None:return Q
  if Q is None:return P
  p=self.p; x,y=P; u,v=Q
  if x==u:
   if (y+v)%p==0:return None
   s=3*x*x*pow(2*y,-1,p)%p
  else:s=(v-y)*pow(u-x,-1,p)%p
  z=(s*s-x-u)%p
  return z,(s*(x-z)-y)%p
 def mul(self,k,P):
  R=None
  while k:
   if k&1:R=self.add(R,P)
   P=self.add(P,P);k>>=1
  return R

def prime(n):
 if n<2:return False
 return all(n%d for d in range(2,math.isqrt(n)+1))

def roots_and_points(p):
 roots={y*y%p:y for y in range(1,(p+1)//2)}
 pts=[]
 for x in range(p):
  v=(x*x*x+7)%p
  if v==0:pts.append((x,0))
  elif v in roots:
   y=roots[v];pts.extend([(x,y),(x,p-y)])
 return pts

def coverage(n,logs,m=16):
 mask=(1<<n)-1; states=1; sizes=[]
 for _ in range(m):
  out=0
  for s in logs:
   out|=((states<<s)&mask)|(states>>(n-s))
  states=out;sizes.append(states.bit_count())
 return states,sizes

def sample_half(curve,F,rng):
 ids=[rng.randrange(len(F)) for _ in range(8)]
 point=F[ids[0]]
 for i in ids[1:]:point=curve.add(point,F[i])
 return point,ids

def build_left(curve,F,L,rng):
 tab={}
 for _ in range(L):
  P,ids=sample_half(curve,F,rng)
  tab.setdefault(P,ids)
 return tab

def solve(curve,F,target,L,left,rng):
 # Does NOT receive generator, n, scalar of target, or factor-base logs.
 for _ in range(L):
  right,ids=sample_half(curve,F,rng)
  needed=curve.add(target,curve.neg(right))
  if needed in left:return left[needed]+ids
 return None

def bsgs_all(curve,G,targets,n):
 L=math.isqrt(n)+1;start=curve.calls
 tab={};P=None
 for j in range(L):
  tab.setdefault(P,j);P=curve.add(P,G)
 step=curve.neg(P);prep=curve.calls-start;start=curve.calls; recovered=[]
 for target in targets:
  R=target
  for i in range(L+1):
   if R in tab:
    recovered.append((i*L+tab[R])%n);break
   R=curve.add(R,step)
  else:raise AssertionError('BSGS failed')
 return prep,curve.calls-start,recovered

def main():
 records=[]
 for p,n,Ds in CONFIGS:
  assert prime(p) and prime(n)
  curve=Curve(p);pts=roots_and_points(p)
  assert len(pts)+1==n
  G=min(pts);byk=[];P=None
  for _ in range(n):byk.append(P);P=curve.add(P,G)
  assert P is None and len(set(byk))==n
  point_log={P:k for k,P in enumerate(byk)}
  target_rng=random.Random(SEED+p)
  ks=[target_rng.randrange(n) for _ in range(N_TARGETS)]
  targets=[byk[k] for k in ks]
  refprep,refcalls,found=bsgs_all(curve,G,targets,n)
  assert found==ks
  for D in Ds:
   assert (p-1)%D==0
   F=sorted(P for P in pts if pow(P[0],D,p)==1)
   if not F:
    records.append({'p':p,'n':n,'D':D,'status':'EMPTY_FACTORBASE'});continue
   logs=[point_log[P] for P in F]
   assert len(F)%6==0
   tic=time.perf_counter();support,sizes=coverage(n,logs);support_seconds=time.perf_counter()-tic
   # Independent set-sum replay for smallest curve, up to all 16 levels.
   if p==4159:
    S={0}
    for m in range(16):
     S={(s+a)%n for s in S for a in logs}
     assert len(S)==sizes[m]
    assert S=={k for k in range(n) if support>>k&1}
   L=math.isqrt(n)+1;rng=random.Random(SEED+p*1000+D)
   start=curve.calls;left=build_left(curve,F,L,rng);prep=curve.calls-start
   found_count=0;calls=0;validation_calls=0;witnesses=[]
   eligible=sum((support>>k)&1 for k in ks)
   for k,R in zip(ks,targets):
    start=curve.calls;ans=solve(curve,F,R,L,left,rng);calls+=curve.calls-start
    if ans is not None:
     assert len(ans)==16
     assert sum(logs[i] for i in ans)%n==k
     before=curve.calls;T=None
     for i in reversed(ans):T=curve.add(T,F[i])
     validation_calls+=curve.calls-before
     assert T==R and (support>>k)&1
     witnesses.append({'target_scalar_for_audit_only':k,'factorbase_indices':ans})
     found_count+=1
   rec={'p':p,'n':n,'D':D,'signed_factorbase_size':len(F),'glv_orbits':len(F)//6,
    'coverage_counts_m1_to_m16':sizes,'exact_coverage_m16':sizes[-1]/n,
    'uniform_targets':N_TARGETS,'representable_targets':eligible,'search_successes':found_count,
    'list_length':L,'unique_left_entries':len(left),'search_precomputation_add_calls':prep,
    'search_online_add_calls':calls,'validation_add_calls':validation_calls,
    'search_add_calls_per_success_including_failed_targets':None if found_count==0 else (prep+calls+validation_calls)/found_count,
    'reference_bsgs_precomputation_add_calls':refprep,'reference_bsgs_online_add_calls':refcalls,
    'reference_bsgs_add_calls_per_success':(refprep+refcalls)/N_TARGETS,
    'coverage_runtime_seconds_not_solver_cost':support_seconds,
    'factorbase_points_sha256':hashlib.sha256(json.dumps(F,separators=(',',':')).encode()).hexdigest(),
    'targets_for_audit_only':ks,'witnesses':witnesses}
   records.append(rec)
   print(p,D,len(F),sizes[-1],round(sizes[-1]/n,6),f'{found_count}/{N_TARGETS}',flush=True)
 out={'seed':SEED,'records':records,'scope':{
 'coverage':'exact exhaustive on listed prime-order toy curves, repetitions permitted',
 'search':'randomized 8+8 point-list collision search, not a Semaev/PKC polynomial solver',
 'targets':'uniform before solving, not sums planted in the factor base',
 'oracle':'complete group enumeration used by coverage and validation, excluded from solver inputs; not a practical algorithm',
 'cost':'counts actual add routine calls, incl precomputation and failed queries; not calibrated to field work or wall time',
 'timing':'coverage_runtime is not claimed as relation-search runtime',
 'reference':'BSGS solves DLP, not factorbase decomposition; separate generic cost reference',
 'limitations':'small curves change D and arithmetic, not asymptotic evidence for secp256k1; no polynomial-solving degree measured'}}
 Path(__file__).with_name('toy_yield_and_search.json').write_text(json.dumps(out,indent=2))
if __name__=='__main__':main()
