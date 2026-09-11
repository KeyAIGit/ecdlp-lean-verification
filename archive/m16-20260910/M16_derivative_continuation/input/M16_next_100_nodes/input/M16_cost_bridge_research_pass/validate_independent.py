#!/usr/bin/env python3
"""Independent arithmetic/certificate validator; does not import producers."""
from pathlib import Path
import json, math, hashlib
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
 z2=Z*Z%p;w2=W*W%p
 u1=X*w2%p;u2=U*z2%p;s1=Y*W*w2%p;s2=V*Z*z2%p
 if u1==u2:return jd(A,p) if s1==s2 else (0,1,0)
 h=(u2-u1)%p;i=(2*h)**2%p;j=h*i%p;r=2*(s2-s1)%p;v=u1*i%p
 xx=(r*r-j-2*v)%p
 return xx,(r*(v-xx)-2*s1*j)%p,((Z+W)**2-z2-w2)*h%p

def aff(A,p):
 X,Y,Z=A
 if not Z:return None
 inv=pow(Z,-1,p)
 return (X*inv*inv%p,Y*inv*inv*inv%p)

def jm(k,P,p):
 A=(0,1,0);B=(P[0],P[1],1)
 while k:
  if k&1:A=ja(A,B,p)
  B=jd(B,p);k//=2
 return aff(A,p)

def sumpts(points,p):
 A=(0,1,0)
 for x,y in points:A=ja(A,(x,y,1),p)
 return aff(A,p)

bounds=json.loads((HERE/'exact_cost_bounds.json').read_text());B=bounds['glv_orbits'];n=int(bounds['n'])
# Independent logarithmic-derivative recurrence, not binomial expansion.
f=[1]
for k in range(20):
 num=(6*B+1-3*k)*f[k]
 if k>=1:num+=(6*B+3*k+1)*f[k-1]
 if k>=2:num+=(k-1)*f[k-2]
 assert num%(k+1)==0
 f.append(num//(k+1))
for row in bounds['rows']:
 m=row['m'];assert int(row['glv_coefficient_vectors'])==(6*B if m==1 else f[m])
 assert int(row['raw_multisets'])==math.comb(6*B+m-1,m)
cert=json.loads((HERE/'permutation_cost_certificate.json').read_text());p=int(cert['p']);D=cert['D']
pts=[tuple(map(int,P)) for P in cert['points']];target=tuple(map(int,cert['target']))
assert len(pts)==len(set(x for x,y in pts))==16
assert all(y*y%p==(x**3+7)%p and pow(x,D,p)==1 for x,y in pts)
assert sumpts(pts,p)==target
assert int(cert['mathematical_distinct_ordered_x_tuples'])==math.prod(range(1,17))
# Divisor verification via independent evaluations; distinct roots + degree16 monic.
g=list(map(int,cert['divisor_monic_coefficients_low_to_high']))
assert len(g)==17 and g[-1]==1
for x,y in pts:
 v=0
 for c in reversed(g):v=(v*x+c)%p
 assert v==0
# A mutation must not pass the equality test.
assert sumpts(pts,p)!=((target[0]+1)%p,target[1])
# Every reported toy witness revalidated by projective arithmetic, including target generation.
records=json.loads((HERE/'toy_yield_and_search.json').read_text())['records'];total=0
cache={}
for rec in records:
 if rec.get('status')=='EMPTY_FACTORBASE':continue
 p=rec['p'];D=rec['D']
 if p not in cache:
  ys={}
  for y in range(p):ys.setdefault(y*y%p,[]).append(y)
  allpoints=sorted((x,y) for x in range(p) for y in ys.get((x**3+7)%p,[]))
  assert len(allpoints)+1==rec['n'];cache[p]=allpoints
 allpoints=cache[p];G=allpoints[0]
 F=[P for P in allpoints if pow(P[0],D,p)==1]
 assert len(F)==rec['signed_factorbase_size']
 assert hashlib.sha256(json.dumps(F,separators=(',',':')).encode()).hexdigest()==rec['factorbase_points_sha256']
 assert len(rec['witnesses'])==rec['search_successes']
 for wit in rec['witnesses']:
  chosen=[F[i] for i in wit['factorbase_indices']]
  assert len(chosen)==16
  assert sumpts(chosen,p)==jm(wit['target_scalar_for_audit_only'],G,p)
  total+=1
out={'status':'PASS','bound_rows_checked':20,'coefficient_count_check':'independent differential recurrence',
 'secp256k1_structural_witness':'projective arithmetic PASS',
 'divisor_membership':'independent Horner evaluations PASS',
 'negative_mutation_test':'PASS','toy_witnesses_checked':total,
 'toy_validation':'independent projective addition and scalar multiplication',
 'coverage_validation':'producer separately cross-checks all seven smallest-curve sumsets using explicit Python sets',
 'not_claimed':['Lean verification','256-bit uniform-target M16 solver','solving-degree bound','asymptotic acceleration']}
# Validate all successful end-to-end matrix recoveries independently.
e2e=json.loads((HERE/'toy_end_to_end.json').read_text())['records']
checked_e2e=0
for r in e2e:
 if r['status']!='RECOVERED':continue
 p,n,D=r['p'],r['n'],r['D'];C,w,a,b=r['C'],r['w'],r['a'],r['b']
 assert any(w)
 assert all(sum(w[i]*C[i][j] for i in range(len(w)))%n==0 for j in range(len(C[0])))
 wb=sum(x*y for x,y in zip(w,b))%n;wa=sum(x*y for x,y in zip(w,a))%n
 assert wb!=0 and (-wa*pow(wb,-1,n))%n==r['recovered']==r['known_secret_test_harness_only']
 allpoints=cache[p];G=allpoints[0];F=[P for P in allpoints if pow(P[0],D,p)==1]
 beta=r['glv_beta'];reps=set()
 for x,y in F:
  orbit=[(x*pow(beta,j,p)%p,sign*y%p) for j in range(3) for sign in (1,-1)]
  reps.add(min(orbit))
 reps=sorted(reps);assert len(reps)==r['columns']
 src=next(t for t in records if t['p']==p and t['D']==D)
 for row,wit in zip(C,src['witnesses']):
  terms=[jm(c,rep,p) for c,rep in zip(row,reps) if c]
  assert sumpts([T for T in terms if T is not None],p)==jm(wit['target_scalar_for_audit_only'],G,p)
 checked_e2e+=1
out['end_to_end_matrix_recoveries_checked']=checked_e2e
(HERE/'independent_validation.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
