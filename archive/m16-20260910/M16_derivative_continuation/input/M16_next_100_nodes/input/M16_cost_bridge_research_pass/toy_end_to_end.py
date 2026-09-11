#!/usr/bin/env python3
"""Close the algebraic recovery on actual unplanted-to-solver toy witnesses.
This is a correctness test, not a claim of novel or faster ECDLP solving.
"""
from pathlib import Path
import json, random
from toy_yield_and_search import Curve,roots_and_points
HERE=Path(__file__).resolve().parent

def nullvector(C,n):
 # Nullspace of transpose(C), chosen from C alone, before generating labels b.
 M=len(C);B=len(C[0]);A=[[C[i][j]%n for i in range(M)] for j in range(B)]
 pivots=[];r=0
 for c in range(M):
  k=next((i for i in range(r,B) if A[i][c]),None)
  if k is None:continue
  A[r],A[k]=A[k],A[r];inv=pow(A[r][c],-1,n);A[r]=[x*inv%n for x in A[r]]
  for i in range(B):
   if i!=r and A[i][c]:
    q=A[i][c];A[i]=[(x-q*y)%n for x,y in zip(A[i],A[r])]
  pivots.append(c);r+=1
  if r==B:break
 free=next(c for c in range(M) if c not in pivots);w=[0]*M;w[free]=1
 for i,c in reversed(list(enumerate(pivots))):w[c]=-sum(A[i][j]*w[j] for j in range(c+1,M))%n
 assert any(w)
 assert all(sum(w[i]*C[i][j] for i in range(M))%n==0 for j in range(B))
 return w,r

records=[]
for rec in json.loads((HERE/'toy_yield_and_search.json').read_text())['records']:
 p,n,D=rec['p'],rec['n'],rec['D'];B=rec['glv_orbits'];wits=rec['witnesses'][:B+1]
 if len(wits)<B+1:
  records.append({'p':p,'D':D,'status':'INSUFFICIENT_WITNESSES','required':B+1,'available':len(wits)});continue
 curve=Curve(p);pts=sorted(roots_and_points(p));G=pts[0];F=[P for P in pts if pow(P[0],D,p)==1]
 beta=next(pow(a,(p-1)//3,p) for a in range(2,p) if pow(a,(p-1)//3,p)!=1)
 lam=next(pow(a,(n-1)//3,n) for a in range(2,n) if pow(a,(n-1)//3,n)!=1)
 phiG=(beta*G[0]%p,G[1])
 if curve.mul(lam,G)!=phiG:lam=lam*lam%n
 assert curve.mul(lam,G)==phiG and (lam*lam+lam+1)%n==0
 mapping={};reps=[]
 for P in F:
  if P in mapping:continue
  col=len(reps);reps.append(P);T=P;c=1
  for _ in range(3):
   mapping[T]=(col,c);mapping[(T[0],-T[1]%p)]=(col,-c%n)
   T=(beta*T[0]%p,T[1]);c=c*lam%n
 assert len(reps)==B and set(mapping)==set(F)
 C=[]
 for wit in wits:
  row=[0]*B
  for i in wit['factorbase_indices']:
   j,c=mapping[F[i]];row[j]=(row[j]+c)%n
  C.append(row)
 w,rank=nullvector(C,n)
 # Test harness only. Uniform target scalars in earlier benchmark were hidden from the solver.
 # Labels b generated after freezing C,w are independent of their contents.
 rng=random.Random(20260910+p*10000+D);secret=rng.randrange(1,n)
 bs=[rng.randrange(n) for _ in wits]
 aa=[(wit['target_scalar_for_audit_only']-b*secret)%n for wit,b in zip(wits,bs)]
 wb=sum(x*y for x,y in zip(w,bs))%n;wa=sum(x*y for x,y in zip(w,aa))%n
 if wb==0:
  records.append({'p':p,'D':D,'status':'UNINFORMATIVE_W_RANDOM_LABEL','rank':rank});continue
 recovered=-wa*pow(wb,-1,n)%n
 assert recovered==secret
 assert curve.mul(recovered,G)==curve.mul(secret,G)
 # Independent numeric check of the elimination relation using the known test target scalars.
 assert sum(w[i]*wits[i]['target_scalar_for_audit_only'] for i in range(len(w)))%n==0
 records.append({'p':p,'n':n,'D':D,'status':'RECOVERED','columns':B,'rows':B+1,'rank':rank,
  'glv_beta':beta,'glv_lambda':lam,'C':C,'w':w,'a':aa,'b':bs,
  'known_secret_test_harness_only':secret,'recovered':recovered})
out={'records':records,'recovered':sum(r['status']=='RECOVERED' for r in records),
 'insufficient':sum(r['status']=='INSUFFICIENT_WITNESSES' for r in records),
 'scope':'Validates relation-to-DLP algebra only. Reuses actual solver witnesses. Scalars only in harness, not decomposition inputs. No improvement in relation-generation cost is claimed.'}
(HERE/'toy_end_to_end.json').write_text(json.dumps(out,indent=2));print([(r['p'],r['D'],r['status']) for r in records])
