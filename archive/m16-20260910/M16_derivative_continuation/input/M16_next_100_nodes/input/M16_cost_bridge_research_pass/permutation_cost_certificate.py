#!/usr/bin/env python3
"""PLANTED 256-bit structural witness; never use to estimate target yield.

Builds a degree-16 divisor of X^D-1 from 16 distinct factor-base points.
Shows why explicitly listing every ordered solution has a 16! multiplier.
The S17 inference uses its mathematical summation property; S17 is NOT expanded.
"""
from pathlib import Path
import json, math, itertools, random
P=2**256-2**32-977
D=564522

def add(A,B):
 if A is None:return B
 if B is None:return A
 x,y=A;u,v=B
 if x==u:
  if (y+v)%P==0:return None
  s=3*x*x*pow(2*y,-1,P)%P
 else:s=(v-y)*pow(u-x,-1,P)%P
 z=(s*s-x-u)%P
 return z,(s*(x-z)-y)%P

def mulpoly(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%P
 return c

def rem(a,g):
 a=a[:]
 while len(a)>=len(g):
  c=a[-1];shift=len(a)-len(g)
  for i,b in enumerate(g):a[i+shift]=(a[i+shift]-c*b)%P
  while a and a[-1]==0:a.pop()
 return a or [0]

def powxmod(e,g):
 a=[1];x=[0,1]
 while e:
  if e&1:a=rem(mulpoly(a,x),g)
  x=rem(mulpoly(x,x),g);e>>=1
 return a

h=pow(3,(P-1)//D,P)
x=1;points=[];steps=0
while len(points)<16:
 rhs=(x*x*x+7)%P;y=pow(rhs,(P+1)//4,P)
 if y*y%P==rhs:points.append((x,min(y,P-y)))
 x=x*h%P;steps+=1
assert len({x for x,y in points})==16
R=None
for Q in points:R=add(R,Q)
assert R is not None
for x,y in points:assert pow(x,D,P)==1 and y*y%P==(x*x*x+7)%P
# Sample permutations test implementation; 16! conclusion is combinatorial, not sampled.
rng=random.Random(20260910)
for _ in range(100):
 perm=points[:];rng.shuffle(perm);T=None
 for Q in perm:T=add(T,Q)
 assert T==R
# All permutations of first 7 entries, remaining suffix unchanged.
for perm in itertools.permutations(points[:7]):
 T=None
 for Q in (*perm,*points[7:]):T=add(T,Q)
 assert T==R

g=[1]
for x,y in points:g=mulpoly(g,[-x%P,1])
assert len(g)==17 and g[-1]==1
assert powxmod(D,g)==[1]
out={'status':'PASS_STRUCTURAL_CERTIFICATE_NOT_RANDOM_TARGET_SEARCH',
 'p':str(P),'D':D,'points':[[str(x),str(y)] for x,y in points],
 'target':[str(x) for x in R], 'target_generation':'PLANTED: sum of the chosen factor-base points',
 'tested_permutations':100+math.factorial(7),
 'mathematical_distinct_ordered_x_tuples':str(math.factorial(16)),
 'explicit_uncompressed_16x32byte_tuple_list_bytes':str(math.factorial(16)*16*32),
 'divisor_monic_coefficients_low_to_high':[str(x) for x in g],
 'remainder_of_X_power_D_mod_divisor':[1],
 'scope':{'proof':'permutation count and quotient-dimension argument in RESEARCH_NOTE_RU.md',
          'not_claimed':['unplanted 256-bit decomposition','probability lower bound','universal Groebner lower bound',
             'new symmetry method','efficient algorithm for finding the divisor','Lean proof','constructed S17 coefficients'],
          'membership_quotient':'divisor test covers distinct x roots only; repeated-root representations require separate handling'}}
Path(__file__).with_name('permutation_cost_certificate.json').write_text(json.dumps(out,indent=2))
print(out['status'], out['mathematical_distinct_ordered_x_tuples'], out['explicit_uncompressed_16x32byte_tuple_list_bytes'])
