# SPDX-License-Identifier: Apache-2.0
"""Bounded representation diagnostic, not a scalable solver or cost theorem."""
import hashlib,json,sys,time,itertools
from pathlib import Path
import sympy as sp
root=Path(__file__).resolve().parent
plan=json.loads((root/'SYMBOLIC_PLAN.json').read_text())
mode=sys.argv[1]
assert mode in ('original','projected')
p=plan['p'];r,z=plan['R'];a1,a2,b0=sp.symbols('a1 a2 b0')
variables=(a1,a2,b0)
ring=sp.GF(p).poly_ring(*variables)
zero=ring.zero
start=time.perf_counter()
a0=ring.convert(z*(r+b0)-a1*r-a2*r*r)
a1,a2,b0=map(ring.convert,variables)
g3=2*b0-a2*a2+r
g2=b0*b0-2*a1*a2+r*g3
g1=7-a1*a1-2*a0*a2+r*g2
g0=14*b0-2*a0*a1+r*g1
g=[g0,g1,g2,g3]
h=[-g1,-2*g2,-3*g3,g1-4,2*g2,3*g3,ring.convert(4)]
for degree in (6,5,4):
    lead=h[degree]
    for j in range(4):h[degree-4+j]-=lead*g[j]
S=h[:4]
v=plan['selector'];j=next(i for i,x in enumerate(v) if x%p)
T=[v[j]*S[i]-v[i]*S[j] for i in range(4) if i!=j] if mode=='projected' else S
polys=[sp.Poly(ring.to_sympy(e),*variables,modulus=p) for e in T]
print(json.dumps({'stage':'constructed','mode':mode,'degrees':[e.total_degree() for e in polys],
                 'term_counts':[len(e.terms()) for e in polys],'elapsed_seconds':time.perf_counter()-start}),flush=True)
gbstart=time.perf_counter()
gb=sp.groebner([e.as_expr() for e in polys],*variables,modulus=p,order='grevlex')
basis_seconds=time.perf_counter()-gbstart
leading=[pol.LM(order=gb.order).exponents for pol in gb.polys]
bounds=[]
for j in range(3):
    powers=[e[j] for e in leading if e[j]>0 and sum(e)==e[j]]
    if not powers:raise ValueError('Expected a zero-dimensional monomial ideal')
    bounds.append(min(powers))
quotient_dimension=sum(1 for e in itertools.product(*(range(b) for b in bounds))
                       if not any(all(a<=b for a,b in zip(lm,e)) for lm in leading))
print(json.dumps({'stage':'basis_completed','mode':mode,'basis_seconds':basis_seconds,'quotient_vector_space_dimension':quotient_dimension,
                 'basis_size':len(gb.polys),'maximum_output_basis_degree':max(e.total_degree() for e in gb.polys),
                 'zero_dimensional':bool(gb.is_zero_dimensional),'elapsed_seconds':time.perf_counter()-start,
                 'solving_degree_measured':False,'root_extraction_performed':False}),flush=True)
