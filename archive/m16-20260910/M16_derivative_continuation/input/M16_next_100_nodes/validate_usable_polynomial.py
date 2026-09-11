#!/usr/bin/env python3
"""Independent character predicate plus an exact all-coefficient partition check.
The product-tree multiplier is shared, explicitly not an independent polynomial
arithmetic implementation. Root classification uses Euler, not producer Jacobi.
"""
from pathlib import Path
import json,time,hashlib
from build_usable_polynomial import P,D,ROOT,readints,kmul,binary

def validate():
    t=time.perf_counter();roots=readints(ROOT/'usable_cube_roots.bin');selected=set(roots)
    J=readints(ROOT/'usable_cube_polynomial.bin');v=pow(pow(3,(P-1)//D,P),3,P);u=1;negative=[];positive=0
    for i in range(D//3):
        e=pow((u+7)%P,(P-1)//2,P)
        assert e in(1,P-1)
        assert ((u in selected)==(e==1))
        if e==P-1:negative.append(u)
        else:positive+=1
        u=u*v%P
    assert u==1 and positive==94509 and len(negative)==93665
    euler_seconds=time.perf_counter()-t;print('EULER_ALL_ROOTS_PASS',euler_seconds,flush=True)
    polys=[[-x%P,1]for x in reversed(negative)]
    while len(polys)>1:
        polys=[kmul(polys[i],polys[i+1])if i+1<len(polys)else polys[i]for i in range(0,len(polys),2)]
    K=polys[0];product=kmul(J,K)
    assert len(product)==D//3+1 and product[0]==P-1 and product[-1]==1 and not any(product[1:-1])
    out={'status':'PASS','Euler_vs_Jacobi_all_cube_roots_checked':D//3,'positive':positive,'negative':len(negative),
         'exact_polynomial_identity':'J(T)*K(T) = T^188174 - 1','coefficients_checked':len(product),
         'euler_seconds':euler_seconds,'total_seconds':time.perf_counter()-t,
         'J_sha256':hashlib.sha256(binary(J)).hexdigest(),
         'scope':['All root-classification decisions independently checked by Euler criterion.',
                  'All coefficients of product checked, not just random evaluations.',
                  'Polynomial multiplication shares the exact Kronecker/GMP backend with the producer.',
                  'Preparation only; no independently targeted secp256k1 M16 decomposition found.']}
    (ROOT/'usable_polynomial_validation.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':validate()
