#!/usr/bin/env python3
"""Build the actual degree-94509 usable-cube polynomial for secp256k1.
Standard Python integer multiplication via exact Kronecker substitution.
No ECDLP target or target witness is used. Binary files store little-endian
32-byte canonical field elements, coefficients in increasing degree.
"""
from pathlib import Path
import hashlib,json,math,sys,time,ctypes,os
import norm_bridge as nb
ROOT=Path(__file__).resolve().parent
P=2**256-2**32-977;D=564522
_LIB=None
if (ROOT/'kronecker_gmp.so').exists() and os.getenv('M16_NO_GMP')!='1':
    _LIB=ctypes.CDLL(str(ROOT/'kronecker_gmp.so'))
    _LIB.m16_multiply.argtypes=[ctypes.c_char_p,ctypes.c_size_t,ctypes.c_char_p,ctypes.c_size_t,ctypes.c_void_p,ctypes.c_size_t]
    _LIB.m16_multiply.restype=ctypes.c_int

def jacobi(a,n):
    a%=n;s=1
    while a:
        while a%2==0:
            a//=2
            if n%8 in(3,5):s=-s
        a,n=n,a
        if a%4==n%4==3:s=-s
        a%=n
    return s if n==1 else 0

def kmul(a,b,p=P):
    if min(len(a),len(b))<=4:return nb.pm(a,b,p)
    # Every integer convolution coefficient is < min(len(a),len(b))*p^2.
    w=(2*p.bit_length()+min(len(a),len(b)).bit_length()+7)//8
    ra=b''.join(x.to_bytes(w,'little')for x in a);rb=b''.join(x.to_bytes(w,'little')for x in b)
    size=w*(len(a)+len(b)-1)
    if _LIB is None:
        raw=(int.from_bytes(ra,'little')*int.from_bytes(rb,'little')).to_bytes(size,'little')
    else:
        buf=ctypes.create_string_buffer(size)
        if _LIB.m16_multiply(ra,len(ra),rb,len(rb),buf,size):raise ArithmeticError('GMP multiplication failure')
        raw=buf.raw
    return [int.from_bytes(raw[i:i+w],'little')%p for i in range(0,len(raw),w)]

def binary(values):return b''.join(x.to_bytes(32,'little')for x in values)
def readints(path):
    b=Path(path).read_bytes();assert len(b)%32==0
    return[int.from_bytes(b[i:i+32],'little')for i in range(0,len(b),32)]

def make_roots():
    t=time.perf_counter();h=pow(3,(P-1)//D,P);v=pow(h,3,P)
    assert pow(v,D//3,P)==1
    assert all(pow(v,(D//3)//l,P)!=1 for l in(2,7,13441))
    u=1;roots=[];negative=0
    for _ in range(D//3):
        c=jacobi(u+7,P)
        if c==1:roots.append(u)
        elif c==-1:negative+=1
        else:raise ValueError('unexpected ramification')
        u=u*v%P
    assert u==1 and len(roots)==94509 and negative==93665
    roots.sort();data=binary(roots);(ROOT/'usable_cube_roots.bin').write_bytes(data)
    out={'status':'PASS','roots':len(roots),'negative':negative,'seconds':time.perf_counter()-t,
         'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),
         'scope':'Exact field-coordinate preparation, not independently targeted decomposition.'}
    (ROOT/'usable_roots_report.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))

def build():
    import random
    rng=random.Random(20260910)
    for l1,l2 in [(5,7),(20,20),(31,64),(257,333)]:
        a=[rng.randrange(P)for _ in range(l1)];b=[rng.randrange(P)for _ in range(l2)]
        assert kmul(a,b)==nb.pm(a,b,P)
    roots=readints(ROOT/'usable_cube_roots.bin');polys=[[-r%P,1]for r in roots];levels=[];start=time.perf_counter();lev=0
    while len(polys)>1:
        t=time.perf_counter();out=[]
        for i in range(0,len(polys)-1,2):out.append(kmul(polys[i],polys[i+1]))
        if len(polys)%2:out.append(polys[-1])
        polys=out;lev+=1
        rec={'level':lev,'polynomials':len(polys),'max_degree':max(map(len,polys))-1,'seconds':time.perf_counter()-t}
        levels.append(rec);print(json.dumps(rec),flush=True)
    J=polys[0];assert len(J)==94510 and J[-1]==1
    data=binary(J);(ROOT/'usable_cube_polynomial.bin').write_bytes(data)
    # Independent Horner/product evaluations, at predeclared points.
    evals=[]
    for x in (0,1,2,7,42,P-1):
        horner=nb.pe(J,x,P);product=1
        for r in roots:product=product*(x-r)%P
        assert horner==product;evals.append({'x':str(x),'value':str(horner)})
    out={'status':'PASS_CONSTRUCTION_AND_POINT_CHECKS','integer_backend':'GMP' if _LIB else 'Python','p':str(P),'D':D,'degree_J':len(J)-1,
         'degree_F_usable':3*(len(J)-1),'nonzero_coefficients_J':sum(c!=0 for c in J),'nonzero_coefficients_F_usable':sum(c!=0 for c in J),'comparison_original_membership_terms':2,'seconds':time.perf_counter()-start,'levels':levels,
         'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'evaluations':evals,
         'scope':['Exact Kronecker multiplication with no integer coefficient carry.',
                  'Six evaluations cross-check construction, not a standalone identity proof.',
                  'This does not find a decomposition for an independently specified target.',
                  'Precomputed polynomial has many terms; lower degree is not automatically lower total cost.']}
    (ROOT/'usable_polynomial_report.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':
    if sys.argv[1]=='roots':make_roots()
    elif sys.argv[1]=='build':build()
    else:raise SystemExit('usage: build_usable_polynomial.py roots|build')
