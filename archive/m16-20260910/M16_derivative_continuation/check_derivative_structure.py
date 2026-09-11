#!/usr/bin/env python3
"""Exact finite-field checks of support equations and their differentials.
NOT a search algorithm for secp256k1. Large-field cases reuse planted inputs.
"""
from pathlib import Path
from itertools import product
from collections import Counter
import json,sys,time,math
import norm_bridge as nb
from derivative_probe import rank_mod
ROOT=Path(__file__).resolve().parent
OLD=ROOT/'input/M16_next_100_nodes'
sys.path.insert(0,str(OLD))
from independent_validate import check as independent_certificate_check

def pad(a,q):return a+[0]*(q-len(a))
def matrix(cols,q):return [[pad(c,q)[i]for c in cols]for i in range(q)]

def det_mod(M,p):
    A=[[x%p for x in r]for r in M];d=1
    for i in range(len(A)):
        j=next((j for j in range(i,len(A))if A[j][i]),None)
        if j is None:return 0
        if j!=i:A[i],A[j]=A[j],A[i];d=-d%p
        a=A[i][i];d=d*a%p;iv=pow(a,-1,p)
        for j in range(i+1,len(A)):
            c=A[j][i]*iv%p
            for k in range(i,len(A)):A[j][k]=(A[j][k]-c*A[i][k])%p
    return d%p

def Fmod(g,p,D):return nb.ps(nb.ppow([0,1],D,g,p),[1],p)

def support_jacobian(g,p,F):
    q=len(g)-1
    H,rem=nb.pd(nb.pm(F,nb.deriv(g,p),p),g,p)
    assert rem==[0]
    def L(h):return nb.mod(nb.ps(nb.pm(F,nb.deriv(h,p),p),nb.pm(H,h,p),p),g,p)
    return matrix([L([0]*i+[1])for i in range(q)],q)

def exhaustive():
    records=[]
    for p,maxq,roots in [(5,4,[1,2]),(7,4,[0,1,3]),(11,3,[2,5])]:
        F=[1]
        for a in roots:F=nb.pm(F,[-a,1],p)
        count=0;positive=0;rank_checks=0
        for q in range(1,maxq+1):
            for cs in product(range(p),repeat=q):
                g=list(cs)+[1];df=nb.mod(nb.pm(F,nb.deriv(g,p),p),g,p)==[0]
                pw=nb.ppow(F,q,g,p)==[0]
                # Independent support oracle: remove all factors in known allowed set.
                r=g
                for a in roots:
                    while len(r)>1:
                        z,rem=nb.pd(r,[-a,1],p)
                        if rem!=[0]:break
                        r=z
                supported=len(r)==1
                assert df==pw==supported
                if supported:
                    assert rank_mod(support_jacobian(g,p,F),p)==q
                    positive+=1;rank_checks+=1
                count+=1
        records.append({'p':p,'max_q':maxq,'roots':roots,'all_monic_polynomials_checked':count,'supported':positive,'full_jacobian_checks':rank_checks})
    p=3;g=[0,0,0,1];F=[-1,1]
    wrong=nb.mod(nb.pm(F,nb.deriv(g,p),p),g,p)==[0]
    correct=nb.ppow(F,3,g,p)==[0]
    assert wrong and not correct
    return {'status':'PASS','cases':records,'total_polynomials':sum(x['all_monic_polynomials_checked']for x in records),'characteristic_guard_counterexample':{'p':p,'g':g,'F':F,'derivative_accepts':wrong,'power_accepts':correct}}

def norm_direction_columns(c):
    p,q=c['p'],c['q'];s=q//2;r,z=c['R'];A=c['A'];B=c['B'];cols=[]
    for i in range(1,s+1):
        da=[-pow(r,i,p)]+[0]*(i-1)+[1]
        num=nb.scale(nb.pm(A,da,p),-2,p);dg,rem=nb.pd(num,[-r,1],p);assert rem==[0];cols.append(dg)
    for i in range(s-1):
        db=[0]*i+[1];da=[z*pow(r,i,p)%p]
        num=nb.scale(nb.ps(nb.pm(nb.pm([7,0,0,1],B,p),db,p),nb.pm(A,da,p),p),2,p)
        dg,rem=nb.pd(num,[-r,1],p);assert rem==[0];cols.append(dg)
    return cols

def norm_jacobians(c):
    p,q,D=c['p'],c['q'],c['D'];g=c['g'];g2=nb.pm(g,g,p);f2=Fmod(g2,p,D);f=nb.mod(f2,g,p)
    term=nb.mod(nb.pm(f2,nb.deriv(g,p),p),g2,p);H,rem=nb.pd(term,g,p);assert rem==[0]
    old=nb.ppow(f2,q,g2,p);Q,rem=nb.pd(old,g,p);assert rem==[0]
    def L(h):return nb.mod(nb.ps(nb.pm(f,nb.deriv(h,p),p),nb.pm(H,h,p),p),g,p)
    cols=norm_direction_columns(c)
    M=matrix([L(h)for h in cols],q)
    P=matrix([nb.mod(nb.scale(nb.pm(Q,h,p),-1,p),g,p)for h in cols],q)
    support_matrix=matrix([L([0]*i+[1])for i in range(q)],q)
    assert rank_mod(support_matrix,p)==q
    assert rank_mod(M,p)==q-1
    mult=Counter(x for x,y in c['recovered_points'])
    det=det_mod(support_matrix,p)
    formula=pow(D,q,p)*math.prod(math.factorial(e)for e in mult.values())*pow(g[0],-1,p)%p
    assert det==formula!=0
    return {'label':c['label'],'q':q,'distinct_x':len(mult),'max_multiplicity':max(mult.values()),'derivative_norm_rank':rank_mod(M,p),'powered_norm_rank':rank_mod(P,p),'support_jacobian_determinant':det,'determinant_formula_verified':True,'derivative_matrix':M,'powered_matrix':P}

def dual_linearization(c,column):
    """Independent forward differentiation of modular repeated squaring.
    Coefficients are pairs (value,epsilon-coefficient), g varies in direction h.
    This does not use the formula F*h'-H*h for its differential.
    """
    p,q,D=c['p'],c['q'],c['D'];g=c['g'];h=pad(norm_direction_columns(c)[column],q)
    G=[(g[i],h[i])for i in range(q)]+[(1,0)]
    def add(a,b):return ((a[0]+b[0])%p,(a[1]+b[1])%p)
    def neg(a):return (-a[0]%p,-a[1]%p)
    def mul(a,b):return (a[0]*b[0]%p,(a[0]*b[1]+a[1]*b[0])%p)
    def red(a):
        a=list(a)
        for i in range(len(a)-1,q-1,-1):
            t=a[i]
            for j in range(q):a[i-q+j]=add(a[i-q+j],neg(mul(t,G[j])))
        return a[:q]+[(0,0)]*max(0,q-len(a))
    def pm(a,b):
        o=[(0,0)]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):o[i+j]=add(o[i+j],mul(x,y))
        return red(o)
    def power(a,e):
        r=[(1,0)]+[(0,0)]*(q-1)
        while e:
            if e&1:r=pm(r,a)
            e//=2
            if e:a=pm(a,a)
        return r
    F=power(red([(0,0),(1,0)]),D);F[0]=add(F[0],(-1,0))
    gp=[((i+1)*G[i+1][0]%p,(i+1)*G[i+1][1]%p)for i in range(q)]
    d=pm(F,gp);w=power(F,q)
    assert all(x[0]==0 for x in d+w)
    return [x[1]for x in d],[x[1]for x in w]

def main():
    t=time.perf_counter();ex=exhaustive();(ROOT/'results/support_exhaustive.json').write_text(json.dumps(ex,indent=2));print('EXHAUSTIVE',ex['total_polynomials'],flush=True)
    old=json.loads((OLD/'certificate_suite.json').read_text());rows=[]
    for c in old['planted_256']:
        independent_certificate_check(c)
        row=norm_jacobians(c);rows.append(row)
        print(c['label'],row['derivative_norm_rank'],row['powered_norm_rank'],flush=True)
    # All 15 columns of one actual 256-bit q16 distinct-point certificate.
    ci=next(i for i,c in enumerate(old['planted_256'])if c['q']==16 and c['distinct_x_count']==16)
    c=old['planted_256'][ci];r=rows[ci]
    for j in range(15):
        a,b=dual_linearization(c,j)
        assert a==[row[j]for row in r['derivative_matrix']]
        assert b==[row[j]for row in r['powered_matrix']]
    out={'status':'PASS','cases':rows,'checks_256':len(rows),'dual_number_crosscheck_columns':15,'seconds':time.perf_counter()-t,'scope':'Planted certificates only; exact rank is not a search result or complexity estimate.'}
    (ROOT/'results/structure_256.json').write_text(json.dumps(out,indent=2));print('PASS',out['seconds'])
if __name__=='__main__':main()
