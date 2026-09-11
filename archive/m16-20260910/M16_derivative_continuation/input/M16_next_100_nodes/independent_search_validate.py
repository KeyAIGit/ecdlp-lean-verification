#!/usr/bin/env python3
"""Independent new-target q2/q4 certificate and complete-answer-set checks.
Uses SymPy and independent Jacobian arithmetic from independent_validate.
No producer point addition, target generation, or polynomial solver is called.
"""
from pathlib import Path
from itertools import combinations, product
import json,hashlib
from independent_validate import check,sumj,ja,jd
HERE=Path(__file__).resolve().parent

def mulj(k,P,p):
    acc=(0,1,0);cur=(P[0],P[1],1)
    while k:
        if k&1:acc=ja(acc,cur,p)
        cur=jd(cur,p);k//=2
    X,Y,Z=acc
    if not Z:return None
    iv=pow(Z,-1,p);return(X*iv*iv%p,Y*iv*iv*iv%p)

def points(p):
    ys={}
    for y in range(p):ys.setdefault(y*y%p,[]).append(y)
    return sorted((x,y)for x in range(p)for y in ys.get((x*x*x+7)%p,[]))

def main():
    cache={};q2=json.loads((HERE/'q2_benchmark.json').read_text());count2=0;cases2=0
    for row in q2['cases']:
        if row['status']!='COMPLETE_Q2_MATCH':continue
        p,D=row['p'],row['D'];R=tuple(row['R'])
        if p not in cache:cache[p]=points(p)
        pts=cache[p];G=pts[0];n=len(pts)+1
        k=int.from_bytes(hashlib.sha256(f'm16-next-q2:{p}:{row["i"]}'.encode()).digest(),'big')%n
        assert row['target_scalar_harness_only']==k and mulj(k,G,p)==R
        F=[P for P in pts if pow(P[0],D,p)==1];Fs=set(F);expected=set()
        for P in F:
            other=sumj([R,(P[0],-P[1]%p)],p)
            if other in Fs:expected.add(tuple(sorted([P,other])))
        got=set()
        for c in row['certificates']:
            check(c);count2+=1;got.add(tuple(sorted(map(tuple,c['recovered_points']))))
        assert expected==got;cases2+=1
    q4=[];count4=0;unique={}
    for path in sorted(HERE.glob('q4_*.json')):
        j=json.loads(path.read_text())
        if j.get('status')!='PASS_COMPLETE_SQUAREFREE_Q4':continue
        p,D=j['p'],j['D'];R=tuple(j['R'])
        if p not in cache:cache[p]=points(p)
        pts=cache[p];n=len(pts)+1
        k=int.from_bytes(hashlib.sha256(f'm16-next-q4:{p}:{j["index"]}'.encode()).digest(),'big')%n
        assert j['target_scalar_harness_only']==k and mulj(k,pts[0],p)==R
        byx={}
        for x,y in pts:
            if pow(x,D,p)==1:byx.setdefault(x,[]).append(y)
        expected=set()
        for xs in combinations(sorted(byx),4):
            for ys in product(*(byx[x]for x in xs)):
                Ps=tuple(zip(xs,ys))
                if sumj(Ps,p)==R:expected.add(Ps)
        got=set()
        for c in j['accepted']:
            check(c);count4+=1;got.add(tuple(sorted(map(tuple,c['recovered_points']))))
        assert got==expected
        key=(p,D,j['index']);frozen=unique.setdefault(key,got);assert frozen==got
        q4.append({'file':path.name,'solutions':len(got)})
    out={'status':'PASS','q2_complete_target_cases':cases2,'q2_certificates':count2,
         'q4_completed_run_records':len(q4),'q4_certificate_records':count4,
         'q4_distinct_target_cases':len(unique),'q4_distinct_target_witness_pairs':sum(map(len,unique.values())),
         'q4_records':q4,'scope':'Exact complete solution sets on the stated tiny cases. No 256-bit targeted decomposition or asymptotic gain.'}
    (HERE/'independent_search_validation.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()
