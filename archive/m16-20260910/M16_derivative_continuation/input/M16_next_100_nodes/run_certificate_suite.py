#!/usr/bin/env python3
"""Certificate/recovery tests. All sources and exclusions are recorded.
The old 319 witnesses were found earlier on small independent targets.
The new 256-bit cases are explicitly PLANTED and measure no search yield.
"""
from pathlib import Path
from collections import Counter
import json,time,random,copy
import norm_bridge as nb
HERE=Path(__file__).resolve().parent
OLD=HERE/'input/M16_cost_bridge_research_pass'

def points_over_field(p):
    ys={}
    for y in range(p):ys.setdefault(y*y%p,[]).append(y)
    return sorted((x,y)for x in range(p)for y in ys.get((x**3+7)%p,[]))

def check_case(points,R,p,D,label):
    c=nb.interpolate_certificate(points,R,p,D)
    t=time.monotonic();got=nb.verify_and_recover(c);elapsed=time.monotonic()-t
    assert Counter(got)==Counter(points)
    c.update({'label':label,'recovered_points':[list(P)for P in got],
              'distinct_x_count':len(set(x for x,y in got)),
              'recovery_seconds_single_local_observation':elapsed})
    return c

def main():
    old=json.loads((OLD/'toy_yield_and_search.json').read_text());cache={};toys=[];special=[]
    for rec in old['records']:
        p,D=rec['p'],rec['D']
        if p not in cache:cache[p]=points_over_field(p)
        allpoints=cache[p];F=[P for P in allpoints if pow(P[0],D,p)==1]
        for i,w in enumerate(rec['witnesses']):
            pts=[F[j] for j in w['factorbase_indices']];R=nb.ec_sum(pts,p)
            reduced,removed=nb.cancel_pairs(pts,p)
            base={'p':p,'D':D,'old_witness_index':i,'original_q':16,
                  'remaining_q':len(reduced),'cancelled_pairs':removed}
            if R is None or pow(R[0],D,p)==1:
                special.append({**base,'status':'SEPARATE_KNOWN_BRANCH','R':R});continue
            c=check_case(reduced,R,p,D,'REPLAY_OLD_UNPLANTED_TOY_WITNESS')
            c.update(base);toys.append(c)
    assert len(toys)+len(special)==sum(len(r['witnesses'])for r in old['records'])==319
    src=json.loads((OLD/'permutation_cost_certificate.json').read_text());p=int(src['p']);D=src['D']
    F=[tuple(map(int,P))for P in src['points']];big=[]
    for q in range(2,17,2):
        patterns={'distinct':F[:q], 'single_repeated':[F[0]]*q,
                  'two_repeated':[F[0]]*(q//2)+[F[1]]*(q//2)}
        for name,pts in patterns.items():
            R=nb.ec_sum(pts,p)
            if R is None or pow(R[0],D,p)==1:raise RuntimeError('unexpected separate branch in fixed cases')
            c=check_case(pts,R,p,D,f'PLANTED_256_Q{q}_{name.upper()}')
            # Reordering must produce identical normalized coefficients.
            alt=nb.interpolate_certificate(list(reversed(pts)),R,p,D)
            assert all(c[k]==alt[k]for k in ['A','B','g'])
            big.append(c)
    mutations=[]
    c=next(c for c in big if c['q']==16 and c['distinct_x_count']==16)
    for name in ['A','B','g','target_sign','target_x','q','D']:
        d=copy.deepcopy(c)
        if name in ('A','B','g'):d[name][0]=(d[name][0]+1)%p
        elif name=='target_sign':d['R'][1]=-d['R'][1]%p
        elif name=='target_x':d['R'][0]=(d['R'][0]+1)%p
        elif name=='q':d['q']=14
        elif name=='D':d['D']=42
        try:nb.verify_and_recover(d)
        except (ValueError,ArithmeticError) as e:mutations.append({'mutation':name,'rejected':True,'reason':str(e)})
        else:raise AssertionError('accepted mutation '+name)
    # A valid repeated witness must not satisfy the simple square-free membership test.
    rep=next(c for c in big if c['q']==16 and c['distinct_x_count']==1)
    assert nb.ppow([0,1],D,rep['g'],p)!=[1]
    # Quotient recovery produces the right branch even with multiplicity.
    for c in big:
        Y=nb.mod(nb.scale(nb.pm(c['A'],nb.pinv(c['B'],c['g'],p),p),-1,p),c['g'],p)
        assert nb.mod(nb.ps(nb.pm(Y,Y,p),[7,0,0,1],p),c['g'],p)==[0]
    out={'status':'PASS','old_witnesses_total':319,'toy_norm_certificates':len(toys),
         'toy_separate_known_branches':len(special),'planted_256_certificates':len(big),
         'toy_chart_q_counts':dict(Counter(c['q']for c in toys)),
         'mutations':mutations,'toys':toys,'special':special,'planted_256':big,
         'scope':'Certificate conversion and independent-input root recovery, not a new-target M16 solver.'}
    (HERE/'certificate_suite.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items()if k not in ('toys','special','planted_256')},indent=2))
if __name__=='__main__':main()
