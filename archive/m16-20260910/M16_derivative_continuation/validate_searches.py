#!/usr/bin/env python3
"""Independent complete tiny-case validation, including repeated coordinates.
Does not import the solver, its finite-field equations, affine addition, or target
selection function. Uses full enumeration only in this validator, never as input
to the measured solver.
"""
from pathlib import Path
from itertools import combinations_with_replacement
from collections import Counter
import json,hashlib,sys
ROOT=Path(__file__).resolve().parent
OLD=ROOT/'input/M16_next_100_nodes'
sys.path.insert(0,str(OLD))
from independent_validate import sumj,check

def main():
    records=[];unique={};rows=0;cache={}
    for path in sorted((ROOT/'results').glob('probe_*.json')):
        data=json.loads(path.read_text())
        if data.get('status')!='SOLVER_FINISHED':continue
        p,D,q=data['p'],data['D'],data['q'];R=tuple(data['R'])
        sq={}
        for y in range(p):sq.setdefault(y*y%p,[]).append(y)
        pts=[(x,y)for x in range(p)for y in sq.get((x*x*x+7)%p,[])]
        h=int.from_bytes(hashlib.sha256(f'M16-derivative-unplanted-v1:{p}:{data["index"]}'.encode()).digest(),'big')
        assert pts[h%len(pts)]==R and pow(R[0],D,p)!=1
        key=(p,D,q,R)
        if key not in cache:
            allowed=[P for P in pts if pow(P[0],D,p)==1]
            expected=set();examined=0
            for ms in combinations_with_replacement(allowed,q):
                S=set(ms)
                if any((x,-y%p)in S for x,y in S):continue
                examined+=1
                if sumj(ms,p)==R:expected.add(tuple(sorted(ms)))
            cache[key]=(expected,examined)
        expected,examined=cache[key]
        if data['encoding']=='squarefree':expected={ms for ms in expected if len({P[0]for P in ms})==q}
        got=set()
        for cert in data['accepted']:
            c=dict(cert);c['recovered_points']=c['points'];c['distinct_x_count']=len({P[0]for P in c['points']})
            check(c);ms=tuple(sorted(map(tuple,c['points'])));got.add(ms)
            rows+=1
        assert got==expected, {'file':path.name,'extra':len(got-expected),'missing':len(expected-got)}
        if data['encoding']!='squarefree':
            if key in unique:assert unique[key]==got
            unique[key]=got
        records.append({'file':path.name,'expected_and_found':len(got),'multisets_checked_independently':examined,'with_repeated_x':sum(len({P[0]for P in ms})<q for ms in got)})
    out={'status':'PASS','completed_run_records':len(records),'unique_target_cases':len(unique),'certificate_records_including_repeat_runs':rows,'distinct_target_witness_pairs':sum(map(len,unique.values())),'records':records,'scope':'Complete norm-map multisets without opposite pairs, including repeated points. Tiny fields only. Solver does not see enumeration.'}
    (ROOT/'results/independent_search_validation.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()
