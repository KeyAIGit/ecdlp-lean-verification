#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,time
import norm_bridge as nb
import q2_slope_solver as solver
HERE=Path(__file__).resolve().parent
CONFIGS=[(4159,18),(4159,42),(4159,126),(16879,174),(64303,42)]

def allpoints(p):
    ys={}
    for y in range(p):ys.setdefault(y*y%p,[]).append(y)
    return sorted((x,y)for x in range(p)for y in ys.get((x**3+7)%p,[]))

def main():
    cache={};rows=[]
    (HERE/'q2_benchmark_plan.json').write_text(json.dumps({'configurations':CONFIGS,'targets_per_configuration':8,
        'selection':'SHA256(p,index) modulo exact group order; chart-excluded targets are logged, not replaced',
        'scope':'Online q2 control. All-point enumeration is ground-truth preparation, not a solver step.'},indent=2))
    for p,D in CONFIGS:
        if p not in cache:cache[p]=allpoints(p)
        pts=cache[p];G=pts[0];n=len(pts)+1;F=[P for P in pts if pow(P[0],D,p)==1];Fs=set(F)
        for i in range(8):
            k=int.from_bytes(hashlib.sha256(f'm16-next-q2:{p}:{i}'.encode()).digest(),'big')%n
            R=nb.ec_mul(k,G,p)
            if R is None or pow(R[0],D,p)==1:
                rows.append({'p':p,'D':D,'i':i,'status':'SEPARATE_CHART_TARGET'});continue
            t=time.perf_counter();answer=solver.solve(p,D,R);elapsed=time.perf_counter()-t
            t=time.perf_counter();expected=set()
            for P in F:
                Q=nb.ec_add(R,(P[0],-P[1]%p),p)
                if Q in Fs:expected.add(tuple(sorted((P,Q))))
            baseline=time.perf_counter()-t
            got={tuple(sorted(tuple(P)for P in c['recovered_points']))for c in answer['certificates']}
            assert got==expected
            row={'p':p,'D':D,'n':n,'i':i,'R':list(R),'status':'COMPLETE_Q2_MATCH',
                 'signed_factorbase_size':len(F),'target_scalar_harness_only':k,
                 'solver_seconds':elapsed,'lookup_online_seconds':baseline,'lookup_additions':len(F),
                 'solutions':len(got),**answer}
            rows.append(row)
            print(p,D,i,'solutions',len(got),'deg',answer['membership_equation_degrees'],
                  'seconds',round(elapsed,4),flush=True)
    out={'status':'PASS','cases':rows,'scope':['Independent target q2 search only.',
          'No extrapolation to q16 or 256-bit total cost.',
          'Lookup timings exclude factor-base preparation; timings are not asymptotic estimates.']}
    (HERE/'q2_benchmark.json').write_text(json.dumps(out,indent=2))
if __name__=='__main__':main()
