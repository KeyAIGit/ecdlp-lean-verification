#!/usr/bin/env python3
"""Sequential matched exploratory jobs. Timeout includes construction and search.
All jobs are logged, including censored and failed runs. No timeout is reported
as absence of solutions, a lower bound, or a mathematical negative result.
"""
from pathlib import Path
import json,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
jobs=[
 (97,3,4,1,'derivative','usable',60),
 (97,3,4,1,'power','usable',60),
 (97,3,4,3,'derivative','usable',60),
 (163,9,4,0,'derivative','usable',60),
 (163,9,4,0,'quotient','usable',60),
 (97,3,6,0,'derivative','usable',60),
]
plan={'jobs':jobs,'interpretation':'Fixed targets independent of membership. Search failures and timeouts kept; no extrapolation to q16.'}
(ROOT/'benchmark_plan.json').write_text(json.dumps(plan,indent=2))
records=[]
for p,D,q,index,encoding,membership,budget in jobs:
    key=f'probe_{p}_{D}_{q}_{index}_{encoding}_{membership}'
    command=[sys.executable,str(ROOT/'derivative_probe.py'),'--p',str(p),'--D',str(D),'--q',str(q),'--index',str(index),'--encoding',encoding,'--membership',membership]
    start=time.perf_counter()
    with open(ROOT/'results'/f'{key}.log','w') as log:
        try:
            cp=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=budget)
            state='FINISHED' if cp.returncode==0 else 'ERROR'
            ret=cp.returncode
        except subprocess.TimeoutExpired:
            state='RIGHT_CENSORED';ret=None
    records.append({'key':key,'command':command,'budget_seconds':budget,'elapsed_seconds':time.perf_counter()-start,'status':state,'returncode':ret})
    (ROOT/'benchmark_runlog.json').write_text(json.dumps(records,indent=2))
    print(json.dumps(records[-1]),flush=True)
