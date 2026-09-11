# SPDX-License-Identifier: Apache-2.0
"""Run both predefined diagnostic arms, preserving censored outcomes."""
import hashlib,json,subprocess,sys,time
from pathlib import Path
root=Path(__file__).resolve().parent
plan=json.loads((root/'SYMBOLIC_PLAN.json').read_text())
mode=sys.argv[1]
if mode not in plan['modes']:raise ValueError('undeclared arm')
start=time.perf_counter()
try:
    p=subprocess.run([sys.executable,str(root/'symbolic_probe.py'),mode],capture_output=True,
                     timeout=plan['child_wall_budget_seconds'])
    status='completed' if p.returncode==0 else 'error';out=p.stdout;err=p.stderr;code=p.returncode
except subprocess.TimeoutExpired as exc:
    status='wall_budget_exceeded';out=exc.stdout or b'';err=exc.stderr or b'';code=None
result={'mode':mode,'status':status,'returncode':code,'wall_seconds':time.perf_counter()-start,
        'stdout':out.decode('utf-8',errors='replace'),'stderr':err.decode('utf-8',errors='replace'),
        'plan_sha256':hashlib.sha256((root/'SYMBOLIC_PLAN.json').read_bytes()).hexdigest(),
        'timeout_is_not_unsatisfiability':True,'global_speedup_established':False}
(root/('SYMBOLIC_'+mode+'.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
