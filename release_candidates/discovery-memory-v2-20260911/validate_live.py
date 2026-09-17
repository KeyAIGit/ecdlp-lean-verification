# SPDX-License-Identifier: Apache-2.0
"""Read-only retrieval checks; write only a new local report."""
import json
from pathlib import Path
import memory
queries=['1304.1238','Sparse FGLM','1707.01971','primary decomposition','рациональные компоненты','производная кратности','B-PKC-M16-COMPLETE-COST-BRIDGE','2202.13387']
rows=[]
for query in queries:
    result=memory.search(query,3)
    row={'query':query,'seconds':result['elapsed_seconds'],'papers':[{k:p[k] for k in ('id','title','read_id')} for p in result['papers']],'documents':[{k:p[k] for k in ('title','path','read_id','start_line','end_line')} for p in result['project_and_selected_sources']]}
    rows.append(row)
    print(json.dumps(row,ensure_ascii=True),flush=True)
assert rows[0]['papers'][0]['id']=='1304.1238'
assert rows[1]['papers'][0]['id']=='1304.1238'
assert rows[2]['papers'][0]['id']=='1707.01971'
assert rows[-1]['papers'][0]['id']=='2202.13387'
assert rows[4]['documents'] and rows[5]['documents']
report={'status':'PASS_RETRIEVAL_SMOKE','scope':'Eight actual local queries, not a scientific benchmark or proof of complete relevance','queries':rows}
(Path(__file__).resolve().parent/'RETRIEVAL_VALIDATION.json').write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding='utf-8')
