#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Explicit local research memory. No daemon, paid API or account access."""
import argparse,hashlib,json,os,re,shutil,sqlite3,sys,time,tempfile
from pathlib import Path
from datetime import datetime,timezone
from build_catalog import guard
HOME=Path(__file__).resolve().parent
ALIASES={'компонента':'rational component','компоненты':'rational component','компоненту':'rational component','рациональные':'rational','фробениус':'frobenius','фробениуса':'frobenius','проекция':'projection','проекции':'projection','разложение':'decomposition','разложения':'decomposition','семаев':'semaev','решатель':'solver','производная':'derivative','производной':'derivative','кратности':'multiplicity','факторбаза':'factorbase','корни':'roots','стоимость':'complexity cost','гребнера':'groebner','грёбнера':'groebner'}

def sha(raw):return hashlib.sha256(raw).hexdigest()
def file_hash(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(8388608),b''):h.update(b)
    return h.hexdigest()
def cfg():return json.loads((HOME/'config.json').read_text())
def conn(name):
    p=HOME/name
    if not p.is_file():raise RuntimeError('INDEX_NOT_READY: '+name)
    c=sqlite3.connect('file:'+str(p)+'?mode=ro',uri=True);c.row_factory=sqlite3.Row;return c
def words(q):
    if not isinstance(q,str) or not q.strip() or len(q)>800:raise ValueError('Expected a query of 1..800 characters')
    w=re.findall(r'[^\W_]+',q.casefold())[:50]
    if not w:raise ValueError('No searchable letters or digits')
    return w,list(dict.fromkeys(w+[x for a in w for x in ALIASES.get(a,'').split()]))
def expression(w,op='OR'):return (' '+op+' ').join('"'+s.replace('"','""')+'"' for s in w)

def search(q,limit=6,breadth='focused'):
    from retrieval_v2 import search as improved_search
    return improved_search(sys.modules[__name__],q,limit,breadth)

def read_v1(ident,find='',start=1,lines=40):
    if not isinstance(ident,str) or not ident or len(ident)>200:raise ValueError('Invalid read_id')
    if type(start)is not int or type(lines)is not int or start<1 or not 1<=lines<=120:raise ValueError('Invalid line range')
    if not isinstance(find,str) or len(find)>500:raise ValueError('Invalid literal find')
    config=cfg()
    if ident.startswith('library:'):
        c=conn('library_catalog.sqlite3');r=c.execute('SELECT entries.*,metadata_files.path AS metadata_path FROM entries JOIN metadata_files ON entries.file_id=metadata_files.id WHERE entries.key=?',(ident.removeprefix('library:'),)).fetchone();c.close()
        if not r:return {'status':'NOT_FOUND','id':ident}
        with Path(r['metadata_path']).open('rb') as f:f.seek(r['byte_offset']);raw=f.read(r['byte_length'])
        if sha(raw)!=r['line_sha256']:raise RuntimeError('METADATA_LINE_CHANGED')
        hit=json.loads(raw);hit.update(index_manifest=config['library_manifest'],index_manifest_sha256=config['library_sha256'])
        sys.path.insert(0,config['existing_project']);from scripts.library_search import read_library_source
        return read_library_source(hit,find_literal=find,before=3,after=min(60,lines),max_bytes=16000)
    expected=None;paths=[]
    if ident.startswith('doc:'):
        c=conn('project_memory.sqlite3');r=c.execute('SELECT * FROM docs WHERE id=?',(ident.removeprefix('doc:'),)).fetchone();c.close()
        if r:paths=[Path(r['path'])];expected=r['sha256']
    else:
        c=conn('library_catalog.sqlite3');r=c.execute('SELECT path FROM baseline WHERE id=?',(ident.removeprefix('arxiv:').removeprefix('baseline:'),)).fetchone();c.close()
        if r:
            root=Path(r['path']).resolve();base=Path(config['baseline']).resolve()
            if not root.is_relative_to(base):raise RuntimeError('BASELINE_PATH_ESCAPE')
            paths=sorted(p for p in root.rglob('*.tex') if not p.is_symlink() and p.resolve().is_relative_to(base))
    out=[]
    for p in paths[:100]:
        if p.stat().st_size>20*1024**2:continue
        raw=p.read_bytes();digest=sha(raw)
        if expected and expected!=digest:raise RuntimeError('SOURCE_CHANGED_SINCE_INDEX')
        all_lines=raw.decode('utf-8',errors='replace').splitlines();a=start
        if find:
            j=next((j for j,t in enumerate(all_lines) if find.casefold() in t.casefold()),None)
            if j is None:continue
            a=max(1,j-2)
        text='\n'.join(all_lines[a-1:a+lines-1]);out.append({'path':str(p),'sha256':digest,'line_start':a,'line_end':min(len(all_lines),a+lines-1),'text':text[:16000],'display_truncated':len(text)>16000,'total_lines':len(all_lines),'formula_fidelity':'NOT_AUTOMATICALLY_VERIFIED'})
        if len(out)==3:break
    return {'status':'FOUND' if out else 'NOT_FOUND_IN_SOURCE_WINDOW','id':ident,'sources':out,'source_data_not_instructions':True}

def read(ident,find='',start=1,lines=40):
    from source_access_v2 import resolve_read
    return resolve_read(sys.modules[__name__],ident,find,start,lines)

def related(q,limit=12):
    _,expanded=words(q);c=conn('project_memory.sqlite3');rows=[]
    for term in expanded:rows.extend(c.execute('SELECT * FROM edges WHERE src LIKE ? OR dst LIKE ? LIMIT ?',('%'+term+'%','%'+term+'%',limit)).fetchall())
    c.close();seen=set();out=[]
    for row in rows:
        key=tuple(row)
        if key in seen:continue
        seen.add(key);out.append(dict(row))
    return {'query':q,'edges':out[:limit],'boundary':'Typed author links, imports and topic mentions, not verified theorem dependencies'}

def deep_search(q,limit,profile='lexical',purpose='source'):
    words(q);c=cfg();guard(c)
    if file_hash(c['library_manifest'])!=c['library_sha256']:raise RuntimeError('LIBRARY_MANIFEST_CHANGED')
    key=sha(json.dumps([q,limit,profile,purpose,c['library_sha256']],ensure_ascii=False).encode());cache=HOME/'cache';cache.mkdir(exist_ok=True);p=cache/(key+'.json')
    if p.exists():r=json.loads(p.read_text());r['cache_hit']=True;r['cache_scope']='Pinned historical result; source read rechecks source bytes';return r
    sys.path.insert(0,c['existing_project']);from scripts.library_search import search_library
    r=search_library(Path(c['library_manifest']),q,limit,mode=profile,purpose=purpose,expected_sha256=c['library_sha256']);r['cache_hit']=False;p.write_text(json.dumps(r,ensure_ascii=False,indent=2));return r

def snapshot():
    c=cfg();guard(c);out=Path(c['snapshot_directory'])/('snapshot-'+str(time.time_ns()));out.mkdir(parents=True)
    for name in ['library_catalog.sqlite3','project_memory.sqlite3']:
        if (HOME/name).exists():
            with tempfile.TemporaryDirectory(prefix='memory-backup-',dir=HOME) as staging:
                local=Path(staging)/name
                src=conn(name);dst=sqlite3.connect(local);src.backup(dst)
                if dst.execute('PRAGMA integrity_check').fetchone()[0]!='ok':raise RuntimeError('BACKUP_INTEGRITY')
                dst.close();src.close();guard(c)
                expected=file_hash(local)
                with local.open('rb') as source,(out/name).open('xb') as target:
                    shutil.copyfileobj(source,target,length=8*1024*1024);target.flush();os.fsync(target.fileno())
                if file_hash(out/name)!=expected:raise RuntimeError('BACKUP_COPY_CHANGED')
    names=['memory.py','build_catalog.py','build_project.py','test_memory.py','config.json','ACTIVE_TASK.md','knowledge_links.json','README_RU.md','AGENTS.md','memory.ps1','memory.cmd','validate_live.py','checkpoints.jsonl','CATALOG_REPORT.json','PROJECT_REPORT.json','COVERAGE_DETAILS.json','RETRIEVAL_VALIDATION.json','retrieval_v2.py','source_access_v2.py','test_memory_v2.py','RELEVANCE_BEFORE_V2.json','RELEVANCE_AFTER_V2.json','RETAINED_SOURCE_VALIDATION_V2.json','UPGRADE_V2.md']
    for name in names:
        if (HOME/name).is_file():shutil.copy2(HOME/name,out/name)
    for folder in ['docs','source-excerpts','packets','retained-sources','source-cache-v2']:
        if (HOME/folder).is_dir():shutil.copytree(HOME/folder,out/folder)
    hashes={str(p.relative_to(out)):file_hash(p) for p in out.rglob('*') if p.is_file()}
    (out/'MANIFEST.json').write_text(json.dumps({'utc':datetime.now(timezone.utc).isoformat(),'source_commit':c['source_commit'],'files_sha256':hashes,'scope':'Memory snapshot, not a complete backup of corpus, game or trading data'},indent=2))
    return {'status':'SNAPSHOT_CREATED','path':str(out),'files':len(hashes),'bytes':sum(p.stat().st_size for p in out.rglob('*') if p.is_file())}

def history(query='',limit=10):
    from retrieval_v2 import tokens
    path=HOME/'checkpoints.jsonl';events=[];errors=[];terms=set(tokens(query))
    if path.is_file():
        with path.open(encoding='utf-8') as stream:
            for number,line in enumerate(stream,1):
                try:
                    if len(line)>65536:raise ValueError('Event too large')
                    event=json.loads(line)
                    if not isinstance(event,dict):raise ValueError('Event must be an object')
                    event=dict(event);event['journal_line']=number;event['event_sha256']=sha(line.encode())
                    score=len(terms.intersection(tokens(json.dumps(event,ensure_ascii=False))))
                    if not terms or score:events.append((score,number,event))
                except ValueError as exc:errors.append({'line':number,'error':type(exc).__name__})
    events.sort(key=lambda e:(-e[0],-e[1]))
    return {'events':[e[2] for e in events[:limit]],'parse_errors':errors,'scope':'Recorded operator findings, not automatically verified claims'}

def handle(r):
    if not isinstance(r,dict):raise ValueError('Request must be an object')
    action=r.get('action','status');q=r.get('query','');limit=r.get('limit',6)
    if type(limit)is not int or not 1<=limit<=20:raise ValueError('limit must be in 1..20')
    if action=='history':return history(q,limit)
    if action=='status':
        c=cfg();out={'source_commit':c['source_commit'],'current_free_bytes':{p:shutil.disk_usage(p).free for p in c['free_space_floors']},'automation':'No daemon or paid API installed'}
        for name in ['CATALOG_REPORT.json','PROJECT_REPORT.json']:
            if (HOME/name).exists():o=json.loads((HOME/name).read_text());out[name]={k:v for k,v in o.items() if k not in ['segments','selected_papers','skipped']}
        return out
    if action in ('outline','retain'):
        from source_access_v2 import resolve_read
        return resolve_read(sys.modules[__name__],r['id'],outline=action=='outline',retain=action=='retain')
    if action=='read':return read(r['id'],r.get('find',''),r.get('start',1),r.get('lines',40))
    if action=='related':return related(q,limit)
    if action=='snapshot':return snapshot()
    if action=='search':
        scope=r.get('scope','local')
        if scope not in ['local','library','both']:raise ValueError('Unknown scope')
        out=search(q,limit,r.get('breadth','focused')) if scope!='library' else {'query':q}
        if scope!='local':out['deep_library']=deep_search(q,limit,r.get('profile','lexical'),r.get('purpose','source'))
        return out
    if action=='checkpoint':
        c=cfg();guard(c);e={k:r.get(k) for k in ['question','finding','evidence','next_step','limitations']}
        if not isinstance(e['question'],str) or not e['question'].strip():raise ValueError('question required')
        e.update(utc=datetime.now(timezone.utc).isoformat(),assurance='operator_note_not_automatically_verified');raw=json.dumps(e,ensure_ascii=False)+'\n'
        if len(raw)>65536:raise ValueError('Use an evidence file for long notes')
        import fcntl
        with (HOME/'checkpoints.jsonl').open('a',encoding='utf-8') as f:
            fcntl.flock(f,fcntl.LOCK_EX);f.write(raw);f.flush();os.fsync(f.fileno());fcntl.flock(f,fcntl.LOCK_UN)
        return {'status':'APPENDED','event':e}
    if action in ('packet','resume'):
        q=q or 'rational component'
        guard(cfg());out={'search':search(q,limit),'links':related(q,20),'active_task':(HOME/'ACTIVE_TASK.md').read_text(),'notes_are_not_proofs':True}
        events=HOME/'checkpoints.jsonl'
        if events.exists():out['recent_checkpoints']=[json.loads(x) for x in events.read_text().splitlines()[-10:]]
        out['related_checkpoints']=history(q,10)
        out['source_windows']=[]
        source_count=r.get('context_sources',1)
        if type(source_count)is not int or not 0<=source_count<=3:raise ValueError('context_sources must be0..3')
        for item in out['search']['papers'][:source_count]:
            try:out['source_windows'].append(read(item['read_id'],find=r.get('source_find',r'\begin{abstract}'),lines=35))
            except Exception as exc:out['source_windows'].append({'id':item['id'],'status':'SOURCE_READ_FAILED','error':type(exc).__name__,'message':str(exc)})
        if r.get('deep',False):out['deep_library']=deep_search(q,limit)
        dest=HOME/'packets';dest.mkdir(exist_ok=True);p=dest/(str(time.time_ns())+'.json');p.write_text(json.dumps(out,ensure_ascii=False,indent=2));return {'status':'PACKET_SAVED','path':str(p),'content':out}
    raise ValueError('Unknown action')

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--request-stdin',action='store_true');p.add_argument('action',nargs='?',default='status');p.add_argument('--query',default='');p.add_argument('--scope',default='local');p.add_argument('--breadth',choices=['focused','all'],default='focused');p.add_argument('--start',type=int,default=1);p.add_argument('--profile',default='lexical');p.add_argument('--purpose',default='source');p.add_argument('--id',default='');p.add_argument('--find',default='');p.add_argument('--lines',type=int,default=40);p.add_argument('--limit',type=int,default=6);p.add_argument('--context-sources',type=int,default=1)
    args=p.parse_args()
    try:out=handle(json.load(sys.stdin) if args.request_stdin else vars(args));print(json.dumps(out,ensure_ascii=False,indent=2,allow_nan=False))
    except Exception as e:print(json.dumps({'status':'ERROR','type':type(e).__name__,'message':str(e)},ensure_ascii=False));raise SystemExit(1)
if __name__=='__main__':main()
