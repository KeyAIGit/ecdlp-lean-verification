#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Build a source-bound fast metadata catalog; does not copy article payloads."""
import hashlib,json,os,shutil,sqlite3,sys,time
from pathlib import Path
from datetime import datetime,timezone
HOME=Path(__file__).resolve().parent

def sha(b):return hashlib.sha256(b).hexdigest()
def guard(c):
    for path,floor in c['free_space_floors'].items():
        if not Path(path).exists() or shutil.disk_usage(path).free<floor:raise RuntimeError('STORAGE_RESERVE: '+path)
    if not any(' /mnt/d ' in s and 'D:' in s for s in Path('/proc/mounts').read_text().splitlines()):raise RuntimeError('D_VOLUME_NOT_MOUNTED')

def build():
    c=json.loads((HOME/'config.json').read_text());guard(c);start=time.monotonic()
    mp=Path(c['library_manifest']);raw=mp.read_bytes()
    if sha(raw)!=c['library_sha256']:raise RuntimeError('MANIFEST_CHANGED')
    m=json.loads(raw);root=Path(m['index_root']).resolve()
    tmp=HOME/('catalog-building-'+str(time.time_ns())+'.sqlite3');db=sqlite3.connect(tmp)
    db.executescript("""
    PRAGMA journal_mode=DELETE; PRAGMA synchronous=FULL;
    CREATE TABLE metadata_files(id INTEGER PRIMARY KEY,path TEXT,sha256 TEXT,bytes INTEGER);
    CREATE TABLE entries(key TEXT UNIQUE,id TEXT,title TEXT,authors TEXT,abstract TEXT,categories TEXT,file_id INTEGER,byte_offset INTEGER,byte_length INTEGER,line_sha256 TEXT,full_text_status TEXT);
    CREATE INDEX entry_id ON entries(id);
    CREATE VIRTUAL TABLE entries_fts USING fts5(id,title,authors,abstract,categories,content='entries',content_rowid='rowid',tokenize='unicode61 remove_diacritics 2');
    CREATE TABLE baseline(id TEXT PRIMARY KEY,path TEXT,metadata_line_sha256 TEXT);
    """)
    report={'utc':datetime.now(timezone.utc).isoformat(),'status':'BUILDING','documents':0,'segments':[],'manifest_sha256':c['library_sha256'],'scope':'Metadata and exact source addresses, not a new full-text index or verification of article versions'}
    for i,e in enumerate(m['segments']):
        guard(c);segment=(root/e['path']).resolve()
        if not segment.is_relative_to(root):raise RuntimeError('SEGMENT_PATH_ESCAPE')
        raw=(segment/'manifest.json').read_bytes()
        if sha(raw)!=e['manifest_sha256']:raise RuntimeError('SEGMENT_MANIFEST_CHANGED')
        spec=json.loads(raw);expected=spec['files_sha256']['metadata.jsonl'];p=segment/'metadata.jsonl'
        digest=hashlib.sha256();offset=0;count=0;batch=[]
        with p.open('rb') as stream:
            for line in stream:
                digest.update(line);r=json.loads(line)
                batch.append((r['key'],r['id'],r.get('title') or '',r.get('authors') or '',r.get('abstract') or '',r.get('categories') or '',i,offset,len(line),sha(line),r.get('full_text_status','UNKNOWN')))
                offset+=len(line);count+=1
                if len(batch)>=2000:db.executemany('INSERT INTO entries VALUES(?,?,?,?,?,?,?,?,?,?,?)',batch);batch=[]
        if batch:db.executemany('INSERT INTO entries VALUES(?,?,?,?,?,?,?,?,?,?,?)',batch)
        if digest.hexdigest()!=expected:raise RuntimeError('METADATA_HASH_CHANGED: '+str(p))
        if count!=e['documents']:raise RuntimeError('SEGMENT_COUNT_CHANGED')
        db.execute('INSERT INTO metadata_files VALUES(?,?,?,?)',(i,str(p),expected,offset));db.commit()
        report['documents']+=count;report['segments'].append({'path':e['path'],'documents':count,'bytes':offset,'sha256':expected})
        progress={'status':'BUILDING','stage':'metadata','documents':report['documents'],'segments':i+1,'expected_segments':len(m['segments']),'elapsed_seconds':time.monotonic()-start}
        (HOME/'CATALOG_PROGRESS.json').write_text(json.dumps(progress))
        if (i+1)%10==0:print(json.dumps(progress),flush=True)
    if report['documents']!=m['coverage']['documents_indexed']:raise RuntimeError('TOTAL_COUNT_CHANGED')
    guard(c);print('BUILDING_FTS',flush=True)
    (HOME/'CATALOG_PROGRESS.json').write_text(json.dumps({'status':'BUILDING','stage':'FTS','documents':report['documents']}))
    db.execute("INSERT INTO entries_fts(entries_fts) VALUES('rebuild')");db.commit()
    base=Path(c['baseline']).resolve();batch=[];n=0;digest=hashlib.sha256()
    with (base/'metadata.jsonl').open('rb') as f:
        for line in f:
            digest.update(line);r=json.loads(line);rel=Path(r['file'])
            if rel.is_absolute() or '..' in rel.parts:raise RuntimeError('BASELINE_PATH_ESCAPE')
            batch.append((r['id'],str(base/rel),sha(line)));n+=1
            if len(batch)>=5000:db.executemany('INSERT INTO baseline VALUES(?,?,?)',batch);batch=[]
    if batch:db.executemany('INSERT INTO baseline VALUES(?,?,?)',batch)
    report['baseline_records']=n;report['baseline_metadata_sha256']=digest.hexdigest();db.commit()
    if db.execute('PRAGMA integrity_check').fetchone()[0]!='ok':raise RuntimeError('SQLITE_INTEGRITY')
    db.close();guard(c);dest=HOME/'library_catalog.sqlite3'
    if dest.exists():shutil.copy2(dest,HOME/('previous-library-'+str(time.time_ns())+'.sqlite3'))
    os.replace(tmp,dest);report.update(status='READY_LOCAL',database_bytes=dest.stat().st_size,elapsed_seconds=time.monotonic()-start)
    (HOME/'CATALOG_REPORT.json').write_text(json.dumps(report,indent=2)+'\n');(HOME/'CATALOG_PROGRESS.json').write_text(json.dumps({'status':'READY_LOCAL','documents':report['documents']}))
    print(json.dumps({k:v for k,v in report.items() if k!='segments'},indent=2),flush=True)
if __name__=='__main__':build()
