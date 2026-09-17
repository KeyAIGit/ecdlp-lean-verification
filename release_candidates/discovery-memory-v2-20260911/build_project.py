#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Index all pinned project text and selected available baseline sources."""
import hashlib,json,os,re,shutil,sqlite3,subprocess,time
from pathlib import Path
from datetime import datetime,timezone
from build_catalog import guard
HOME=Path(__file__).resolve().parent
PATTERNS=[r'FGLM',r'Krylov',r'Wiedemann',r'zero[ -]dimensional ideal',r'summation polynomial',r'primary decomposition',r'triangular decomposition',r'rational univariate',r'geometric resolution',r'polynomial system.*finite field',r'finite field.*polynomial system',r'elliptic.*discrete logarithm',r'discrete logarithm.*elliptic',r'linear recurrent.*sequence']
TOPICS={'rational-component':['frobenius','rational root','field equation','рациональн'],'norm-chart':['norm chart','norm map','нормов','a+y'],'derivative-support':['derivative','производн','multiplicit','кратност'],'sparse-linear-algebra':['fglm','wiedemann','krylov','berlekamp'],'prime-field-ecdlp':['semaev','summation polynomial','pkc','secp256k1'],'honest-cost':['cost','complexity','стоимост','solving degree']}

def chunks(text):
    lines=text.splitlines();a=0
    while a<len(lines):
        b=a;n=0
        while b<len(lines) and b-a<70 and (n+len(lines[b])+1<=8000 or b==a):n+=len(lines[b])+1;b+=1
        raw='\n'.join(lines[a:b]);yield a+1,b,raw[:8000],len(raw)>8000
        a=b if b-a<=8 else b-8

def build():
    c=json.loads((HOME/'config.json').read_text());guard(c);start=time.monotonic();repo=HOME/'source/ecdlp-lean-verification'
    actual=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
    if actual!=c['source_commit']:raise RuntimeError('PINNED_PROJECT_HEAD_CHANGED')
    if subprocess.check_output(['git','-C',str(repo),'status','--porcelain'],text=True).strip():raise RuntimeError('PINNED_PROJECT_WORKTREE_CHANGED')
    vault=Path('/mnt/d/ResearchVault/parity-secp256k1-epoch');base=Path(c['baseline']).resolve()
    roots=[HOME/'docs',repo,HOME/'source-excerpts',HOME/'retained-sources']
    for n in ['elliptic-20260908-v1','science-boundaries-20260908-v1','sec-definitions-20260908-v1','crypto-definitions-20260908-v1']:roots.append(vault/'corpus-incremental'/n/'documents')
    patterns=[re.compile(p,re.I) for p in PATTERNS];selected=[]
    with (base/'metadata.jsonl').open() as f:
        for line in f:
            r=json.loads(line)
            if any(p.search(r.get('title') or '') for p in patterns):
                p=(base/r['file']).resolve()
                if not p.is_relative_to(base):raise RuntimeError('SELECTED_SOURCE_PATH_ESCAPE')
                selected.append({'id':r['id'],'title':r['title'],'path':str(p)});roots.append(p)
    tmp=HOME/('project-building-'+str(time.time_ns())+'.sqlite3');db=sqlite3.connect(tmp)
    db.executescript("""
      PRAGMA journal_mode=DELETE; PRAGMA synchronous=FULL;
      CREATE TABLE docs(id TEXT PRIMARY KEY,path TEXT,title TEXT,sha256 TEXT,kind TEXT,bytes INTEGER);
      CREATE TABLE chunks(id INTEGER PRIMARY KEY,doc_id TEXT,start_line INTEGER,end_line INTEGER,title TEXT,body TEXT,tags TEXT,truncated INTEGER);
      CREATE VIRTUAL TABLE chunks_fts USING fts5(title,body,tags,content='chunks',content_rowid='id',tokenize='unicode61 remove_diacritics 2');
      CREATE TABLE edges(src TEXT,relation TEXT,dst TEXT,evidence TEXT,UNIQUE(src,relation,dst,evidence));
      CREATE INDEX edges_src ON edges(src);CREATE INDEX edges_dst ON edges(dst);
    """)
    report={'utc':datetime.now(timezone.utc).isoformat(),'source_commit':actual,'documents':0,'chunks':0,'duplicate_documents':0,'selected_papers':selected,'skipped':[],'scope':'Source-located chunks, declared links and lexical topic mentions; not automatically verified mathematics'}
    hashes={};visited=set();skipdirs={'.git','.lake','node_modules','.venv','__pycache__','assets','.pytest_cache','.secrets','secrets'};allowed={'.md','.lean','.py','.tex','.bib','.txt','.rst','.json'}
    for root in roots:
        if not root.is_dir():report['skipped'].append({'path':str(root),'reason':'MISSING_DIRECTORY'});continue
        for parent,dirs,files in os.walk(root,followlinks=False):
            dirs[:]=sorted(n for n in dirs if n not in skipdirs and not (Path(parent)/n).is_symlink())
            for name in sorted(files):
                p=Path(parent)/name
                if p.is_symlink() or p.suffix.lower() not in allowed or str(p) in visited:continue
                visited.add(str(p));maximum=262144 if p.suffix.lower()=='.json' else 4*1024**2
                if p.stat().st_size>maximum:report['skipped'].append({'path':str(p),'reason':'LARGE_SOURCE_REFERENCE_ONLY','bytes':p.stat().st_size});continue
                raw=p.read_bytes()
                try:text=raw.decode('utf-8')
                except UnicodeDecodeError:report['skipped'].append({'path':str(p),'reason':'NOT_UTF8'});continue
                digest=hashlib.sha256(raw).hexdigest()
                if digest in hashes:db.execute('INSERT OR IGNORE INTO edges VALUES(?,?,?,?)',(digest,'identical_bytes_location',str(p),digest));report['duplicate_documents']+=1;continue
                hashes[digest]=str(p);title=next((l.strip('# ').strip() for l in text.splitlines()[:15] if l.startswith('# ')),p.name)
                kind='literature_tex' if '/retained-sources/' in str(p) and p.suffix=='.txt' else 'lean_source' if p.suffix=='.lean' else 'literature_tex' if p.suffix=='.tex' else 'code' if p.suffix=='.py' else 'recorded_data' if p.suffix=='.json' else 'pdf_extracted_text' if p.name=='text.txt' else 'research_document'
                if '/retained-sources/' in str(p) and p.suffix=='.txt' and p.with_name(p.name+'.json').is_file():
                    source_metadata=json.loads(p.with_name(p.name+'.json').read_text());title='arxiv:'+source_metadata['id']+' '+source_metadata['title']
                db.execute('INSERT INTO docs VALUES(?,?,?,?,?,?)',(digest,str(p),title,digest,kind,len(raw)));report['documents']+=1
                tags=' '.join(k for k,values in TOPICS.items() if any(v in text.casefold() for v in values))
                for a,b,body,truncated in chunks(text):db.execute('INSERT INTO chunks(doc_id,start_line,end_line,title,body,tags,truncated) VALUES(?,?,?,?,?,?,?)',(digest,a,b,title,body,tags,int(truncated)));report['chunks']+=1
                for tag in tags.split():db.execute('INSERT OR IGNORE INTO edges VALUES(?,?,?,?)',(digest,'mentions_topic',tag,str(p)))
                for target in re.findall(r'\]\(([^\s)]+)\)',text):db.execute('INSERT OR IGNORE INTO edges VALUES(?,?,?,?)',(digest,'authored_link',target,str(p)))
                for ident in set(re.findall(r'arxiv\.org/(?:abs|pdf|html)/([\w./-]+)',text)):db.execute('INSERT OR IGNORE INTO edges VALUES(?,?,?,?)',(digest,'cites_identifier','arxiv:'+ident.removesuffix('.pdf'),str(p)))
                if p.suffix=='.lean':
                    for module in re.findall(r'^import\s+([\w.]+)',text,re.M):db.execute('INSERT OR IGNORE INTO edges VALUES(?,?,?,?)',(digest,'lean_import',module,str(p)))
                if report['documents']%300==0:guard(c);db.commit()
    graph=HOME/'knowledge_links.json'
    if graph.exists():
        for e in json.loads(graph.read_text())['edges']:db.execute('INSERT OR IGNORE INTO edges VALUES(?,?,?,?)',(e['src'],e['relation'],e['dst'],e['evidence']))
    db.execute("INSERT INTO chunks_fts(chunks_fts) VALUES('rebuild')");db.commit()
    if db.execute('PRAGMA integrity_check').fetchone()[0]!='ok':raise RuntimeError('PROJECT_DB_INTEGRITY')
    report['edges']=db.execute('SELECT count(*) FROM edges').fetchone()[0];db.close();guard(c);dest=HOME/'project_memory.sqlite3'
    if dest.exists():shutil.copy2(dest,HOME/('previous-project-'+str(time.time_ns())+'.sqlite3'))
    os.replace(tmp,dest);report.update(status='READY_LOCAL',database_bytes=dest.stat().st_size,elapsed_seconds=time.monotonic()-start)
    (HOME/'PROJECT_REPORT.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ['selected_papers','skipped']},ensure_ascii=False,indent=2))
if __name__=='__main__':build()
