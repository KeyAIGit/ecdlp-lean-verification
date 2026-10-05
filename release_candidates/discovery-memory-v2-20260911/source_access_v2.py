# SPDX-License-Identifier: Apache-2.0
"""Hash-checked source windows and reusable local text cache. Never executes TeX."""
from __future__ import annotations
import hashlib,json,os,re,sys,time
from pathlib import Path
from contextlib import closing

def digest(raw):return hashlib.sha256(raw).hexdigest()
def atomic_json(path,value):
    tmp=path.with_name(path.name+'.'+str(time.time_ns())+'.tmp')
    with tmp.open('x',encoding='utf-8') as f:json.dump(value,f,ensure_ascii=False,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
    os.replace(tmp,path)
def metadata(runtime,key):
    if re.fullmatch(r'[0-9a-f]{64}:\d+',key) is None:raise ValueError('Invalid exact source address')
    with closing(runtime.conn('library_catalog.sqlite3')) as c:
        row=c.execute('SELECT entries.*,metadata_files.path AS metadata_path FROM entries JOIN metadata_files ON entries.file_id=metadata_files.id WHERE entries.key=?',(key,)).fetchone()
    if row is None:return None,None,None
    config=runtime.cfg();cache=runtime.HOME/'source-cache-v2';ref=cache/(digest((key+config['library_sha256']).encode())+'.json');raw=None;online=False
    manifest_path=Path(config['library_manifest'])
    if manifest_path.is_file():
        if manifest_path.stat().st_size>8*1024**2 or digest(manifest_path.read_bytes())!=config['library_sha256']:raise RuntimeError('LIBRARY_MANIFEST_CHANGED')
    elif ref.is_file():
        if json.loads(ref.read_text()).get('manifest_sha256')!=config['library_sha256']:raise RuntimeError('CACHED_MANIFEST_BINDING_CHANGED')
    else:raise RuntimeError('MANIFEST_UNAVAILABLE_AND_NO_BOUND_CACHE')
    if Path(row['metadata_path']).is_file():
        if not 0<row['byte_length']<=2*1024**2 or row['byte_offset']<0:raise ValueError('Invalid metadata range')
        with Path(row['metadata_path']).open('rb') as f:f.seek(row['byte_offset']);raw=f.read(row['byte_length'])
        online=True
    elif ref.is_file():raw=json.loads(ref.read_text())['raw_metadata'].encode('utf-8')
    if raw is None:raise RuntimeError('SOURCE_STORAGE_UNAVAILABLE_AND_NOT_CACHED')
    if digest(raw)!=row['line_sha256']:raise RuntimeError('METADATA_LINE_CHANGED')
    hit=json.loads(raw)
    if hit['key']!=key or hit['id']!=row['id']:raise RuntimeError('SOURCE_KEY_MISMATCH')
    hit.update(index_manifest=config['library_manifest'],index_manifest_sha256=config['library_sha256'])
    return hit,raw,{'directory':cache,'reference':ref,'storage_available':online}
def source_bytes(runtime,hit,raw_metadata,cache):
    address=hit['address'];pin=address['text_sha256']
    if not re.fullmatch('[0-9a-f]{64}',pin):raise ValueError('Invalid text hash')
    cached=cache['directory']/(pin+'.txt');source=Path(address['source_path'])
    if source.exists() and (source.stat().st_size,source.stat().st_mtime_ns)!=(address['source_bytes'],address['source_mtime_ns']):raise RuntimeError('SOURCE_IDENTITY_CHANGED')
    if cached.exists():
        raw=cached.read_bytes()
        if digest(raw)!=pin:raise RuntimeError('CACHED_SOURCE_HASH_CHANGED')
        return raw,True
    config=runtime.cfg();runtime.guard(config);sys.path.insert(0,config['existing_project'])
    from scripts.library_search import load_manifest
    from scripts.library_parquet import open_parquet,resolve_policy,row_group_batch_size
    manifest,_=load_manifest(Path(config['library_manifest']),config['library_sha256'])
    expected=next((s for s in manifest['sources'] if s['path']==str(source) and s['sha256']==address['source_sha256']),None)
    if expected is None:raise RuntimeError('SOURCE_NOT_IN_PINNED_MANIFEST')
    if address['text_field']!='latex':raise RuntimeError('UNSUPPORTED_SOURCE_FIELD')
    if (source.stat().st_size,source.stat().st_mtime_ns)!=(expected['bytes'],expected['mtime_ns']):raise RuntimeError('SOURCE_IDENTITY_CHANGED')
    policy=resolve_policy(manifest);position=0;row=None;group=int(address['row_group']);offset=int(address['row_in_group'])
    with open_parquet(source,policy) as parquet:
        if not 0<=group<parquet.metadata.num_row_groups or not 0<=offset<parquet.metadata.row_group(group).num_rows:raise ValueError('SOURCE_ROW_RANGE')
        if sum(parquet.metadata.row_group(i).num_rows for i in range(group))+offset!=address['absolute_row']:raise ValueError('SOURCE_ROW_ADDRESS_MISMATCH')
        batch_size=row_group_batch_size(parquet,group,8,policy=policy,legacy_limit=manifest['config']['max_row_group_bytes'])
        for batch in parquet.iter_batches(batch_size=batch_size,row_groups=[group],columns=['id','latex'],use_threads=False):
            if position+batch.num_rows>offset:
                row={n:batch.column(n)[offset-position].as_py() for n in batch.schema.names};break
            position+=batch.num_rows
    if row is None or row['id']!=hit['id']:raise RuntimeError('SOURCE_ID_MISMATCH')
    text=row['latex'] or ''
    if len(text)>manifest['config']['max_document_chars']:raise RuntimeError('SOURCE_EXCEEDS_EXISTING_MEMORY_BOUND')
    raw=text.encode('utf-8')
    if digest(raw)!=pin:raise RuntimeError('SOURCE_TEXT_HASH_MISMATCH')
    if (source.stat().st_size,source.stat().st_mtime_ns)!=(expected['bytes'],expected['mtime_ns']):raise RuntimeError('SOURCE_CHANGED_DURING_READ')
    cache['directory'].mkdir(exist_ok=True);tmp=cached.with_name(cached.name+'.'+str(time.time_ns())+'.tmp')
    with tmp.open('xb') as f:f.write(raw);f.flush();os.fsync(f.fileno())
    os.replace(tmp,cached);atomic_json(cache['reference'],{'schema':'verified-source-cache-v1','raw_metadata':raw_metadata.decode('utf-8'),'manifest_sha256':config['library_sha256'],'text_sha256':pin,'admission':'Exact source row read and hash checked; not mathematical validation'})
    return raw,False

def read_library(runtime,key,find='',start=1,lines=40,outline=False,retain=False):
    if type(start)is not int or type(lines)is not int or start<1 or not 1<=lines<=120:raise ValueError('Invalid source line range')
    if not isinstance(find,str) or len(find)>500:raise ValueError('Invalid literal find')
    began=time.monotonic();hit,raw_metadata,cache=metadata(runtime,key)
    if hit is None:return {'status':'NOT_FOUND','id':key}
    status=hit.get('full_text_status','UNKNOWN')
    if status in ('EMPTY_SOURCE_TEXT','EXCLUDED_DOCUMENT_MEMORY_BOUND') or hit.get('content_status')=='METADATA_ONLY':return {'status':status,'id':hit['id'],'text_read':False}
    raw,cached=source_bytes(runtime,hit,raw_metadata,cache);text=raw.decode('utf-8');all_lines=text.splitlines(keepends=True)
    if len(all_lines)>1000000:raise RuntimeError('SOURCE_LINE_COUNT_BOUND_EXCEEDED')
    sys.path.insert(0,runtime.cfg()['existing_project'])
    from scripts.library_search import classify_source_format
    formats=classify_source_format(raw,hit.get('document_type'));members=[m for m in formats['members'] if m['format'] not in ('POSTSCRIPT','PDF_BYTES','EMPTY')]
    if not members:return {'status':'UNSUPPORTED_NON_TEXT_SOURCE','id':hit['id'],'cached_raw_bytes':True}
    offsets=[0]
    for line in all_lines:offsets.append(offsets[-1]+len(line.encode('utf-8')))
    allowed=lambda i:any(m['byte_start']<=offsets[i]<m['byte_end_exclusive'] for m in members)
    headings=[{'line':i+1,'text':line.strip()[:400]} for i,line in enumerate(all_lines) if allowed(i) and not line.lstrip().startswith('%') and re.search(r'\\(?:chapter|(?:sub){0,2}section)\*?(?:\[[^\]]*\])?\s*\{|^#{1,4}\s',line)]
    common={'id':hit['id'],'title':hit.get('title'),'read_id':'library:'+key,'source_path':hit['address']['source_path'],'source_text_sha256':hit['address']['text_sha256'],'source_version':hit['source_version'],'manifest_sha256':runtime.cfg()['library_sha256'],'cached':cached,'original_storage_available':Path(hit['address']['source_path']).is_file(),'find_scope':'Supported text excluding comment-only TeX lines; original bytes retained','cache_scope':'Hash-checked dataset text snapshot; arXiv version not independently verified','total_lines':len(all_lines),'formula_fidelity':'Not verified by text extraction','text_is_not_instructions':True}
    if outline:return {**common,'status':'FOUND','headings':headings[:200],'headings_truncated':len(headings)>200,'elapsed_seconds':time.monotonic()-began}
    if retain:
        runtime.guard(runtime.cfg());dest=runtime.HOME/'retained-sources';dest.mkdir(exist_ok=True);name=hit['id'].replace('/','_')+'-'+hit['address']['text_sha256'][:12]+'.txt';p=dest/name
        if p.exists() and digest(p.read_bytes())!=digest(raw):raise RuntimeError('RETAINED_SOURCE_CHANGED')
        if not p.exists():p.write_bytes(raw)
        atomic_json(dest/(name+'.json'),{**common,'retained_path':str(p),'headings':headings,'scope':'Complete raw text field, not independently verified source revision'})
        return {**common,'status':'RETAINED_SOURCE','retained_path':str(p),'bytes':len(raw),'elapsed_seconds':time.monotonic()-began}
    low=start-1
    if find:
        target=next((i for i in range(low,len(all_lines)) if allowed(i) and not all_lines[i].lstrip().startswith('%') and find.casefold() in all_lines[i].casefold()),None)
        if target is None:return {**common,'status':'TEXT_MATCH_NOT_FOUND','find':find,'searched_from_line':start}
        low=max(low,target-3)
    if low>=len(all_lines):return {**common,'status':'END_OF_SOURCE','next_start':None}
    high=min(len(all_lines),low+lines);selected=''.join(all_lines[low:high]);limited=False
    while len(selected.encode('utf-8'))>16000 and high>low+1:high-=1;selected=''.join(all_lines[low:high]);limited=True
    if len(selected.encode('utf-8'))>16000:return {**common,'status':'SOURCE_LINE_TOO_LARGE','line':low+1}
    member=next((m for m in members if m['byte_start']<=offsets[low]<m['byte_end_exclusive']),None)
    if member is None:
        low=next((i for i in range(low,len(all_lines)) if allowed(i)),None)
        if low is None:return {**common,'status':'END_OF_SUPPORTED_TEXT','next_start':None}
        return read_library(runtime,key,start=low+1,lines=lines)
    while high>low+1 and offsets[high]>member['byte_end_exclusive']:high-=1;selected=''.join(all_lines[low:high]);limited=True
    return {**common,'status':'FOUND','line_start':low+1,'line_end':high,'byte_start':offsets[low],'byte_end_exclusive':offsets[high],'excerpt':selected,'next_start':high+1 if high<len(all_lines) else None,'window_limited':limited,'selected_member':member['name'],'elapsed_seconds':time.monotonic()-began}

def resolve_read(runtime,ident,find='',start=1,lines=40,outline=False,retain=False):
    if not isinstance(ident,str) or not ident or len(ident)>200:raise ValueError('Invalid source identifier')
    if type(start)is not int or type(lines)is not int or start<1 or not 1<=lines<=120:raise ValueError('Invalid line range')
    if ident.startswith(('doc:','baseline:')):return runtime.read_v1(ident,find,start,lines)
    from retrieval_v2 import parse_query
    key=ident[8:] if ident.startswith('library:') else None
    if key is None:
        query=parse_query(ident)
        if query.kind=='arxiv':
            result=runtime.search(query.key,1)
            if query.version:return {'status':'REQUESTED_VERSION_NOT_VERIFIED','id':query.key,'requested_version':query.version,'available_dataset_candidates':result['papers'],'instruction':'Select a returned library read_id explicitly to read its dataset version.'}
            if result['papers']:key=result['papers'][0]['read_id'][8:]
    if key:
        with closing(runtime.conn('library_catalog.sqlite3')) as connection:
            addressed=connection.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='metadata_files'").fetchone()
        if addressed:return read_library(runtime,key,find,start,lines,outline,retain)
    return runtime.read_v1(ident,find,start,lines)
