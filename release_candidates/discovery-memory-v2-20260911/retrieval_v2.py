# SPDX-License-Identifier: Apache-2.0
"""Transparent routing for the existing indexes. No network or corpus writes."""
from __future__ import annotations
import re,time,unicodedata
from dataclasses import dataclass
from contextlib import closing
from urllib.parse import urlparse,unquote
STOP=frozenset('a an the of for to in on and or with using how can we find without from over that this by as is are be'.split())
MATH_CATEGORIES=('cs.SC','math.AC','math.AG','math.NT','cs.CR','cs.CC')
ALIASES={'рациональные':'rational','рациональных':'rational','компонента':'component','компоненты':'components','компонент':'components','фробениус':'frobenius','фробениуса':'frobenius','проекция':'projection','проекции':'projection','уравнений':'equations','производная':'derivative','производной':'derivative','кратности':'multiplicity','кратностей':'multiplicity','корни':'roots','корней':'roots','полином':'polynomial','полиномов':'polynomials','гребнера':'groebner','грёбнера':'groebner','конечные':'finite','конечных':'finite','поля':'fields','полей':'fields','разложение':'decomposition','семаев':'semaev'}
@dataclass(frozen=True)
class Query:
    raw:str
    kind:str
    key:str
    version:str|None
    words:tuple[str,...]
    translated:tuple[str,...]
def tokens(text):
    text=unicodedata.normalize('NFKD',text.casefold())
    text=''.join(c for c in text if not unicodedata.combining(c))
    text=re.sub(r'\\+["\'`^~]','',text).replace('groebner','grobner')
    return re.findall(r'[^\W_]+',text)
def expression(ws,join='AND'):
    return (' '+join+' ').join('"'+w.replace('"','""')+'"' for w in ws)
def parse_query(q):
    if not isinstance(q,str) or not q.strip() or len(q)>800:raise ValueError('Expected a query of1..800 characters')
    original=q.strip();s=original
    if re.match(r'https?://',s,re.I):
        u=urlparse(s)
        if u.hostname in ('arxiv.org','www.arxiv.org','export.arxiv.org'):s=re.sub(r'^/(?:abs|pdf|html)/','',unquote(u.path)).removesuffix('.pdf')
    s=re.sub(r'^arxiv\s*:\s*','',s,flags=re.I)
    a=re.fullmatch(r'(\d{4}\.\d{4,5}|[a-z-]+(?:\.[A-Z]{2})?/\d{7})(v[1-9]\d*)?',s,re.I)
    kind,key,version=('arxiv',a[1],a[2]) if a else ('text',original,None)
    if re.fullmatch(r'(?:B-[A-Z]|NEXT-|TASK-|CQ-|CELL-|HYP-|R-PETIT|R-GLV)[A-Z0-9-]*',original):kind,key='project',original
    ws=tuple(dict.fromkeys(t for t in tokens(key) if t not in STOP))
    if not ws or len(ws)>60:raise ValueError('Expected1..60 searchable terms')
    translated=tuple(dict.fromkeys(t for w in ws for t in ALIASES.get(w,w).split()))
    return Query(original,kind,key,version,ws,translated)
def contextual_variants(q,breadth):
    variants=[('terms',expression(q.words))]
    if q.translated!=q.words:variants.append(('term_translation',expression(q.translated)))
    ts=set(q.translated)
    if breadth=='focused':
        if 'rational' in ts and ts.intersection({'component','components','root','roots'}):variants.append(('algebra_context','("polynomial" OR "ideals" OR "ideal") AND ("finite" OR "frobenius" OR "decomposition") AND ("rational" OR "component" OR "roots" OR "zero-dimensional")'))
        if ts.intersection({'derivative','multiplicity'}) and len(ts)>=2:variants.append(('polynomial_context','("derivative" OR "multiplicity" OR "squarefree") AND ("polynomial" OR "polynomials")'))
    return list(dict.fromkeys(variants))
def topic_relevance(row,q):
    ts=set(tokens((row.get('title') or '')+' '+(row.get('abstract') or '')));qs=set(q.translated);score=0
    if qs.intersection({'component','components','roots','root'}) and 'rational' in qs:score+=5*bool(ts.intersection({'polynomial','polynomials','ideal','ideals'}))+3*bool(ts.intersection({'frobenius','decomposition','dimensional'}))+2*('finite' in ts)
    if qs.intersection({'derivative','multiplicity'}):score+=5*bool(ts.intersection({'polynomial','polynomials','squarefree'}))
    return score
def search(runtime,query,limit=6,breadth='focused'):
    if type(limit)is not int or not 1<=limit<=20:raise ValueError('limit must be in1..20')
    if breadth not in ('focused','all'):raise ValueError('breadth must be focused or all')
    start=time.monotonic();q=parse_query(query);cap=max(60,limit*8);papers=[];channels=[];ranks={};records={}
    with closing(runtime.conn('library_catalog.sqlite3')) as c:
        direct=c.execute('SELECT * FROM entries WHERE id=? LIMIT ?',(q.key,cap)).fetchall() if q.kind=='arxiv' else []
        if direct:
            for n,row in enumerate(direct):records[row['key']]=dict(row);ranks[row['key']]=100-n
            channels.append('exact_arxiv_identifier')
        elif q.kind=='text':
            sql='SELECT entries.*,entries_fts.rank AS lexical_rank FROM entries_fts JOIN entries ON entries.rowid=entries_fts.rowid WHERE entries_fts MATCH ? AND entries_fts.rank MATCH ? ORDER BY entries_fts.rank LIMIT ?'
            for label,expr in contextual_variants(q,breadth):
                found=c.execute(sql,(expr,'bm25(30,12,3,1,2)',cap)).fetchall();channels.append(label)
                for n,row in enumerate(found):records[row['key']]=dict(row);ranks[row['key']]=ranks.get(row['key'],0)+1/(61+n)
            if not records:
                channels.append('broad_or_fallback');found=c.execute(sql,(expression(q.translated,'OR'),'bm25(30,12,3,1,2)',cap)).fetchall()
                for n,row in enumerate(found):records[row['key']]=dict(row);ranks[row['key']]=1/(61+n)
    normalized=' '.join(q.translated)
    def paper_score(item):
        title=' '.join(tokens(item['title'] or ''));category=item.get('categories') or ''
        exact=20 if title==normalized else 8 if title.startswith(normalized) else 0
        usable=1 if item.get('full_text_status')=='INDEXED' else -2
        focus=(2*any(x in category.split() for x in MATH_CATEGORIES)+topic_relevance(item,q)) if breadth=='focused' else 0
        return exact+usable+focus+30*ranks[item['key']]
    ordered=sorted(records.values(),key=lambda r:(-paper_score(r),r['id'],r['key']));seen=set()
    for row in ordered:
        if row['id'] in seen:continue
        seen.add(row['id']);p={k:row.get(k) for k in ('id','title','authors','abstract','categories','full_text_status')}
        p.update(abstract=(p['abstract'] or '')[:1200],read_id='library:'+row['key'],text_read_this_query=False,score=round(paper_score(row),6),requested_version=q.version,requested_version_verified=False,source_version_note='Dataset text is hash-addressed; arXiv revision is not inferred from metadata.',language_policy='No language exclusion',rank_scope='Candidate reranking, not exhaustive relevance assurance');papers.append(p)
        if len(papers)>=limit:break
    docs=[]
    if (runtime.HOME/'project_memory.sqlite3').is_file():
        with closing(runtime.conn('project_memory.sqlite3')) as c:
            sql='SELECT chunks.*,docs.path,docs.sha256,docs.kind,chunks_fts.rank AS lexical_rank FROM chunks_fts JOIN chunks ON chunks.id=chunks_fts.rowid JOIN docs ON docs.id=chunks.doc_id WHERE chunks_fts MATCH ? AND chunks_fts.rank MATCH ? ORDER BY chunks_fts.rank LIMIT ?'
            variants=[('exact_reference','"'+q.key.replace('"','""')+'"')] if q.kind!='text' else contextual_variants(q,'all')
            candidates={};order={}
            for label,expr in variants:
                rows=c.execute(sql,('{title body}: ('+expr+')','bm25(8,1,2)',max(cap,160))).fetchall()
                for n,row in enumerate(rows):candidates[row['id']]=dict(row);order[row['id']]=order.get(row['id'],0)+1/(61+n)
            if not candidates and q.kind=='text':
                rows=c.execute(sql,('{title body}: ('+expression(q.translated,'OR')+')','bm25(8,1,2)',160)).fetchall()
                for n,row in enumerate(rows):candidates[row['id']]=dict(row);order[row['id']]=1/(61+n)
            def doc_score(row):
                path=row['path'];title=' '.join(tokens(row['title']));score=order[row['id']]*30
                if ' '.join(q.words) in title:score+=3
                if row['kind']=='research_document':score+=3
                if '/source-excerpts/' in path:score+=3
                if row['kind'] in ('code','recorded_data'):score-=3
                if q.kind=='project':
                    if path.endswith('/BARRIERS.md') and q.key.startswith('B-'):score+=12
                    if q.key in row['title']:score+=20
                    if '/tasks/' in path:score+=3
                if path.endswith('/docs/ACTIVE_TASK.md') and set(q.translated).intersection({'rational','component','components'}):score+=9
                return score
            per_doc={}
            for row in sorted(candidates.values(),key=lambda r:(-doc_score(r),r['start_line'])):per_doc.setdefault(row['doc_id'],row)
            for row in list(per_doc.values())[:limit]:
                if q.key in row['title'] or row['path'].endswith('/docs/ACTIVE_TASK.md'):
                    first=c.execute('SELECT * FROM chunks WHERE doc_id=? ORDER BY start_line LIMIT 1',(row['doc_id'],)).fetchone()
                    if first:row.update(dict(first))
                text=row['body'];row.update(read_id='doc:'+row['doc_id'],body=text[:1600],excerpt_display_limited=len(text)>1600,assurance='Source excerpt; evidence status is separate from search ranking',citation={'path':row['path'],'sha256':row['sha256'],'lines':[row['start_line'],row['end_line']]});docs.append(row)
    return {'status':'FOUND' if papers or docs else 'NOT_FOUND_IN_SELECTED_INDEXES','query':query,'query_kind':q.kind,'normalized_identifier':q.key if q.kind!='text' else None,'requested_version':q.version,'version_warning':'Requested revision not independently verified; no silent revision substitution.' if q.version else None,'expanded_terms':list(dict.fromkeys(q.words+q.translated)),'expansion_is_not_equivalence':True,'retrieval_channels':channels,'breadth':breadth,'papers':papers,'project_and_selected_sources':docs,'elapsed_seconds':time.monotonic()-start,'scope':'All indexed metadata plus selected local full text; library scope uses the original full-text engine.','ranking_limitations':'Heuristic topic-aware ranking. Use breadth=all for cross-disciplinary exploration. Search rank is not scientific correctness.'}
