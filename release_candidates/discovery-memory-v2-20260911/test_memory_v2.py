# SPDX-License-Identifier: Apache-2.0
"""Additional engineering checks, using synthetic sources. Not peer review."""
import hashlib,json,sqlite3,sys,types,unittest
from pathlib import Path
from unittest.mock import patch
import memory,retrieval_v2,source_access_v2,test_memory

class RoutingTests(unittest.TestCase):
    def setUp(self):self.fixture=test_memory.MemoryTests();self.fixture.setUp()
    def tearDown(self):self.fixture.tearDown()
    def test_arxiv_url(self):self.assertEqual(memory.search('https://arxiv.org/pdf/1304.1238.pdf',1)['papers'][0]['id'],'1304.1238')
    def test_arxiv_version_disclosed(self):
        r=memory.search('arxiv:1304.1238v2',1);self.assertEqual(r['requested_version'],'v2');self.assertFalse(r['papers'][0]['requested_version_verified'])
    def test_version_read_does_not_substitute(self):self.assertEqual(memory.read('1304.1238v2')['status'],'REQUESTED_VERSION_NOT_VERIFIED')
    def test_legacy_arxiv_id(self):self.assertEqual(retrieval_v2.parse_query('https://arxiv.org/abs/math/0201154v1').key,'math/0201154')
    def test_missing_id_no_or_fallback(self):self.assertEqual(memory.search('9912.99999',3)['papers'],[])
    def test_project_identifier(self):self.assertEqual(memory.search('B-PKC-M16-COMPLETE-COST-BRIDGE',2)['query_kind'],'project')
    def test_invalid_breadth(self):
        with self.assertRaises(ValueError):memory.search('rational',2,'invalid')
    def test_oversize_query(self):
        with self.assertRaises(ValueError):memory.search('a'*801)
    def test_all_language_characters_retained(self):self.assertIn('русская',retrieval_v2.tokens('Русская статья'))
    def test_stopwords(self):self.assertEqual(retrieval_v2.parse_query('How can we find Sparse FGLM').words,('sparse','fglm'))
    def test_arbitrary_url_is_not_fetched(self):self.assertEqual(retrieval_v2.parse_query('https://example.invalid/private').kind,'text')
    def test_tex_accent_query(self):self.assertEqual(retrieval_v2.tokens('Groebner'),['grobner'])
    def test_focused_and_cross_disciplinary_modes(self):
        c=sqlite3.connect(self.fixture.home/'library_catalog.sqlite3')
        c.executemany('INSERT INTO entries VALUES(?,?,?,?,?,?,?)',[
          ('fixture:1','0001.00001','Rational component design for batteries','A','materials','cond-mat.mtrl-sci','EMPTY_SOURCE_TEXT'),
          ('fixture:2','0001.00002','Primary decomposition of zero-dimensional ideals over finite fields','B','A rational component of a polynomial ideal','cs.SC','INDEXED')])
        c.execute("INSERT INTO entries_fts(entries_fts) VALUES('rebuild')");c.commit();c.close()
        self.assertEqual(memory.search('rational component',1,'focused')['papers'][0]['id'],'0001.00002')
        self.assertEqual(memory.search('rational component',1,'all')['papers'][0]['id'],'0001.00001')
    def test_russian_article_metadata(self):
        c=sqlite3.connect(self.fixture.home/'library_catalog.sqlite3');c.execute('INSERT INTO entries VALUES(?,?,?,?,?,?,?)',('fixture:3','0001.00003','Разложение идеалов над конечными полями','Автор','Алгоритм','math.AC','INDEXED'));c.execute("INSERT INTO entries_fts(entries_fts) VALUES('rebuild')");c.commit();c.close()
        self.assertEqual(memory.search('Разложение идеалов',1)['papers'][0]['id'],'0001.00003')

    def test_history_retains_and_finds(self):
        memory.handle({'action':'checkpoint','question':'Frobenius component','finding':'Needs a multiplication matrix'})
        r=memory.handle({'action':'history','query':'Frobenius','limit':3})
        self.assertEqual(len(r['events']),1);self.assertIn('not_automatically_verified',r['events'][0]['assurance'])
    def test_history_reports_invalid_records(self):
        (self.fixture.home/'checkpoints.jsonl').write_text('not json\n')
        self.assertEqual(len(memory.history()['parse_errors']),1)
    def test_snapshot_includes_new_dependencies(self):
        for name in ['retrieval_v2.py','source_access_v2.py']:(self.fixture.home/name).write_text('# fixture module\n')
        r=memory.snapshot();m=json.loads((Path(r['path'])/'MANIFEST.json').read_text())
        self.assertIn('retrieval_v2.py',m['files_sha256']);self.assertIn('source_access_v2.py',m['files_sha256'])

    def test_lowercase_project_id(self):self.assertEqual(memory.search('b-pkc-m16-complete-cost-bridge')['normalized_identifier'],'B-PKC-M16-COMPLETE-COST-BRIDGE')
    def test_groebner_spelling_group(self):self.assertIn('"groebner"',retrieval_v2.expression(['grobner']))

class CachedSourceTests(unittest.TestCase):
    def setUp(self):
        self.fixture=test_memory.MemoryTests();self.fixture.setUp();self.home=self.fixture.home
        self.raw=b'% \\section{Comment only}\n\\section{Actual section}\nAlpha content\nBeta content\n'
        self.pin=hashlib.sha256(self.raw).hexdigest();self.key='a'*64+':1'
        self.metadata_path=self.home/'metadata.jsonl'
        self.hit={'id':'0001.00004','key':self.key,'title':'Synthetic source','full_text_status':'INDEXED','source_version':'fixture','address':{'text_sha256':self.pin,'source_path':str(self.home/'missing-source.parquet'),'source_bytes':0,'source_mtime_ns':0}}
        self.line=(json.dumps(self.hit)+'\n').encode();self.metadata_path.write_bytes(self.line)
        c=sqlite3.connect(self.home/'library_catalog.sqlite3')
        for n,t in [('file_id','INTEGER'),('byte_offset','INTEGER'),('byte_length','INTEGER'),('line_sha256','TEXT')]:c.execute('ALTER TABLE entries ADD COLUMN '+n+' '+t)
        c.execute('CREATE TABLE metadata_files(id INTEGER PRIMARY KEY,path TEXT)');c.execute('INSERT INTO metadata_files VALUES(?,?)',(1,str(self.metadata_path)))
        c.execute('INSERT INTO entries VALUES(?,?,?,?,?,?,?,?,?,?,?)',(self.key,self.hit['id'],'Synthetic source','A','','math.AC','INDEXED',1,0,len(self.line),hashlib.sha256(self.line).hexdigest()));c.commit();c.close()
        config=json.loads((self.home/'config.json').read_text());config.update(library_sha256='b'*64,library_manifest=str(self.home/'manifest.json'),existing_project=str(self.home));(self.home/'config.json').write_text(json.dumps(config))
        cache=self.home/'source-cache-v2';cache.mkdir();self.text_path=cache/(self.pin+'.txt');self.text_path.write_bytes(self.raw)
        ref=cache/(hashlib.sha256((self.key+config['library_sha256']).encode()).hexdigest()+'.json');ref.write_text(json.dumps({'raw_metadata':self.line.decode(),'manifest_sha256':config['library_sha256']}))
        module=types.ModuleType('scripts.library_search');module.classify_source_format=lambda raw,kind:{'members':[{'name':'fixture.tex','format':'TEXT','byte_start':0,'byte_end_exclusive':len(raw)}]}
        package=types.ModuleType('scripts');package.__path__=[]
        self.patch=patch.dict(sys.modules,{'scripts':package,'scripts.library_search':module});self.patch.start()
    def tearDown(self):self.patch.stop();self.fixture.tearDown()
    def test_complete_window_and_next(self):
        a=memory.read('library:'+self.key,start=2,lines=2);b=memory.read('library:'+self.key,start=a['next_start'],lines=2)
        self.assertEqual(a['line_start'],2);self.assertEqual(a['line_end'],3);self.assertEqual(b['line_start'],4);self.assertIsNone(b['next_start'])
    def test_cache_hash_required(self):
        self.text_path.write_bytes(b'changed')
        with self.assertRaisesRegex(RuntimeError,'CACHED_SOURCE_HASH_CHANGED'):memory.read('library:'+self.key)
    def test_metadata_hash_required(self):
        self.metadata_path.write_bytes(b'changed')
        with self.assertRaisesRegex(RuntimeError,'METADATA_LINE_CHANGED'):memory.read('library:'+self.key)
    def test_offline_cached_read_is_labelled(self):
        self.metadata_path.unlink();r=memory.read('library:'+self.key)
        self.assertEqual(r['status'],'FOUND');self.assertFalse(r['original_storage_available']);self.assertTrue(r['cached'])
    def test_outline_omits_comment_headings(self):
        r=source_access_v2.read_library(memory,self.key,outline=True);self.assertEqual(len(r['headings']),1);self.assertEqual(r['headings'][0]['line'],2)
    def test_end_of_source(self):self.assertEqual(memory.read('library:'+self.key,start=500)['status'],'END_OF_SOURCE')
    def test_missing_find(self):self.assertEqual(memory.read('library:'+self.key,find='not present')['status'],'TEXT_MATCH_NOT_FOUND')
    def test_invalid_source_key(self):
        with self.assertRaises(ValueError):source_access_v2.metadata(memory,'../../outside')

    def test_changed_available_manifest_rejected(self):
        (self.home/'manifest.json').write_text('changed')
        with self.assertRaisesRegex(RuntimeError,'LIBRARY_MANIFEST_CHANGED'):memory.read('library:'+self.key)

if __name__=='__main__':unittest.main(verbosity=2)
