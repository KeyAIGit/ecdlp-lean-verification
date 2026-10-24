# SPDX-License-Identifier: Apache-2.0
"""Portable adversarial-input tests on synthetic data, not scientific review."""
import hashlib,json,sqlite3,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import memory
from build_catalog import guard

class MemoryTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.home=Path(self.tmp.name)
        self.old_home=memory.HOME;memory.HOME=self.home
        self.mock=patch.object(memory,'guard',lambda config:None);self.mock.start()
        base=self.home/'baseline';(base/'src/1304.1238').mkdir(parents=True)
        (base/'src/1304.1238/main.tex').write_text('Sparse FGLM algorithms\nTheorem A\nRational component\n')
        cfg={'baseline':str(base),'source_commit':'fixture','free_space_floors':{},'snapshot_directory':str(self.home/'snapshots')}
        (self.home/'config.json').write_text(json.dumps(cfg))
        (self.home/'ACTIVE_TASK.md').write_text('Research task, not solved')
        c=sqlite3.connect(self.home/'library_catalog.sqlite3')
        c.executescript('CREATE TABLE entries(key TEXT,id TEXT,title TEXT,authors TEXT,abstract TEXT,categories TEXT,full_text_status TEXT); CREATE VIRTUAL TABLE entries_fts USING fts5(id,title,authors,abstract,categories,content="entries",content_rowid="rowid"); CREATE TABLE baseline(id TEXT,path TEXT);')
        c.execute('INSERT INTO entries VALUES(?,?,?,?,?,?,?)',('fixture:0','1304.1238','Sparse FGLM algorithms','Authors','Finite fields rational component','cs.SC','INDEXED'))
        c.execute('INSERT INTO baseline VALUES(?,?)',('1304.1238',str(base/'src/1304.1238')));c.execute("INSERT INTO entries_fts(entries_fts) VALUES('rebuild')");c.commit();c.close()
        self.note=self.home/'note.md';self.note.write_text('# Rational component\nПроекция сохраняет корни.\nFrobenius field equations.\n',encoding='utf-8');self.digest=hashlib.sha256(self.note.read_bytes()).hexdigest()
        c=sqlite3.connect(self.home/'project_memory.sqlite3')
        c.executescript('CREATE TABLE docs(id TEXT,path TEXT,sha256 TEXT,kind TEXT);CREATE TABLE chunks(id INTEGER PRIMARY KEY,doc_id TEXT,start_line INTEGER,end_line INTEGER,title TEXT,body TEXT,tags TEXT,truncated INTEGER);CREATE VIRTUAL TABLE chunks_fts USING fts5(title,body,tags,content="chunks",content_rowid="id");CREATE TABLE edges(src TEXT,relation TEXT,dst TEXT,evidence TEXT);')
        c.execute('INSERT INTO docs VALUES(?,?,?,?)',(self.digest,str(self.note),self.digest,'research_document'))
        c.execute('INSERT INTO chunks VALUES(?,?,?,?,?,?,?,?)',(1,self.digest,1,3,'Rational component',self.note.read_text(),'rational-component',0));c.execute("INSERT INTO chunks_fts(chunks_fts) VALUES('rebuild')")
        c.execute('INSERT INTO edges VALUES(?,?,?,?)',('rational-component','candidate_method','Frobenius','declared, not proved'));c.commit();c.close()
    def tearDown(self):
        self.mock.stop();memory.HOME=self.old_home;self.tmp.cleanup()
    def test_exact_identifier(self):self.assertEqual(memory.search('arxiv:1304.1238',2)['papers'][0]['id'],'1304.1238')
    def test_title_lookup(self):self.assertEqual(memory.search('Sparse FGLM',2)['papers'][0]['id'],'1304.1238')
    def test_russian_query(self):self.assertTrue(memory.search('Проекция корни',2)['project_and_selected_sources'])
    def test_empty_queries_rejected(self):
        for q in ['', '  ','";*()']:
            with self.assertRaises(ValueError):memory.search(q,2)
    def test_sql_stays_data(self):
        memory.search('" OR 1=1; DROP TABLE entries;',2)
        self.assertEqual(memory.search('1304.1238',2)['papers'][0]['id'],'1304.1238')
    def test_source_hash(self):
        r=memory.read('doc:'+self.digest);self.assertEqual(r['sources'][0]['sha256'],self.digest)
        self.note.write_text('changed')
        with self.assertRaisesRegex(RuntimeError,'SOURCE_CHANGED'):memory.read('doc:'+self.digest)
    def test_baseline_read_and_find(self):self.assertIn('Theorem A',memory.read('1304.1238',find='Theorem',lines=4)['sources'][0]['text'])
    def test_invalid_line_ranges(self):
        for start,count in [(0,2),(1,0),(1,121),(True,3)]:
            with self.assertRaises(ValueError):memory.read('1304.1238',start=start,lines=count)
    def test_typed_links(self):self.assertEqual(memory.related('Фробениус')['edges'][0]['relation'],'candidate_method')
    def test_packet_is_persistent(self):
        r=memory.handle({'action':'packet','query':'rational component','limit':2});self.assertTrue(Path(r['path']).is_file());self.assertTrue(r['content']['notes_are_not_proofs'])
    def test_checkpoint_not_promoted(self):
        r=memory.handle({'action':'checkpoint','question':'Question','finding':'Candidate only'});self.assertIn('not_automatically_verified',r['event']['assurance'])
    def test_snapshot_hashes(self):
        r=memory.snapshot();root=Path(r['path']);m=json.loads((root/'MANIFEST.json').read_text())
        for name,digest in m['files_sha256'].items():self.assertEqual(memory.file_hash(root/name),digest)
    def test_invalid_requests(self):
        for r in [[],{'action':'search','query':'a','limit':True},{'action':'search','query':'a','scope':'accounts'}]:
            with self.assertRaises(ValueError):memory.handle(r)
    def test_reserve_guard(self):
        with self.assertRaisesRegex(RuntimeError,'STORAGE_RESERVE'):guard({'free_space_floors':{'/path/does/not/exist':1}})

if __name__=='__main__':unittest.main(verbosity=2)
