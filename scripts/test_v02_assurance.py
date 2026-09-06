#!/usr/bin/env python3
"""Release-candidate consistency and failure-path fixtures, not proof certificates."""
from __future__ import annotations
import contextlib
import io
import itertools
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import check_axioms as checker
import v02_replay as replay
import verify_v02 as verifier

ROOT = Path(__file__).resolve().parents[1]
CANDIDATES = ROOT / 'release_candidates/v0.2'


class AssuranceTests(unittest.TestCase):
    def test_exact_candidate_registry(self):
        registry = checker.load_registry(CANDIDATES / 'axiom_registry.json')
        expected, known, bases = checker.validate_registry(registry)
        source = (CANDIDATES / 'InformationLoss.lean').read_text(encoding='utf-8')
        declared = {'Ecdlp.ReleaseV02.' + name for name in
                    re.findall(r'^theorem ([A-Za-z_][A-Za-z_0-9]*)', source, re.M)}
        printed = re.findall(r'^#print axioms (\S+)$', source, re.M)
        self.assertEqual(len(expected), 6)
        self.assertEqual(declared, expected)
        self.assertEqual(known, expected)
        self.assertEqual(set(printed), expected)
        self.assertEqual(len(printed), len(expected))
        self.assertTrue(all(base == 'standard' for base in bases.values()))

    def test_candidate_is_init_only(self):
        source = (CANDIDATES / 'InformationLoss.lean').read_text(encoding='utf-8')
        self.assertEqual(re.findall(r'^import (.+)$', source, re.M), ['Init'])
        self.assertIsNone(re.search(r'^\s*(axiom|opaque|unsafe|initialize)\b', source, re.M))
        self.assertNotIn('native_decide', source)
        self.assertNotIn('sorry', source)
        self.assertNotIn('admit', source)

    def test_knowledge_references_exact_registry(self):
        knowledge = json.loads((CANDIDATES / 'knowledge.json').read_text(encoding='utf-8'))
        registry = checker.load_registry(CANDIDATES / 'axiom_registry.json')
        names = {name for record in knowledge['records'] for name in record['lean_declarations']}
        self.assertEqual(names, set(registry['ledger_declarations']))
        self.assertEqual(knowledge['canonical_results_added'], 0)
        ids = [record['id'] for record in knowledge['records']]
        self.assertEqual(len(ids), len(set(ids)))
        for record in knowledge['records']:
            self.assertTrue(record['limitations'])
        pending = next(r for r in knowledge['records'] if r['id'] == 'V02-CYCLE-ANALYTIC-PENDING')
        self.assertEqual(pending['formal_status'], 'not_formalized')
        self.assertEqual(pending['lean_declarations'], [])
        self.assertTrue(pending['required_obligations'])

    def test_frozen_replay_exact(self):
        expected = json.dumps(replay.evaluate(), indent=2, sort_keys=True) + '\n'
        self.assertEqual((CANDIDATES / 'replay.json').read_text(encoding='utf-8'), expected)

    def test_replay_optimized_mode(self):
        process = subprocess.run([sys.executable, '-B', '-O', str(ROOT / 'scripts/v02_replay.py'), '--check'],
                                 capture_output=True, text=True, timeout=120, check=False)
        self.assertEqual(process.returncode, 0, process.stderr + process.stdout)
        self.assertEqual(json.loads(process.stdout)['lean_status'], 'not_run')

    def test_replay_drift_is_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            frozen = Path(folder) / 'replay.json'
            frozen.write_text('{}\n', encoding='utf-8')
            with patch.object(replay, 'OUTPUT', frozen), patch.object(sys, 'argv', ['v02_replay.py', '--check']), contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(replay.main(), 1)
            self.assertEqual(frozen.read_text(encoding='utf-8'), '{}\n')

    def test_invalid_control_parameters(self):
        for n in (0, 1, 2, 4, -3):
            with self.subTest(n=n), self.assertRaises(ValueError):
                replay.negation_pairs(n)
        for m in (0, -1):
            with self.subTest(m=m), self.assertRaises(ValueError):
                replay.local_control(m)

    def test_extended_small_control_family(self):
        for m in range(1, 129):
            result = replay.local_control(m)
            self.assertEqual(2 * result['correct'], result['nonzero_observations'])
            self.assertEqual(result['ordinary_edges'] - result['ordinary_edges_satisfied'], 2)

    def test_boolean_mask_identity_independent(self):
        for a, b, u, v in itertools.product((False, True), repeat=4):
            self.assertEqual(((a != u) != (b != v)) != (a != b), u != v)

    def test_registry_size_limit(self):
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / 'oversized'
            source.write_bytes(b'x' * 65)
            with patch.object(checker, 'MAX_INPUT_BYTES', 64), self.assertRaises(checker.AuditError):
                checker.read_text_bounded(source)

    def test_nested_duplicate_registry_key(self):
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / 'registry.json'
            source.write_text('{"declarations":{"x":{},"x":{}}}', encoding='utf-8')
            with self.assertRaises(checker.AuditError):
                checker.load_registry(source)

    def test_failed_process_is_not_success(self):
        with tempfile.TemporaryDirectory() as folder:
            with self.assertRaises(RuntimeError):
                verifier.execute([sys.executable, '-c', 'raise SystemExit(3)'], Path(folder) / 'failed.log', 10)

    def test_timeout_is_not_success(self):
        with tempfile.TemporaryDirectory() as folder:
            with self.assertRaises(subprocess.TimeoutExpired):
                verifier.execute([sys.executable, '-c', 'import time; time.sleep(2)'], Path(folder) / 'timeout.log', 0.05)

    def test_log_symlink_is_refused(self):
        with tempfile.TemporaryDirectory() as folder:
            target = Path(folder) / 'target'
            target.write_text('preserve', encoding='utf-8')
            link = Path(folder) / 'link'
            link.symlink_to(target)
            with self.assertRaises(RuntimeError):
                verifier.execute([sys.executable, '-c', 'print(1)'], link, 10)
            self.assertEqual(target.read_text(encoding='utf-8'), 'preserve')

    def test_missing_lake_cannot_report_lean_success(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            for name in (verifier.CANDIDATE, verifier.REGISTRY, 'scripts/check_axioms.py', 'scripts/v02_replay.py'):
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((ROOT / name).read_bytes())
            with patch.object(verifier, 'ROOT', root), patch.object(verifier, 'execute'), patch.object(verifier.shutil, 'which', return_value=None), patch.object(sys, 'argv', ['verify_v02.py', '--candidate-only']), contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(verifier.main(), 1)
            reports = list((root / '_v02_validation').glob('run-*/candidate-only-report.json'))
            self.assertEqual(len(reports), 1)
            report = json.loads(reports[0].read_text(encoding='utf-8'))
            self.assertEqual(report['candidate_lean_status'], 'not_run')
            self.assertFalse(report['release_ready'])
            self.assertIn('lake is not installed', report['failure'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
