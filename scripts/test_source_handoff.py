#!/usr/bin/env python3
"""Source-report regression and hostile-input fixtures, not theorem tests."""
from __future__ import annotations

from contextlib import redirect_stdout, redirect_stderr
import copy
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import source_handoff as h
from lean_portability import build_snapshot, canonical_json_bytes, sha256_bytes


def sealed(snapshot):
    snapshot['content_manifest_sha256'] = sha256_bytes(canonical_json_bytes(snapshot['files']))
    snapshot['snapshot_sha256'] = sha256_bytes(canonical_json_bytes(
        {k: v for k, v in snapshot.items() if k != 'snapshot_sha256'}))
    return snapshot


def fixture(prefix='Example', extra=''):
    files = {
        'LICENSE': b'Fixture license, not a real license grant.\n',
        'lean-toolchain': b'leanprover/lean4:v4.31.0\n',
        f'{prefix}.lean': f'import {prefix}.Basic\n'.encode(),
        f'{prefix}/Basic.lean': (f'import Init\nnamespace {prefix}\n'
            f'theorem example : True := by trivial\n{extra}\nend {prefix}\n').encode(),
    }
    selected = {
        'repository': 'https://github.com/example/' + prefix.lower(),
        'commit_sha': 'a'*40, 'tree_sha': 'b'*40, 'license_file': 'LICENSE',
        'license_sha256': sha256_bytes(files['LICENSE']), 'license_spdx': 'LicenseRef-Fixture',
        'toolchain_file': 'lean-toolchain', 'lean_toolchain': 'leanprover/lean4:v4.31.0',
        'adapter': {'module_roots': [{'path': '.', 'module_prefix': ''}],
                    'owned_module_prefixes': [prefix], 'entrypoints': [prefix], 'explicit_exclusions': []},
    }
    return build_snapshot(Path('.'), {'id': 'FIXTURE', 'task_id': 'TEST', 'selected_source': selected},
                          'a'*40, sorted(files), file_loader=files.__getitem__)


class HandoffTests(unittest.TestCase):
    def setUp(self):
        self.s = fixture()
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def report(self, snapshot=None):
        return h.build_report(self.s if snapshot is None else snapshot, 'c'*64)

    def bad(self, snapshot):
        with self.assertRaises((h.HandoffError, KeyError, TypeError)):
            self.report(sealed(snapshot))

    def test_valid_source_report_has_no_proof_or_customer_promotion(self):
        r = self.report()
        self.assertEqual(r['build_status'], 'not_run')
        self.assertEqual(r['compiled_axiom_audit_status'], 'not_run')
        self.assertFalse(r['candidate_execution_authorized'])
        self.assertEqual(r['customer_validation'], 'not_established')
        self.assertEqual(r['summary']['source_declarations'], 1)

    def test_two_distinct_module_layouts_use_same_renderer(self):
        for prefix in ('Arithmetic', 'Protocol'):
            r = self.report(fixture(prefix))
            self.assertEqual(r['entrypoints'], [prefix])
            self.assertIn(prefix, h.render_markdown(r))

    def test_repeat_is_byte_identical(self):
        a, b = self.report(), self.report()
        self.assertEqual(canonical_json_bytes(a), canonical_json_bytes(b))
        self.assertEqual(h.render_markdown(a), h.render_markdown(b))

    def test_report_digest_is_self_consistent(self):
        r = self.report(); claimed = r.pop('report_sha256')
        self.assertEqual(claimed, sha256_bytes(canonical_json_bytes(r)))

    def test_no_external_commands_are_called(self):
        with patch.object(subprocess, 'run', side_effect=AssertionError('execution forbidden')):
            h.render_markdown(self.report())

    def test_marker_and_axiom_findings_remain_visible(self):
        r = self.report(fixture(extra='theorem unfinished : True := by sorry\naxiom limit : Prop'))
        self.assertEqual(r['summary']['sorry_tokens'], 1)
        self.assertIn('Example.limit', r['declared_axioms_or_constants'])
        self.assertIn('sorry', h.render_markdown(r))
        self.assertEqual(r['build_status'], 'not_run')

    def test_private_module_visibility_is_supported(self):
        self.s['declarations'][0]['visibility'] = 'module_private'
        self.s['summary']['public_source_declarations'] = 0
        self.assertEqual(self.report(sealed(self.s))['summary']['public_source_declarations'], 0)

    def test_snapshot_content_hash_mismatch(self):
        self.s['source']['commit_sha'] = 'd'*40
        with self.assertRaises(h.HandoffError): self.report()

    def test_manifest_content_hash_mismatch(self):
        self.s['content_manifest_sha256'] = '0'*64
        self.s['snapshot_sha256'] = sha256_bytes(canonical_json_bytes(
            {k:v for k,v in self.s.items() if k != 'snapshot_sha256'}))
        with self.assertRaises(h.HandoffError): self.report()

    def test_rehashed_false_summary_rejected(self):
        for key, value in self.s['summary'].items():
            s = copy.deepcopy(self.s)
            if type(value) is int:
                s['summary'][key] += 1
                with self.subTest(key=key): self.bad(s)

    def test_boolean_counts_rejected(self):
        self.s['summary']['source_declarations'] = True
        self.bad(self.s)

    def test_duplicate_file_rejected(self):
        self.s['files'].append(copy.deepcopy(self.s['files'][0])); self.bad(self.s)

    def test_duplicate_module_rejected(self):
        self.s['modules'].append(copy.deepcopy(self.s['modules'][0])); self.bad(self.s)

    def test_missing_module_rejected(self):
        self.s['modules'].pop(); self.bad(self.s)

    def test_declaration_outside_module_rejected(self):
        self.s['declarations'][0]['file'] = 'Other.lean'; self.bad(self.s)

    def test_bad_line_rejected(self):
        self.s['declarations'][0]['line'] = 0; self.bad(self.s)

    def test_bad_paths_rejected(self):
        for value in ('../outside', '/etc/passwd', 'C:\\file', 'a//b', 'x\nname'):
            s = copy.deepcopy(self.s); s['files'][0]['path'] = value
            with self.subTest(value=value): self.bad(s)

    def test_license_identity_rejected(self):
        self.s['source']['license_sha256'] = '0'*64; self.bad(self.s)

    def test_missing_toolchain_rejected(self):
        self.s['source']['toolchain_file'] = 'missing'; self.bad(self.s)

    def test_entrypoint_rejected(self):
        self.s['entrypoints'] = ['Missing']; self.bad(self.s)

    def test_import_classification_rejected(self):
        self.s['modules'][0]['external_imports'].append('NotThere'); self.bad(self.s)

    def test_promoted_evidence_rejected(self):
        for key, value in (('external_evidence', True), ('unlocks_task_012', True),
                           ('evidence_class', 'proof_verified')):
            s = copy.deepcopy(self.s); s[key] = value
            with self.subTest(key=key): self.bad(s)

    def test_unknown_format_rejected(self):
        self.s['schema_version'] = '2.0'; self.bad(self.s)

    def test_html_and_markdown_are_escaped(self):
        self.s['source']['repository'] = '<script>alert(1)</script> [x](javascript:1) `code` |'
        rendered = h.render_markdown(self.report(sealed(self.s)))
        self.assertNotIn('<script>', rendered)
        self.assertNotIn('[x](javascript:', rendered)
        self.assertNotIn('`code`', rendered)
        self.assertIn('&lt;script&gt;', rendered)

    def write_input(self, raw):
        path = self.root/'snapshot.json'; path.write_bytes(raw)
        return path, sha256_bytes(raw)

    def test_raw_input_pin_required_and_checked(self):
        path, sha = self.write_input(canonical_json_bytes(self.s))
        self.assertEqual(h.load_snapshot(path, sha)[0], self.s)
        with self.assertRaises(h.HandoffError): h.load_snapshot(path, '0'*64)

    def test_duplicate_keys_and_nonfinite_numbers_rejected(self):
        for raw in (b'{"a":1,"a":2}', b'{"x":NaN}', b'{"x":Infinity}'):
            path, sha = self.write_input(raw)
            with self.subTest(raw=raw), self.assertRaises(h.HandoffError): h.load_snapshot(path, sha)

    def test_oversized_input_rejected(self):
        path, sha = self.write_input(b'{}'*100)
        with patch.object(h, 'MAX_BYTES', 100), self.assertRaises(h.HandoffError): h.load_snapshot(path, sha)

    def test_input_symlink_refused(self):
        path, sha = self.write_input(b'{}'); link = self.root/'link'; link.symlink_to(path)
        with self.assertRaises(h.HandoffError): h.load_snapshot(link, sha)

    def test_new_directory_contains_both_reports(self):
        r = self.report(); dest = self.root/'out'; h.publish_new_directory(dest, r)
        self.assertEqual(json.loads((dest/'report.json').read_text()), r)
        self.assertEqual((dest/'report.md').read_text(), h.render_markdown(r))

    def test_existing_output_is_preserved(self):
        (self.root/'report.md').write_text('preserve')
        with self.assertRaises(FileExistsError): h.publish_new_directory(self.root, self.report())
        self.assertEqual((self.root/'report.md').read_text(), 'preserve')

    def test_output_symlink_refused(self):
        target = self.root/'target'; target.mkdir(); link = self.root/'link'; link.symlink_to(target)
        with self.assertRaises(h.HandoffError): h.publish_new_directory(link/'out', self.report())
        self.assertEqual(list(target.iterdir()), [])

    def test_bad_cli_input_fails_without_report(self):
        path, sha = self.write_input(b'{')
        with redirect_stderr(io.StringIO()):
            self.assertEqual(h.main(['--snapshot', str(path), '--expected-sha256', sha,
                                     '--output', str(self.root/'out')]), 1)
        self.assertFalse((self.root/'out').exists())

    def test_cli_requires_explicit_pin(self):
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as exc:
            h.main(['--snapshot', 'file.json'])
        self.assertEqual(exc.exception.code, 2)

    def test_demo_pinned_historical_input(self):
        before = h.DEMO.read_bytes()
        with redirect_stdout(io.StringIO()):
            self.assertEqual(h.main(['--demo', '--output', str(self.root/'demo')]), 0)
        self.assertEqual(before, h.DEMO.read_bytes())
        r = json.loads((self.root/'demo/report.json').read_text())
        self.assertEqual(r['source']['commit_sha'], '3f093947b8ae789e9497772815c3a37309ea5566')
        self.assertEqual(r['build_status'], 'not_run')


if __name__ == '__main__':
    unittest.main(verbosity=2)
