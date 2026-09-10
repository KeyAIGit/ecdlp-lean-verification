#!/usr/bin/env python3
"""Mutation fixtures for pending-rights metadata, not a test of legal ownership."""
from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
from copy import deepcopy
import hashlib
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import check_oss_readiness as gate


class ReadinessTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.m = json.loads((gate.ROOT / gate.MANIFEST).read_text())
        names = list(gate.DOCUMENTS) + [gate.MANIFEST]
        names += [row['path'] for row in self.m['license_texts'] + self.m['third_party_files']]
        for name in names:
            p = self.root / name
            p.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(gate.ROOT / name, p)

    def save(self):
        (self.root / gate.MANIFEST).write_text(json.dumps(self.m))

    def invalid(self):
        self.save()
        with self.assertRaises((ValueError, TypeError, KeyError, OSError)):
            gate.inspect(self.root)

    def test_valid_pending_metadata_is_not_clearance(self):
        result = gate.inspect(self.root)
        self.assertFalse(result['release_ready'])
        self.assertEqual(result['reviewed_third_party_files'], 4)

    def test_release_required_fails(self):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            self.assertEqual(gate.main(['--root', str(self.root), '--require-release-ready']), 1)

    def test_default_cli_is_consistency_only(self):
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertEqual(gate.main(['--root', str(self.root)]), 0)
        self.assertIn('PENDING', out.getvalue())

    def test_duplicate_json_keys(self):
        p = self.root / gate.MANIFEST
        p.write_text(p.read_text().replace('"schema_version": 1,', '"schema_version": 1, "schema_version": 1,'))
        with self.assertRaises(ValueError): gate.inspect(self.root)

    def test_malformed_json(self):
        (self.root / gate.MANIFEST).write_text('{')
        with self.assertRaises(ValueError): gate.inspect(self.root)

    def test_boolean_schema_rejected(self):
        self.m['schema_version'] = True; self.invalid()

    def test_missing_approval_field_rejected(self):
        self.m.pop('owner_approval'); self.invalid()

    def test_fabricated_owner_approval(self):
        self.m['owner_approval'] = {'signed': True}; self.invalid()

    def test_claimed_blanket_grant(self):
        self.m['repository_license_granted'] = True; self.invalid()

    def test_false_status_promotion(self):
        self.m['status'] = 'approved'; self.invalid()

    def test_root_license_contradiction(self):
        (self.root / 'LICENSE').write_text('Apache License'); self.invalid()

    def test_blocker_removal(self):
        self.m['blockers'].pop(); self.invalid()

    def test_duplicate_blocker(self):
        self.m['blockers'].append(deepcopy(self.m['blockers'][0])); self.invalid()

    def test_empty_blocker_detail(self):
        self.m['blockers'][0]['required'] = ''; self.invalid()

    def test_missing_known_input(self):
        self.m['third_party_files'].pop(); self.invalid()

    def test_duplicate_source(self):
        self.m['third_party_files'].append(deepcopy(self.m['third_party_files'][0])); self.invalid()

    def test_wrong_license(self):
        self.m['third_party_files'][0]['license'] = 'MIT'; self.invalid()

    def test_modified_font(self):
        (self.root/'fonts/Nunito-Variable.woff2').write_bytes(b'changed'); self.invalid()

    def test_missing_notice(self):
        (self.root/'fonts/OFL-Nunito.txt').unlink(); self.invalid()

    def test_notice_digest_mismatch(self):
        (self.root/'fonts/OFL-Nunito.txt').write_text('edited'); self.invalid()

    def test_duplicate_notice(self):
        self.m['license_texts'].append(deepcopy(self.m['license_texts'][0])); self.invalid()

    def test_rehashed_missing_attribution(self):
        row = self.m['third_party_files'][0]
        p = self.root/row['path']; p.write_text(p.read_text().replace(row['copyright'], ''))
        row['source_sha256'] = hashlib.sha256(p.read_bytes()).hexdigest(); self.invalid()

    def test_new_attributed_lean_file(self):
        (self.root/'Ecdlp/Other.lean').write_text('/-\nCopyright (c) Another author\n-/'); self.invalid()

    def test_unregistered_font(self):
        (self.root/'fonts/Other.ttf').write_bytes(b'font'); self.invalid()

    def test_path_traversal(self):
        self.m['license_texts'][0]['path'] = '../LICENSE'; self.invalid()

    def test_absolute_path(self):
        self.m['license_texts'][0]['path'] = '/etc/passwd'; self.invalid()

    def test_symlink_rejected(self):
        p = self.root/'fonts/OFL-Nunito.txt'; p.unlink(); p.symlink_to(self.root/'fonts/OFL-Baloo2.txt'); self.invalid()

    def test_missing_document(self):
        (self.root/'LICENSING.md').unlink(); self.invalid()

    def test_invalid_commit(self):
        self.m['audited_source_commit'] = 'main'; self.invalid()

    def test_missing_evidence_limit(self):
        self.m['third_party_files'][0]['evidence'] = ''; self.invalid()

    def test_invalid_date(self):
        self.m['review_date'] = 'not-a-date'; self.invalid()

    def test_cli_bad_root(self):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            self.assertEqual(gate.main(['--root', str(self.root/'missing')]), 1)


if __name__ == '__main__':
    unittest.main(verbosity=2)
