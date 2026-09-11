# SPDX-License-Identifier: Apache-2.0
"""Two archival-integrity tests in addition to the 17 polynomial regressions."""
import json
import unittest
from pathlib import Path
from audit_archives import run

class ArchiveTests(unittest.TestCase):
    def test_exact_archives_and_expanded_snapshot(self):
        result = run()
        self.assertEqual(result['status'], 'PASS')
        self.assertEqual(len(result['archives']), 4)
        self.assertEqual(sum(r['snapshot_files_checked'] for r in result['archives']), 98)
        self.assertEqual(result['new_target_searches'], 0)
        self.assertFalse(result['lean_checked'])

    def test_saved_report_matches_replay(self):
        saved = Path(__file__).with_name('ARCHIVE_AUDIT.json')
        self.assertEqual(json.loads(saved.read_text()), run())

if __name__ == '__main__':
    unittest.main()
