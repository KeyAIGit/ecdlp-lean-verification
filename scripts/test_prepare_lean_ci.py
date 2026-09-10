#!/usr/bin/env python3
"""No SDK is deleted by these fixtures; subprocess and disk usage are mocked."""
from pathlib import Path
from collections import namedtuple
from unittest import TestCase, main
from unittest.mock import patch
import tempfile
import prepare_lean_ci as prep

Usage = namedtuple('Usage', 'total used free')

class DiskPreparationTests(TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.env = dict(GITHUB_ACTIONS='true', RUNNER_ENVIRONMENT='github-hosted',
                        RUNNER_OS='Linux', ImageOS='ubuntu24', GITHUB_WORKSPACE=str(self.root))

    def test_hosted_environment(self):
        self.assertEqual(prep.hosted_workspace(self.env), self.root)

    def test_each_missing_environment_guard_rejected(self):
        for key in self.env:
            with self.subTest(key=key), self.assertRaises(ValueError):
                prep.hosted_workspace({k:v for k,v in self.env.items() if k != key})

    def test_self_hosted_rejected(self):
        with self.assertRaises(ValueError):
            prep.hosted_workspace(dict(self.env, RUNNER_ENVIRONMENT='self-hosted'))

    def test_wrong_image_rejected(self):
        with self.assertRaises(ValueError):
            prep.hosted_workspace(dict(self.env, ImageOS='ubuntu22'))

    def test_relative_workspace_rejected(self):
        with self.assertRaises(ValueError):
            prep.hosted_workspace(dict(self.env, GITHUB_WORKSPACE='.'))

    def test_arbitrary_path_rejected(self):
        with self.assertRaises(ValueError):
            prep.validate_target(Path('/tmp/unrelated'), self.root)

    def test_workspace_overlap_rejected(self):
        target = prep.SDK_PATHS[0]
        for workspace in (target, target/'project', target.parent):
            with self.subTest(workspace=workspace), self.assertRaises(ValueError):
                prep.validate_target(target, workspace)

    def test_symlink_rejected(self):
        with patch.object(Path, 'is_symlink', return_value=True), self.assertRaises(ValueError):
            prep.validate_target(prep.SDK_PATHS[0], self.root)

    @patch.object(prep, 'validate_target')
    @patch.object(prep.shutil, 'disk_usage', return_value=Usage(100,20,30*1024**3))
    @patch.object(Path, 'exists', return_value=True)
    @patch.object(prep.subprocess, 'run')
    def test_dry_run_never_deletes(self, run, *_):
        self.assertEqual(prep.prepare(self.root, False), 0)
        run.assert_not_called()

    @patch.object(prep, 'validate_target')
    @patch.object(prep.shutil, 'disk_usage', return_value=Usage(100,20,30*1024**3))
    @patch.object(Path, 'exists', return_value=True)
    @patch.object(prep.subprocess, 'run')
    def test_apply_has_only_fixed_paths_and_no_shell(self, run, *_):
        self.assertEqual(prep.prepare(self.root, True), 0)
        self.assertEqual(run.call_count, len(prep.SDK_PATHS))
        for call, path in zip(run.call_args_list, prep.SDK_PATHS):
            self.assertEqual(call.args[0], ['sudo','-n','rm','-rf','--',str(path)])
            self.assertEqual(call.kwargs, {'check':True})

    @patch.object(prep, 'validate_target')
    @patch.object(prep.shutil, 'disk_usage', return_value=Usage(100,20,1))
    @patch.object(Path, 'exists', return_value=False)
    def test_low_disk_fails_before_download(self, *_):
        with self.assertRaises(ValueError): prep.prepare(self.root, True)

if __name__ == '__main__':
    main(verbosity=2)
