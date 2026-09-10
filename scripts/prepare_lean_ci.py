#!/usr/bin/env python3
"""Reclaim unused SDK space only on disposable GitHub-hosted Ubuntu 24.04.

Default: show a plan. --apply: remove fixed unused preinstalled SDK directories,
then require 25 GiB free before downloading Lean/Mathlib. Never clean the source,
Lean caches, compiler, Python, Node, or arbitrary caller-supplied paths.
"""
from __future__ import annotations
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
from typing import Mapping

SDK_PATHS = (
    Path('/usr/local/lib/android'), Path('/usr/share/dotnet'),
    Path('/usr/share/swift'), Path('/opt/ghc'), Path('/usr/local/.ghcup'),
    Path('/opt/hostedtoolcache/CodeQL'),
)
MIN_FREE = 25 * 1024**3


def hosted_workspace(env: Mapping[str, str]) -> Path:
    if not (env.get('GITHUB_ACTIONS') == 'true'
            and env.get('RUNNER_ENVIRONMENT') == 'github-hosted'
            and env.get('RUNNER_OS') == 'Linux'
            and env.get('ImageOS') == 'ubuntu24'):
        raise ValueError('Cleanup is restricted to disposable GitHub-hosted Ubuntu 24.04.')
    value = env.get('GITHUB_WORKSPACE', '')
    workspace = Path(value)
    if not value or not workspace.is_absolute() or not workspace.is_dir():
        raise ValueError('An existing absolute GITHUB_WORKSPACE is required.')
    return workspace.resolve()


def validate_target(target: Path, workspace: Path) -> None:
    if target not in SDK_PATHS or target.is_symlink() or target.resolve() != target:
        raise ValueError(f'Not a fixed real SDK directory: {target}')
    if (workspace == target or workspace in target.parents or target in workspace.parents):
        raise ValueError(f'Refusing to overlap repository workspace: {target}')


def prepare(workspace: Path, apply: bool) -> int:
    before = shutil.disk_usage(workspace).free
    print(f'Free before preparation: {before / 1024**3:.2f} GiB')
    # Validate the complete plan before making any changes.
    for target in SDK_PATHS:
        validate_target(target, workspace)
    for target in SDK_PATHS:
        if not target.exists():
            continue
        print(f'{"Remove unused SDK" if apply else "Would remove unused SDK"}: {target}')
        if apply:
            subprocess.run(['sudo', '-n', 'rm', '-rf', '--', str(target)], check=True)
    after = shutil.disk_usage(workspace).free
    print(f'Free after preparation: {after / 1024**3:.2f} GiB')
    if apply and after < MIN_FREE:
        raise ValueError('Less than 25 GiB free; abort before fetching Lean/Mathlib, not during decompression.')
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args(argv)
    try:
        workspace = hosted_workspace(os.environ)
        return prepare(workspace, args.apply)
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        print(f'LEAN CI DISK PREPARATION FAILED: {exc}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
