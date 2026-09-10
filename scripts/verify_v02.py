#!/usr/bin/env python3
"""Verify the isolated v0.2 candidates; never promote or publish anything.

--python-only runs exact controls and gate fixtures, explicitly without Lean.
--candidate-only checks the candidate with the repository's pinned Lean toolchain.
--full first requests a clean project rebuild and audits both canonical ledgers.
The existing repository CI is still required; this is not a replacement for it.
No SSH host, model provider, key recovery, or external experiment is invoked.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CANDIDATE = 'release_candidates/v0.2/InformationLoss.lean'
REGISTRY = 'release_candidates/v0.2/axiom_registry.json'


def execute(args: list[str], log: Path, timeout: int = 3600) -> None:
    if log.is_symlink():
        raise RuntimeError('symlink log refused')
    with log.open('wb') as out:
        completed = subprocess.run(args, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT,
                                   timeout=timeout, check=False)
    if completed.returncode:
        raise RuntimeError(f'command exited {completed.returncode}: {args}; see {log.name}')


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--python-only', action='store_true')
    modes.add_argument('--candidate-only', action='store_true')
    modes.add_argument('--full', action='store_true')
    args = parser.parse_args()
    output = ROOT / '_v02_validation'
    # Refuse a redirected report directory. The program writes only local logs.
    if output.is_symlink():
        print('VERIFICATION BLOCKED: report directory is a symlink', file=sys.stderr)
        return 1
    output.mkdir(exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix='run-', dir=output))
    report = {'schema_version': 1, 'mode': 'python-only' if args.python_only else
              ('full' if args.full else 'candidate-only'),
              'checked_at': datetime.now(timezone.utc).isoformat(),
              'candidate_sha256': digest(ROOT / CANDIDATE),
              'source_digests': {name: digest(ROOT / name) for name in
                  (CANDIDATE, REGISTRY, 'scripts/check_axioms.py', 'scripts/v02_replay.py')},
              'candidate_lean_status': 'not_run', 'canonical_build_status': 'not_run',
              'python_status': 'not_run', 'release_ready': False,
              'reason': 'All repository CI, scope review, and release approval remain required.'}
    code = 0
    try:
        execute([sys.executable, '-B', 'scripts/test_check_axioms.py'], output / 'axiom-fixtures.log', 120)
        execute([sys.executable, '-B', 'scripts/v02_replay.py', '--check'], output / 'replay.log', 120)
        report['python_status'] = 'passed'
        if not args.python_only:
            if shutil.which('lake') is None:
                raise RuntimeError('lake is not installed; Lean verification has not run')
            execute(['lake', 'env', 'lean', '--version'], output / 'lean-version.log', 120)
            if args.full:
                # This intentionally invalidates the PROJECT build cache for release
                # evidence. Dependency caches/toolchain binaries remain a trust boundary.
                execute(['lake', 'clean', 'ecdlp'], output / 'lake-clean.log')
                execute(['lake', 'build'], output / 'lake-build.log', 7200)
                for lane, stem, registry in (
                    ('ecdlp', 'Ecdlp/LedgerAxiomAudit.lean', 'data/result_registry.json'),
                    ('researchos', 'ResearchOS/LedgerAxiomAudit.lean', 'data/researchos_result_registry.json')):
                    log = output / f'{lane}-axioms.log'
                    execute(['lake', 'env', 'lean', stem], log)
                    execute([sys.executable, '-B', 'scripts/check_axioms.py', str(log), registry],
                            output / f'{lane}-audit-check.log', 120)
                report['canonical_build_status'] = 'built_and_both_ledgers_audited'
            log = output / 'candidate-axioms.log'
            execute(['lake', 'env', 'lean', CANDIDATE], log, 600)
            execute([sys.executable, '-B', 'scripts/check_axioms.py', str(log), REGISTRY],
                    output / 'candidate-audit-check.log', 120)
            report['candidate_lean_status'] = 'lean_and_exact_axiom_audit_passed'
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as exc:
        report['failure'] = str(exc)
        code = 1
    # A successful component check must not claim the entire release is accepted.
    text = json.dumps(report, indent=2, ensure_ascii=False) + '\n'
    destination = output / f"{report['mode']}-report.json"
    if destination.is_symlink():
        print('VERIFICATION BLOCKED: report file is a symlink', file=sys.stderr)
        return 1
    destination.write_text(text, encoding='utf-8')
    print(text, end='')
    print(f'Report directory: {output}')
    return code


if __name__ == '__main__':
    raise SystemExit(main())
