#!/usr/bin/env python3
"""Render a pinned source snapshot as a reproducible handoff, without executing it.

Uses the existing lean_portability snapshot format. Hashes establish consistency
with the caller's selected input, not authorship or independent proof validity.
No network, Git/Lake invocation, model request, or target-code import is performed.
"""
from __future__ import annotations

import argparse
from collections import Counter
import html
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys
from typing import Any

from lean_portability import canonical_json_bytes, sha256_bytes

ROOT = Path(__file__).resolve().parents[1]
DEMO = ROOT / 'rehearsals/keyai-portability-001/snapshot.json'
DEMO_SHA256 = '08feefe437e305dc3f444e70cfb1f9d9e27c7efcc9b34cbb6b6669078767050e'
MAX_BYTES = 16 * 1024 * 1024
MAX_ITEMS = 100_000
BOUNDARY = (
    'Source inventory only. No Lean build or compiled axiom audit was run by this tool. '
    'Zero detected markers is not a proof of completeness. Hash consistency does not '
    'authenticate the producer or cited repository. This report is not customer evidence '
    'and does not authorize candidate execution.'
)


class HandoffError(ValueError):
    """Malformed, inconsistent, or unsafe report input."""


def require(ok: bool, message: str) -> None:
    if not ok:
        raise HandoffError(message)


def text(value: Any) -> str:
    require(isinstance(value, str) and 0 < len(value) <= 4096, 'invalid text field')
    require(not any(ord(c) < 32 or 127 <= ord(c) <= 159 for c in value), 'control character in text')
    return value


def relpath(value: Any) -> str:
    value = text(value)
    path = PurePosixPath(value)
    require(not path.is_absolute() and path.as_posix() == value and '..' not in path.parts
            and '\\' not in value and ':' not in value, 'unsafe source path')
    return value


def digest(value: Any, size: int = 64) -> str:
    require(isinstance(value, str) and re.fullmatch(r'[0-9a-f]{' + str(size) + '}', value) is not None,
            'invalid digest')
    return value


def rows(value: Any) -> list[dict]:
    require(isinstance(value, list) and len(value) <= MAX_ITEMS
            and all(isinstance(x, dict) for x in value), 'invalid record list')
    return value


def names(value: Any) -> list[str]:
    require(isinstance(value, list) and len(value) <= MAX_ITEMS, 'invalid name list')
    return [text(x) for x in value]


def count(value: Any) -> int:
    require(type(value) is int and value >= 0, 'invalid nonnegative count')
    return value


def unique_object(pairs: list[tuple[str, Any]]) -> dict:
    result: dict = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def no_symlink_path(path: Path) -> Path:
    path = Path(os.path.abspath(path))
    require(not any(p.is_symlink() for p in (path, *path.parents)), 'symlink path refused')
    return path


def load_snapshot(path: Path, expected: str) -> tuple[dict, str]:
    digest(expected)
    path = no_symlink_path(path)
    require(stat.S_ISREG(path.stat().st_mode), 'snapshot must be a regular file')
    with path.open('rb') as stream:
        raw = stream.read(MAX_BYTES + 1)
    require(len(raw) <= MAX_BYTES, 'snapshot exceeds size limit')
    actual = sha256_bytes(raw)
    require(actual == expected, 'input SHA-256 mismatch')
    value = json.loads(raw.decode('utf-8'), object_pairs_hook=unique_object,
                       parse_constant=lambda _: (_ for _ in ()).throw(HandoffError('non-finite JSON number')))
    require(isinstance(value, dict), 'snapshot must be an object')
    return value, actual


def build_report(snapshot: dict, input_sha256: str) -> dict:
    digest(input_sha256)
    require(snapshot.get('schema_version') == '1.0', 'unsupported snapshot version')
    require(snapshot.get('evidence_class') == 'internal_technical_rehearsal'
            and snapshot.get('external_evidence') is False
            and snapshot.get('unlocks_task_012') is False, 'unsupported evidence classification')
    producer = snapshot['generator']
    require(isinstance(producer, dict), 'invalid generator record')
    require(producer.get('id') == 'keyai-lean-portability' and producer.get('version') == '1.0',
            'unsupported source inventory generator')
    unsigned = {k: v for k, v in snapshot.items() if k != 'snapshot_sha256'}
    require(sha256_bytes(canonical_json_bytes(unsigned)) == digest(snapshot['snapshot_sha256']),
            'snapshot content digest mismatch')
    files = rows(snapshot['files'])
    require(sha256_bytes(canonical_json_bytes(files)) == digest(snapshot['content_manifest_sha256']),
            'file manifest digest mismatch')
    by_path: dict[str, dict] = {}
    for record in files:
        path = relpath(record['path'])
        require(path not in by_path, 'duplicate file path')
        text(record['classification']); count(record['bytes'])
        if record['classification'] != 'gitlink':
            digest(record['sha256'])
        by_path[path] = record
    modules = rows(snapshot['modules'])
    declarations = rows(snapshot['declarations'])
    module_names: set[str] = set()
    module_paths: set[str] = set()
    external_imports: set[str] = set()
    for module in modules:
        name, path = text(module['module']), relpath(module['file'])
        require(name not in module_names and path not in module_paths, 'duplicate module')
        require(path in by_path and by_path[path]['classification'] == 'lean_source'
                and by_path[path]['module'] == name, 'module/file mismatch')
        module_names.add(name); module_paths.add(path)
        external_imports.update(names(module['external_imports']))
    lean_files = [r for r in files if r['classification'] == 'lean_source']
    require(module_paths == {r['path'] for r in lean_files}, 'unmapped Lean file')
    for declaration in declarations:
        require(relpath(declaration['file']) in module_paths, 'declaration outside scoped modules')
        text(declaration['qualified_name']); text(declaration['kind'])
        require(declaration['visibility'] in {'public', 'private', 'module_private'}, 'invalid visibility')
        require(count(declaration['line']) > 0, 'invalid declaration line')
    require(len({(d['file'], d['line'], d['qualified_name']) for d in declarations}) == len(declarations),
            'duplicate declaration record')
    for module in modules:
        imports = names(module['imports'])
        require(imports == names(by_path[module['file']]['imports']), 'module import mismatch')
        require(sorted(names(module['internal_imports'])) == sorted(set(imports) & module_names),
                'internal import classification mismatch')
        require(sorted(names(module['external_imports'])) == sorted(set(imports) - module_names),
                'external import classification mismatch')
    declared_per_file = Counter(d['file'] for d in declarations)
    for record in lean_files:
        require(count(record['declaration_count']) == declared_per_file[record['path']],
                'per-file declaration count mismatch')
    source = snapshot['source']
    require(isinstance(source, dict), 'invalid source record')
    for key in ('commit_sha', 'tree_sha'):
        digest(source[key], 40)
    for key in ('repository', 'license_spdx', 'lean_toolchain'):
        text(source[key])
    license_path, toolchain_path = relpath(source['license_file']), relpath(source['toolchain_file'])
    require(license_path in by_path and by_path[license_path]['sha256'] == digest(source['license_sha256']),
            'license identity mismatch')
    require(toolchain_path in by_path, 'missing toolchain record')
    entrypoints = names(snapshot['entrypoints'])
    require(bool(entrypoints) and len(set(entrypoints)) == len(entrypoints)
            and set(entrypoints) <= module_names, 'invalid entrypoints')
    axioms = sorted(d['qualified_name'] for d in declarations if d['kind'] in {'axiom', 'constant'})
    require(axioms == sorted(names(snapshot['axiom_or_constant_declarations'])), 'axiom list mismatch')
    unsupported = sorted(r['path'] for r in files if r['classification'] == 'lean_out_of_scope'
                         or (r['path'].lower().endswith('.lean') and r['classification'] in {'symlink', 'gitlink'}))
    require(unsupported == sorted(names(snapshot['unsupported_lean_files'])), 'unsupported-file list mismatch')
    summary = {
        'tracked_files': len(files), 'classified_files': len(files),
        'classification_counts': dict(sorted(Counter(r['classification'] for r in files).items())),
        'lean_modules': len(modules), 'source_declarations': len(declarations),
        'public_source_declarations': sum(d['visibility'] == 'public' for d in declarations),
        'anonymous_instances': sum(count(r['anonymous_instance_count']) for r in lean_files),
        'sorry_tokens': sum(count(r['sorry_token_count']) for r in lean_files),
        'admit_tokens': sum(count(r['admit_token_count']) for r in lean_files),
        'axiom_or_constant_declarations': len(axioms), 'unsupported_lean_files': len(unsupported),
    }
    require(isinstance(snapshot['summary'], dict), 'invalid summary')
    require(isinstance(snapshot['summary'].get('classification_counts'), dict), 'invalid classification counts')
    for value in snapshot['summary']['classification_counts'].values():
        count(value)
    require(set(snapshot['summary']) == set(summary), 'unsupported summary fields')
    for key, value in summary.items():
        if key != 'classification_counts':
            count(snapshot['summary'][key])
        require(snapshot['summary'][key] == value, 'summary disagrees with records: ' + key)
    findings = []
    for record in lean_files:
        for marker in ('sorry_token_count', 'admit_token_count'):
            if record[marker]:
                findings.append({'path': record['path'], 'signal': marker, 'count': record[marker]})
    report = {
        'schema_version': '1.0', 'evidence_level': 'source_inventory_only',
        'input_file_sha256': input_sha256, 'snapshot_sha256': snapshot['snapshot_sha256'],
        'content_manifest_sha256': snapshot['content_manifest_sha256'],
        'generator_sha256': sha256_bytes(Path(__file__).read_bytes()),
        'serialization_helper_sha256': sha256_bytes((ROOT / 'scripts/lean_portability.py').read_bytes()),
        'source': {k: source[k] for k in ('repository', 'commit_sha', 'tree_sha', 'license_spdx', 'lean_toolchain')},
        'summary': summary, 'entrypoints': sorted(entrypoints),
        'entrypoint_files': {m['module']: m['file'] for m in modules if m['module'] in entrypoints},
        'external_imports': sorted(external_imports), 'source_findings': findings,
        'declared_axioms_or_constants': axioms, 'unsupported_lean_files': unsupported,
        'build_status': 'not_run', 'compiled_axiom_audit_status': 'not_run',
        'customer_validation': 'not_established', 'candidate_execution_authorized': False,
        'boundary': BOUNDARY,
        'next_action': 'Review adapter coverage and source findings, then use a separately authorized, isolated build and exact axiom audit.',
    }
    report['report_sha256'] = sha256_bytes(canonical_json_bytes(report))
    return report


def cell(value: Any) -> str:
    value = html.escape(str(value), quote=True)
    for char in ('`', '|', '[', ']', '*', '_', '\\'):
        value = value.replace(char, f'&#{ord(char)};')
    return value


def render_markdown(report: dict) -> str:
    lines = ['# KeyAI source handoff', '', '**SOURCE INVENTORY ONLY. NOT A PROOF CERTIFICATE.**', '', BOUNDARY, '',
             '## Pinned input', '', '| Field | Value |', '|---|---|']
    for key, value in report['source'].items():
        lines.append(f"| {cell(key.replace('_', ' '))} | {cell(value)} |")
    lines += ['', '## Source-level observations', '', '| Observation | Count |', '|---|---:|']
    for key, value in report['summary'].items():
        if key != 'classification_counts':
            lines.append(f'| {cell(key.replace("_", " "))} | {value} |')
    lines += ['', 'Counts describe recorded source headings and tokens, not accepted or novel theorems.', '',
              '## Review first', '']
    if report['source_findings']:
        lines += [f"- {cell(r['path'])}: {cell(r['signal'])} = {r['count']}" for r in report['source_findings'][:20]]
        if len(report['source_findings']) > 20:
            lines.append('Only the first 20 findings are shown; see the JSON report for the full list.')
    else:
        lines.append('No incomplete-proof markers are recorded in the configured source scope. This does not establish completeness.')
    for label, key in [('Entrypoints', 'entrypoints'), ('External imports', 'external_imports'),
                       ('Declared axiom/constant headings', 'declared_axioms_or_constants'),
                       ('Unsupported Lean files', 'unsupported_lean_files')]:
        values = report[key]
        lines += ['', f'**{label} ({len(values)}):** ' + (', '.join(cell(x) for x in values[:20]) or 'None recorded.')]
        if len(values) > 20:
            lines.append('Only the first 20 are shown here. The JSON report retains the full list.')
    lines += ['', '## Where to start', '', '| Entrypoint | Source file |', '|---|---|']
    for name, path in sorted(report['entrypoint_files'].items()):
        lines.append(f'| {cell(name)} | {cell(path)} |')
    lines += ['', '## Next action', '', report['next_action'], '',
              'Build: **not run**. Compiled axiom audit: **not run**. Customer validation: **not established**.', '',
              '## Reproducibility', '', '| Digest | SHA-256 |', '|---|---|']
    for key in ('input_file_sha256', 'snapshot_sha256', 'content_manifest_sha256', 'generator_sha256',
                'serialization_helper_sha256', 'report_sha256'):
        lines.append(f'| {cell(key)} | {report[key]} |')
    lines += ['', 'Hashes detect changes against the supplied reference; an attacker can also hash fabricated data.',
              'The demo re-renders a historical internal snapshot. It does not contact or freshly build that project.', '']
    return '\n'.join(lines)


def publish_new_directory(output: Path, report: dict) -> None:
    output = no_symlink_path(output)
    require(output.parent.is_dir(), 'output parent must already exist')
    output.mkdir()  # Refuse overwriting an existing report or other user directory.
    for name, payload in (
        ('report.json', json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + '\n'),
        ('report.md', render_markdown(report)),
    ):
        with (output / name).open('x', encoding='utf-8', newline='\n') as stream:
            stream.write(payload)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    inputs = parser.add_mutually_exclusive_group(required=True)
    inputs.add_argument('--demo', action='store_true', help='render the existing pinned internal rehearsal; no new inspection')
    inputs.add_argument('--snapshot', type=Path, help='existing lean_portability 1.0 snapshot JSON')
    parser.add_argument('--expected-sha256', help='required for --snapshot; obtain from the reviewed source, not this report')
    parser.add_argument('--output', type=Path, help='new directory for Markdown and JSON; default is Markdown on stdout')
    args = parser.parse_args(argv)
    if (args.demo and args.expected_sha256) or (args.snapshot and not args.expected_sha256):
        parser.error('use --demo alone, or --snapshot with --expected-sha256')
    try:
        snapshot, sha = load_snapshot(DEMO if args.demo else args.snapshot,
                                      DEMO_SHA256 if args.demo else args.expected_sha256)
        report = build_report(snapshot, sha)
        if args.output:
            publish_new_directory(args.output, report)
            print('Source-only handoff written. No build, model call, or candidate execution occurred.')
        else:
            print(render_markdown(report), end='')
        return 0
    except (OSError, ValueError, TypeError, KeyError, RecursionError) as exc:
        print(f'SOURCE HANDOFF FAILED: {exc}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
