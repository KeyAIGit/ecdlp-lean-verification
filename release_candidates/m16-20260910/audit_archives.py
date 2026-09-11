# SPDX-License-Identifier: Apache-2.0
"""Check exact archived bytes and expanded sources. No scientific jobs or network."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import stat
import zipfile

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
SIZES = {
    'ecdlp_M16_factorbase_check.zip': 4183,
    'M16_cost_bridge_research_pass_2026-09-10.zip': 50470,
    'M16_next_100_nodes_2026-09-10.zip': 6250466,
    'M16_derivative_continuation_2026-09-10.zip': 6415728,
}

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def safe(name):
    path = PurePosixPath(name)
    require(not path.is_absolute() and '..' not in path.parts and ':' not in name
            and '\\' not in name, 'unsafe archive path: ' + name)
    return path

def run():
    expected = {}
    for line in (ROOT / 'ARCHIVES.sha256').read_text().splitlines():
        digest, name = line.split('  ', 1)
        require(name not in expected, 'duplicate expected archive')
        expected[name] = digest
    require(set(expected) == set(SIZES), 'unexpected archive inventory')
    rows = []
    for name, digest in sorted(expected.items()):
        path = ROOT / 'archives' / name
        raw = path.read_bytes()
        require(len(raw) == SIZES[name] and sha(raw) == digest, 'archive mismatch: ' + name)
        with zipfile.ZipFile(path) as z:
            entries = z.infolist()
            names = [e.filename for e in entries]
            require(len(names) == len(set(names)), 'duplicate ZIP paths')
            for entry in entries:
                safe(entry.filename)
                require(not stat.S_ISLNK(entry.external_attr >> 16), 'ZIP symlink')
                require(entry.file_size <= 10_000_000, 'unexpected expanded size')
            verified = 0
            for member in names:
                if PurePosixPath(member).name.lower() != 'manifest.sha256':
                    continue
                parent = PurePosixPath(member).parent
                for line in z.read(member).decode().splitlines():
                    h, rel = line.split('  ', 1)
                    full = str(parent / safe(rel))
                    require(sha(z.read(full)) == h, 'inner manifest mismatch: ' + full)
                    verified += 1
            expanded = 0
            if name.startswith('M16_derivative_'):
                base = REPO / 'archive' / 'm16-20260910'
                for member in names:
                    file = base / member
                    require(file.is_file() and not file.is_symlink(), 'missing snapshot file')
                    require(file.read_bytes() == z.read(member), 'snapshot mismatch: ' + member)
                    expanded += 1
            rows.append({'file': name, 'bytes': len(raw), 'sha256': digest,
                         'zip_entries': len(entries), 'inner_hash_checks': verified,
                         'snapshot_files_checked': expanded})
    return {'schema': 'm16-public-archive-audit/v1', 'status': 'PASS',
            'archives': rows, 'scope': 'Exact byte preservation, not new science or Lean acceptance.',
            'new_target_searches': 0, 'lean_checked': False}

if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
