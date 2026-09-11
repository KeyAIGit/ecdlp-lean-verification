#!/usr/bin/env python3
"""Reconstruct four source archives, accepting only original SHA-256 bytes.
No target search: replay known certificates and generate coordinate-only data.
Historical timing fields are restored from input metadata, not reported as new.
"""
from pathlib import Path, PurePosixPath
import base64, hashlib, json, lzma, os, shutil, stat, subprocess, sys, zipfile

XZ_SHA = 'e95f51e7fd21c134a9c28ad518dc3725321443724ddb55c2595a4fb9b5b7cc5c'
JSON_SHA = 'b956b5ece60c2b0e5ed0468ae8389d0cecdbc1ba10c0e174b0a5376690b16ae1'


def need(ok, why):
    if not ok: raise RuntimeError(why)


def digest(b): return hashlib.sha256(b).hexdigest()


def run(args, cwd):
    print('RUN', ' '.join(map(str,args)), flush=True)
    subprocess.run(list(map(str,args)), cwd=cwd, check=True, timeout=300)


def restore(descriptor, work):
    obj = json.loads(descriptor)
    need(digest(descriptor) == JSON_SHA, 'descriptor hash mismatch')
    blobs = {h: s.encode('utf-8') for h,s in obj['blobs'].items()}
    for h,b in blobs.items(): need(digest(b)==h, 'text blob hash mismatch')
    latest = next(a for a in obj['archives'] if a['name'].startswith('M16_derivative_'))
    work.mkdir(parents=True, exist_ok=False)
    for e in latest['entries']:
        p = PurePosixPath(e['name'])
        need(not p.is_absolute() and '..' not in p.parts and ':' not in e['name'] and '\\' not in e['name'], 'unsafe entry')
        if e['sha256'] in blobs:
            dst=work/e['name'];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(blobs[e['sha256']])
    root = work/'M16_derivative_continuation'
    old = root/'input/M16_next_100_nodes'
    run([sys.executable,'run_certificate_suite.py'],old)
    for h,spec in obj['regenerate_json'].items():
        if not spec['name'].endswith('/certificate_suite.json'): continue
        p=old/'certificate_suite.json'; data=json.loads(p.read_bytes())
        for path,value in spec['floats']:
            cursor=data
            for key in path[:-1]:cursor=cursor[key]
            cursor[path[-1]]=value
        b=json.dumps(data,indent=2).encode()
        need(digest(b)==h,'certificate reproduction mismatch')
        blobs[h]=b;p.write_bytes(b)
    run([sys.executable,'check_derivative_structure.py'],root)
    for h,spec in obj['regenerate_json'].items():
        if not spec['name'].endswith('/structure_256.json'): continue
        p=root/'results/structure_256.json';data=json.loads(p.read_bytes())
        for path,value in spec['floats']:
            cursor=data
            for key in path[:-1]:cursor=cursor[key]
            cursor[path[-1]]=value
        b=json.dumps(data,indent=2).encode()
        need(digest(b)==h,'structure reproduction mismatch')
        blobs[h]=b;p.write_bytes(b)
    run(['gcc','-O2','-fPIC','-shared','kronecker_gmp.c','-lgmp','-o','kronecker_gmp.so'],old)
    run([sys.executable,'build_usable_polynomial.py','roots'],old)
    run([sys.executable,'build_usable_polynomial.py','build'],old)
    for h,spec in obj['binaries'].items():
        b=(old/Path(spec['path']).name).read_bytes()
        need(len(b)==spec['length'] and digest(b)==h,'binary reproduction mismatch')
        blobs[h]=b
    # Discard generated timings and temporary compilation products from publication.
    # Every published byte below is required to match the original archive hash.
    archives = work/'publish/archives';archives.mkdir(parents=True)
    snapshot=work/'publish/snapshot';snapshot.mkdir()
    for ar in obj['archives']:
        out=archives/ar['name']
        with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
            z.comment=bytes.fromhex(ar['comment'])
            for row in ar['entries']:
                b=blobs[row['sha256']];need(len(b)==row['size'],'size mismatch')
                i=zipfile.ZipInfo(row['name'],tuple(row['date_time']))
                for key in ('compress_type','create_system','create_version','extract_version','reserved','flag_bits','volume','internal_attr','external_attr'):setattr(i,key,row[key])
                i.extra=bytes.fromhex(row['extra']);i.comment=bytes.fromhex(row['comment'])
                z.writestr(i,b,compresslevel=6)
        need(out.stat().st_size==ar['size'] and digest(out.read_bytes())==ar['sha256'],'archive reconstruction mismatch '+ar['name'])
        print('EXACT_ARCHIVE',ar['name'],ar['sha256'],flush=True)
    for row in latest['entries']:
        dst=snapshot/row['name'];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(blobs[row['sha256']])
    report={'schema':'m16-archive-restoration/v1','status':'PASS','archive_count':len(obj['archives']),'snapshot_files':len(latest['entries']),'archives':[{'file':a['name'],'sha256':a['sha256'],'bytes':a['size']} for a in obj['archives']], 'scope':'Byte-identical archival restoration; not new scientific results or historical timing reruns.', 'new_target_searches':0,'lean_checked':False}
    (work/'publish/RESTORE_REPORT.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)


if __name__=='__main__':
    src=Path(sys.argv[1]);work=Path(sys.argv[2])
    if src.is_dir():
        pieces=sorted(src.glob('part*.bin'));need(len(pieces)==9,'need all nine descriptor parts')
        payload=b''.join(p.read_bytes() for p in pieces)
        need(digest(payload)==XZ_SHA,'compressed transport hash mismatch')
        descriptor=lzma.decompress(payload,memlimit=256*1024*1024)
    else:descriptor=src.read_bytes()
    restore(descriptor,work)
