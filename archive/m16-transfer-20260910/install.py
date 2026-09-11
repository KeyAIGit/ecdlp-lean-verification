# SPDX-License-Identifier: Apache-2.0
"""Install only hash-validated historical archives and update intake disclosures."""
from pathlib import Path
import hashlib, json, shutil, subprocess, sys

repo = Path.cwd().resolve()
publish = Path(sys.argv[1]).resolve()
root = repo / 'release_candidates/m16-20260910'
report = json.loads((publish/'RESTORE_REPORT.json').read_text())
assert report['status'] == 'PASS' and report['archive_count'] == 4
assert report['snapshot_files'] == 98
for row in report['archives']:
    data = (publish/'archives'/row['file']).read_bytes()
    assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256']
    dst = root/'archives'/row['file']; dst.parent.mkdir(parents=True,exist_ok=True)
    assert not dst.exists(), str(dst)
    dst.write_bytes(data)
snapshot = repo/'archive/m16-20260910'
assert not snapshot.exists()
shutil.copytree(publish/'snapshot', snapshot)
(snapshot/'.gitattributes').write_text('* -text\n', encoding='utf-8')
(root/'RESTORE_REPORT.json').write_bytes((publish/'RESTORE_REPORT.json').read_bytes())

p=root/'README.md'; text=p.read_text()
start=text.index('## What is and is not published here')
end=text.index('## Acceptance and attribution',start)
text=text[:start]+'''## Complete archival publication

All four original ZIP archives are now included in [archives/](archives/), with
exact original byte lengths and SHA-256 hashes recorded in `ARCHIVES.sha256`.
The [expanded latest snapshot](../../archive/m16-20260910/M16_derivative_continuation/)
contains 98 original files, including nested earlier inputs, all historical
scripts, fixture matrices, the research-node lists and the large finite-field
polynomial/root arrays. The separate first factor-base ZIP is preserved too.

```sh
python3 release_candidates/m16-20260910/audit_archives.py
```

The audit checks the four ZIP files, every embedded checksum manifest and all
98 expanded files against the original archive bytes. It requires only the
Python standard library. `ARCHIVE_AUDIT.json` is the expected deterministic
report. [Archival replay instructions](ARCHIVAL_REPLAY.md) explain how to run
historical numerical checks in a disposable working copy.

`RESTORE_REPORT.json` records a byte-identical archival restoration. During
transport, deterministic bulky data were regenerated and required to match the
original SHA-256 hashes. Original timing fields were restored as historical
metadata, not represented as new timings. No new-target search was launched.

Historical notes are frozen: statements in them such as "GitHub unchanged"
describe the time of the original research pass, not this publication. The
current publication status is this README and `EVIDENCE.json`. Publishing an
archive does not promote its mathematical assertions or grant status.

'''+text[end:]
text=text.replace('runs 17 regression tests','runs 17 polynomial regression tests plus 2 archive-integrity tests')
p.write_text(text,encoding='utf-8')

(root/'PROGRESS_RU.md').write_text('''# Где сохранён прогресс M16

Полные материалы перенесены в Git в отдельной исследовательской ветке и PR №436.
Это публикация исходных байтов, а не принятие новых математических результатов.
`B-PKC-M16-COMPLETE-COST-BRIDGE` остаётся открытым; счётчики Lean не изменены.

## Публичные материалы

- Четыре исходных ZIP: `archives/`, с проверкой `ARCHIVES.sha256`.
- Развёрнутый последний снимок: `../../archive/m16-20260910/M16_derivative_continuation/`.
- Вложенный предыдущий проход содержит `NODES_100_RU.md`, нормовую карту,
  прежние эксперименты, источники, генератор и полные массивы коэффициентов.
- Текущий снимок содержит `NODES_CONTINUATION.md`, доказательства критерия
  с производной, исходники, журналы и результаты проверок.
- `ARCHIVE_AUDIT.json` и `RESTORE_REPORT.json` фиксируют сохранность публикации.

В развёрнутом снимке 98 оригинальных файлов. Четыре ZIP сохраняют отдельные
исторические этапы; вложенные копии не считаются новыми открытиями или опытами.
Файлы .bin являются массивами элементов конечного поля, не исполняемыми файлами.

## Проверить из чистой копии

```sh
python3 release_candidates/m16-20260910/audit_archives.py
python3 release_candidates/m16-20260910/replay.py
python3 -m unittest discover -s release_candidates/m16-20260910 -p 'test_*.py' -v
```

Подробности повторного запуска исторических программ находятся в
`ARCHIVAL_REPLAY.md`. Их выводы включают изменяющееся время выполнения, поэтому
для опытов используется отдельная рабочая копия, а архивы остаются неизменными.

## Граница подтверждения

Компактная проверка поддержки использует 5043 малых полинома, 57 положительных
случаев полного ранга и 17 регрессионных тестов. Исторические 256-битные
сертификаты заранее построены. Они не являются решением неизвестной цели.
Другая программа того же автора не заменяет внешнюю математическую рецензию.
Письменные доказательства ещё не проверены ядром Lean.

Публикация закрывает пробел хранения, но не стоимость глобального поиска,
не научную новизну общих тождеств и не условия получения гранта. Следующие
задачи: внешняя проверка, точная формализация и исследование полной стоимости.
Оригинальные заметки с фразой «GitHub не изменялся» сохранены как исторические.
Актуальный статус публикации указан здесь и в `EVIDENCE.json`.
''',encoding='utf-8')

(root/'ARCHIVAL_REPLAY.md').write_text('''# Archival replay

## Integrity checks (no numerical search)

From a clean checkout of the feature branch:

```sh
python3 release_candidates/m16-20260910/audit_archives.py
python3 release_candidates/m16-20260910/replay.py
python3 -m unittest discover -s release_candidates/m16-20260910 -p 'test_*.py' -v
```

These checks do not install dependencies or call model APIs. The four ZIP
hashes identify exact original artifacts; the public archive audit also checks
all embedded manifests and 98 expanded source files. Historical logs and their
labels are retained, including unsuccessful and time-limited attempts.

## Rerun historical numerical verification

Extract `archives/M16_derivative_continuation_2026-09-10.zip` into a new
working directory. Use a dedicated Python environment with SymPy 1.14.0.
From its `M16_derivative_continuation` directory, after reviewing the sources:

```sh
python check_derivative_structure.py
python validate_searches.py
```

These commands verify the historical structures and saved small answers; they
are not new searches against an unknown 256-bit target. Generated reports can
contain new timings and therefore need not have the historical report hashes.
Keep them outside the frozen repository snapshot.

The nested `input/M16_next_100_nodes/` directory contains the coefficient/root
arrays and their generator. Rebuilding the arrays with the original fast
multiplication helper requires GCC and GMP development headers on Linux:

```sh
gcc -O2 -fPIC -shared kronecker_gmp.c -lgmp -o kronecker_gmp.so
python build_usable_polynomial.py roots
python build_usable_polynomial.py build
```

The original reports document exact scope, failures, dependencies and timings.
Do not relabel planted inputs as independent targets or finite tests as Lean
proofs. The source-only intake scripts remain separate from canonical proofs.

## Transport provenance

`archive/m16-transfer-20260910/` retains the small lossless descriptor and the
bounded restore/install sources. These were only a transport mechanism. The
final ZIP files themselves are the authoritative original artifacts and can
be downloaded directly; no restoration step is required to read them. The
one-time publishing workflow is removed after successful publication. No
ongoing remote job, new solver campaign or paid inference is configured.
''',encoding='utf-8')

p=root/'EVIDENCE.json';obj=json.loads(p.read_text())
obj['publication_boundary']['included']='All four original ZIPs, 98 expanded latest-snapshot files, nested historical source and fixtures, original finite-field polynomial/root arrays, plus the compact intake and tests.'
obj['publication_boundary']['not_in_git']=[]
obj['publication_boundary']['repeatability']='Public clone contains exact archives and expanded bytes. Standard-library archive audit checks integrity; historical numerical replays require their documented dependencies.'
obj['publication_boundary']['publication_status']='COMPLETE_ARCHIVAL_BYTES_PUBLISHED_IN_FEATURE_BRANCH_NOT_MERGED'
obj['publication_boundary']['historical_notes']='Frozen original statements about no GitHub changes are superseded by this publication metadata only.'
obj['archive_restoration']=report
obj['public_replay']['polynomial_unit_tests']=17
obj['public_replay']['archive_unit_tests']=2
obj['public_replay']['unit_tests']=19
obj['public_archive_audit']={'command':'python3 release_candidates/m16-20260910/audit_archives.py','expected_report':'ARCHIVE_AUDIT.json','scope':'Integrity only, not scientific promotion.'}
p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')

p=root/'GRANT_PLAN.md';text=p.read_text();text=text.replace('Full historical\narchives are not yet publicly replicated by this compact Git package.', 'All four historical archives and the expanded latest snapshot are now public\nin this feature branch; archival publication does not imply external replication.');p.write_text(text,encoding='utf-8')

result=subprocess.run([sys.executable,str(root/'audit_archives.py')],check=True,capture_output=True)
(root/'ARCHIVE_AUDIT.json').write_bytes(result.stdout)
names=[line.split('  ',1)[1] for line in (root/'MANIFEST.sha256').read_text().splitlines() if line]
names=sorted(set(names)|{'audit_archives.py','ARCHIVE_AUDIT.json','ARCHIVAL_REPLAY.md','RESTORE_REPORT.json','test_archives.py'})
(root/'MANIFEST.sha256').write_text(''.join(hashlib.sha256((root/n).read_bytes()).hexdigest()+'  '+n+'\n' for n in names),encoding='utf-8')
print(result.stdout.decode(),flush=True)
print('Installed exact archives and updated publication disclosures.',flush=True)
