#!/usr/bin/env python3
"""Package committed BFGS sources and a standalone corrected LaTeX edition.

Only Git-tracked files from HEAD enter the source snapshot. Build caches,
scratch work, local configuration and untracked files are never traversed.
The full archive carries a self-contained Git bundle for historical audits.
"""
import datetime as dt
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'dist'
FORBIDDEN = {'.git', '.lake', '.toolchain', '.cache', 'tmp', 'scratch', '__pycache__', '.DS_Store'}
SUFFIXES = {'.olean', '.ilean', '.o', '.pyc', '.aux', '.toc', '.fls', '.fdb_latexmk'}
LATEX_PREFIX = 'bfgs_lean_stage1/master_report/latex/'
PDF = 'bfgs_lean_stage1/output/pdf/Rigorous_BFGS_Master_Report.pdf'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def main():
    if not __debug__:
        raise RuntimeError('Run without Python optimization.')
    commit = git('rev-parse', 'HEAD').decode().strip()
    if git('status', '--porcelain', '--untracked-files=no'):
        raise RuntimeError('Commit tracked changes first, or restore them before packaging.')
    timestamp = int(git('show', '-s', '--format=%ct', commit))
    expected_names = set(git('ls-tree', '-r', '--name-only', '-z', commit).decode().rstrip('\0').split('\0'))
    date = dt.datetime.fromtimestamp(timestamp, dt.timezone.utc).timetuple()[:6]
    archive_prefix = ROOT.name + '/'
    OUT.mkdir(exist_ok=True)
    full_path = OUT / 'BFGS_complete_source_and_verification.zip'
    tex_path = OUT / 'BFGS_corrected_report_LaTeX.zip'
    payloads = {'complete': {}, 'latex': {}}
    tracked = {}

    def add(archive, kind, prefix, name, data, mode=0o644, stored=False):
        path = Path(name)
        assert not path.is_absolute() and '..' not in path.parts
        assert not (set(path.parts) & FORBIDDEN), name
        assert path.suffix not in SUFFIXES, name
        info = zipfile.ZipInfo(prefix + name, date_time=date)
        info.create_system = 3
        info.external_attr = (0o100000 | mode) << 16
        info.compress_type = zipfile.ZIP_STORED if stored else zipfile.ZIP_DEFLATED
        archive.writestr(info, data, compresslevel=9)
        assert name not in payloads[kind]
        payloads[kind][name] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

    with tempfile.TemporaryDirectory(prefix='package-', dir=OUT) as temporary:
        bundle = Path(temporary) / 'history.bundle'
        subprocess.run(['git', 'bundle', 'create', str(bundle), 'HEAD'], cwd=ROOT, check=True)
        heads = subprocess.check_output(['git', 'bundle', 'list-heads', str(bundle)], text=True)
        assert heads.strip() == commit + ' HEAD', heads
        with zipfile.ZipFile(full_path, 'w', allowZip64=True) as full, \
                zipfile.ZipFile(tex_path, 'w', allowZip64=True) as tex:
            process = subprocess.Popen(['git', 'archive', '--format=tar', commit], cwd=ROOT, stdout=subprocess.PIPE)
            with tarfile.open(fileobj=process.stdout, mode='r|') as stream:
                for member in stream:
                    if member.isdir():
                        continue
                    assert member.isfile(), ('Nonregular committed file', member.name)
                    name = member.name
                    data = stream.extractfile(member).read()
                    mode = member.mode & 0o777
                    add(full, 'complete', archive_prefix, name, data, mode)
                    tracked[name] = payloads['complete'][name]
                    if name.startswith(LATEX_PREFIX):
                        add(tex, 'latex', archive_prefix, name, data, mode)
                    elif name == PDF:
                        add(tex, 'latex', archive_prefix, name, data)
            assert process.wait() == 0
            process.stdout.close()
            assert set(tracked) == expected_names, 'Snapshot differs from the independently listed Git tree'
            assert len([name for name in payloads['latex'] if name.endswith('.tex')]) == 30
            assert set(payloads['latex']) == {name for name in expected_names if name.startswith(LATEX_PREFIX) or name == PDF}
            add(full, 'complete', archive_prefix, '_archive/history.bundle', bundle.read_bytes(), stored=True)
            add(full, 'complete', archive_prefix, '_archive/restore_git_history.py',
                git('show', commit + ':packaging/restore_git_history.py'), 0o755)
            full_readme = f'''# Complete BFGS source and verification package

Source commit: {commit}

The outer folder retains the original name, {ROOT.name}. Every committed file
keeps its exact repository-relative path; no source file is flattened or moved.
Archive-only instructions, inventories and history helpers are supplemental.

This contains the exact committed project, corrected report/PDF, editable
authoring inputs, original research sources, Lean proofs, pinned dependency
records, compiler/axiom logs, literature audit and all sealed review evidence.
Open bfgs_lean_stage1/output/pdf/Rigorous_BFGS_Master_Report.pdf to read the report.
Its LaTeX entry point is bfgs_lean_stage1/master_report/latex/master.tex.

Excluded: .lake, .toolchain, .cache, tmp, audit/scratch, Python caches, raw .git,
untracked duplicate documents, compiled objects and local machine configuration.
Actual archived compiler/review logs are evidence and are intentionally retained.
No files in the original working directory were deleted by packaging.

## Validate the delivered evidence

Extract into a NEW directory. Python 3, Node.js and Git must be available on PATH.
The bundled release history is required by the immutable baseline comparisons.
It contains committed history only: no local Git configuration, hooks or reflogs.
From the extracted {ROOT.name} directory, run:

    python3 _archive/restore_git_history.py
    cd bfgs_lean_stage1
    python3 scripts/verify_rigorous_master_report.py
    python3 literature_audit/scripts/validate.py

The restore helper checks the inventory first and refuses an existing .git.
It restores local history without overwriting source files or contacting a server.
These checks validate recorded evidence; they do not perform fresh Lean compilation.

## Fresh builds and persistent edits

Use a separate extraction/checkout for new compiler runs, so the sealed evidence
remains intact. Follow bfgs_lean_stage1/README.md for repository-local Elan setup
under .toolchain/elan and the pinned Lean version, then scripts/bootstrap.sh.
The all-declaration runner requires this local toolchain location. The compiler
and pinned dependencies must be downloaded again; their several-GB installed
size is why they are excluded here. Bootstrap writes historical checker output
paths; do not use it in the copy whose delivered seal you want to preserve.
For the standalone fresh audit runner, see master_report/audit/README.md.

For persistent report edits, change master_report/authoring and master_report/edits
and regenerate with scripts/build_rigorous_master_report.py. The generated LaTeX
can be compiled directly, but regeneration overwrites direct edits to it.

_archive/CONTENTS.json lists every other archive member with its SHA-256 and size.
The report's own manifests and proof records are included unchanged.
'''
            add(full, 'complete', archive_prefix, 'ARCHIVE_README.md', full_readme.encode())
            tex_readme = f'''# Corrected BFGS report: standalone LaTeX package

Source commit: {commit}

The outer folder retains the original name, {ROOT.name}. All source files keep
their exact repository-relative paths. This package contains all 30 required
.tex files: the main document, bibliography, 14 chapters and 14 coverage tables.
The entry point is bfgs_lean_stage1/master_report/latex/master.tex.
The reviewed 98-page PDF remains at
bfgs_lean_stage1/output/pdf/Rigorous_BFGS_Master_Report.pdf.

From the extracted {ROOT.name} directory, compile with a TeX distribution providing the packages
declared in master.tex (including latexmk, Latin Modern, xurl and bookmark):

    cd bfgs_lean_stage1/master_report/latex
    latexmk -pdf -interaction=nonstopmode -halt-on-error master.tex

No Lean installation, Git history, external figures or BibTeX database is needed
to typeset this package. The bibliography is included directly in bibliography.tex.
Build products are excluded from this ZIP; the command above creates them locally.

These are exact generated LaTeX sources from the corrected report. You may edit
them as a standalone document. For persistent changes in the research project's
generation workflow, use its authoring inputs and edit ledger instead.

The PDF and coverage tables refer to companion Lean sources and audit records.
This small package does not include those proof artifacts or support the full
verification gate; use BFGS_complete_source_and_verification.zip for that purpose.
_archive/CONTENTS.json lists every other member with its SHA-256 and size.
'''
            add(tex, 'latex', archive_prefix, 'ARCHIVE_README.md', tex_readme.encode())
            for kind, archive, prefix, manifest_name in [
                ('complete', full, archive_prefix, '_archive/CONTENTS.json'),
                ('latex', tex, archive_prefix, '_archive/CONTENTS.json'),
            ]:
                record = {'schema_version': 1, 'source_commit': commit,
                          'scope': kind, 'root_directory': ROOT.name,
                          'source_paths': 'Exact repository-relative paths; no flattening or relocation',
                          'files': dict(payloads[kind])}
                add(archive, kind, prefix, manifest_name, (json.dumps(record, indent=2) + '\n').encode())
        assert git('rev-parse', 'HEAD').decode().strip() == commit, 'HEAD changed during packaging'

    results = []
    for kind, path, prefix in [('complete', full_path, archive_prefix),
                               ('latex', tex_path, archive_prefix)]:
        with zipfile.ZipFile(path) as archive:
            assert archive.testzip() is None
            names = archive.namelist()
            assert len(names) == len(set(names))
            assert set(names) == {prefix + name for name in payloads[kind]}
            for name, record in payloads[kind].items():
                data = archive.read(prefix + name)
                assert len(data) == record['bytes']
                assert hashlib.sha256(data).hexdigest() == record['sha256']
        results.append({'kind': kind, 'path': str(path.relative_to(ROOT)),
                        'bytes': path.stat().st_size, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                        'members': len(payloads[kind]),
                        'uncompressed_bytes': sum(r['bytes'] for r in payloads[kind].values())})
    summary = {'status': 'PASS', 'source_commit': commit,
               'utc': dt.datetime.now(dt.timezone.utc).isoformat(),
               'root_directory': ROOT.name,
               'source_paths': 'Exact repository-relative paths; no flattening or relocation',
               'tracked_files': len(tracked), 'tracked_bytes': sum(r['bytes'] for r in tracked.values()),
               'excluded_path_components': sorted(FORBIDDEN),
               'excluded_suffixes': sorted(SUFFIXES),
               'checks': ['Committed snapshot only', 'Exact original directory name and source paths in both archives',
                          'No temporary/cache paths or compiled artifacts',
                          'Self-contained release bundle with exact HEAD', 'ZIP CRC and every member SHA-256'],
               'archives': results}
    (OUT / 'ARCHIVES.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
