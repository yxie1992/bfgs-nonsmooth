#!/usr/bin/env python3
"""Package a committed, reviewed source freeze with unambiguous release metadata."""
from pathlib import Path, PurePosixPath
import datetime
import hashlib
import json
import subprocess
import tarfile
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'release'
PDFS = {'paper': 'BFGS_Journal_Article.pdf', 'companion': 'BFGS_Complete_Companion.pdf'}
FORBIDDEN = {'.git', '.lake', '.toolchain', '.cache', 'tmp', 'scratch', '__pycache__', '.DS_Store', 'work'}
SUFFIXES = {'.olean', '.ilean', '.pyc', '.aux', '.fls', '.fdb_latexmk', '.toc'}
FREEZE_STATUSES = {'AWAITING_ARCHIVE_VALIDATION', 'SOURCE_REVIEWED_AWAITING_ARCHIVE_VALIDATION'}


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe_name(name):
    p = PurePosixPath(name)
    assert name and '\\' not in name and not p.is_absolute() and '..' not in p.parts
    assert p.as_posix() == name and not FORBIDDEN.intersection(p.parts) and p.suffix not in SUFFIXES, name
    return p


def reviewed_documents(source_names):
    """Require the source freeze itself to contain the currently reviewed PDFs."""
    release = json.loads((OUT / 'RELEASE.json').read_text())
    assert release['status'] in FREEZE_STATUSES, 'Release metadata must identify an awaiting-validation source freeze.'
    assert release.get('source_archive') is None, 'A new source freeze must not claim an already completed source archive.'
    assert release.get('extraction_validation') is None, 'A new source freeze must not claim an already completed extraction validation.'
    reviews = json.loads((ROOT / 'editorial/reviews/render_manifest.json').read_text())['documents']
    checks = json.loads((ROOT / 'editorial/logs/document_checks.json').read_text())
    assert checks['status'] == 'PASS'
    assert len(reviews) == 2 and {r['document'] for r in reviews} == set(PDFS)
    assert len(checks['documents']) == 2 and {r['document'] for r in checks['documents']} == set(PDFS)
    assert set(release['pdfs']) == set(PDFS.values())
    records = {}
    for document, filename in PDFS.items():
        name = 'release/' + filename
        assert name in source_names, 'Commit the current release PDF before packaging: ' + name
        delivered = (ROOT / name).read_bytes()
        built = (ROOT / document / 'build/master.pdf').read_bytes()
        review = next(r for r in reviews if r['document'] == document)
        check = next(r for r in checks['documents'] if r['document'] == document)
        record = {'bytes': len(delivered), 'sha256': sha(delivered), 'pages': review['page_count']}
        assert delivered == built, 'Tracked release PDF differs from current build: ' + document
        assert record['sha256'] == review['pdf_sha256'] == check['sha256'], document
        assert check['pages'] == record['pages'] and not check['errors'] and not check['overfull_warnings'], document
        assert all(release['pdfs'][filename][key] == value for key, value in record.items()), 'Stale release metadata: ' + filename
        records[filename] = record
    return release, records


def prior_receipts(source_names):
    """Archive hashes in a committed tree necessarily predate this new package."""
    receipts = []
    for name in sorted(source_names):
        if name == 'release/SOURCE_MANIFEST.json' or (name.startswith('release/history/') and name.endswith('/SOURCE_MANIFEST.json')):
            data = (ROOT / name).read_bytes()
            old = json.loads(data)
            receipts.append({'path': name, 'file_sha256': sha(data), 'source_commit': old.get('source_commit'),
                             'archive_sha256': old.get('sha256'),
                             'role': 'Preserved committed prior-package receipt; does not describe this archive.'})
    return receipts


def main():
    if not __debug__:
        raise RuntimeError('Run without Python optimization so integrity assertions remain enabled.')
    commit = git('rev-parse', 'HEAD').decode().strip()
    assert not git('status', '--porcelain', '--untracked-files=no'), 'Commit tracked source changes before packaging.'
    source_names = set(git('ls-tree', '-r', '--name-only', '-z', commit).decode().strip('\0').split('\0'))
    assert source_names and '' not in source_names
    for name in source_names:
        safe_name(name)
        assert not name.startswith('_archive/') and name != 'AUTHOR_REVIEW_README.md', 'Reserved archive-only path is tracked: ' + name
    release, pdfs = reviewed_documents(source_names)
    receipts = prior_receipts(source_names)
    prefix = ROOT.name + '/'
    path = OUT / 'BFGS_paper_companion_sources.zip'
    OUT.mkdir(exist_ok=True)
    work = OUT / 'work'
    work.mkdir(parents=True, exist_ok=True)
    timestamp = int(git('show', '-s', '--format=%ct', commit).decode().strip())
    date = datetime.datetime.fromtimestamp(timestamp, datetime.timezone.utc).timetuple()[:6]
    assert 1980 <= date[0] <= 2107
    files = {}
    snapshot = {
        'schema_version': 1, 'status': 'PACKAGED_SOURCE_SNAPSHOT_AWAITING_EXTRACTION_VALIDATION',
        'source_commit': commit, 'root_directory': ROOT.name,
        'pdfs': pdfs,
        'source_freeze_metadata': {'path': 'release/RELEASE.json', 'status': release['status'],
                                   'sha256': sha((OUT / 'RELEASE.json').read_bytes())},
        'committed_prior_package_receipts': receipts,
        'metadata_authority': 'This archive-only snapshot identifies the current package. Committed SOURCE_MANIFEST receipts describe earlier packages. The external new SOURCE_MANIFEST records this ZIP hash after creation.',
        'extraction_validation': {'status': 'NOT_YET_RUN', 'scope': 'Later versioned validation evidence is external to this immutable source snapshot.'},
    }
    with tempfile.TemporaryDirectory(prefix='pack-', dir=work) as tmp:
        temp = Path(tmp)
        bundle = temp / 'history.bundle'
        subprocess.run(['git', 'bundle', 'create', str(bundle), 'HEAD'], cwd=ROOT, check=True)
        staged = temp / 'sources.zip'
        with zipfile.ZipFile(staged, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9, allowZip64=True) as z:
            def add(name, data, mode=0o644):
                safe_name(name)
                assert name not in files, name
                info = zipfile.ZipInfo(prefix + name, date)
                info.create_system = 3
                info.external_attr = (0o100000 | mode) << 16
                info.compress_type = zipfile.ZIP_DEFLATED
                z.writestr(info, data, compresslevel=9)
                files[name] = {'bytes': len(data), 'sha256': sha(data), 'mode': mode}

            process = subprocess.Popen(['git', 'archive', '--format=tar', commit], cwd=ROOT, stdout=subprocess.PIPE)
            names = set()
            try:
                with tarfile.open(fileobj=process.stdout, mode='r|') as tar:
                    for member in tar:
                        if member.isdir():
                            continue
                        assert member.isfile(), member.name
                        add(member.name, tar.extractfile(member).read(), member.mode & 0o777)
                        names.add(member.name)
            finally:
                process.stdout.close()
                code = process.wait()
            assert code == 0 and names == source_names
            for filename, record in pdfs.items():
                assert files['release/' + filename]['sha256'] == record['sha256']
            add('_archive/history.bundle', bundle.read_bytes())
            add('_archive/restore_git_history.py', (ROOT / 'packaging/restore_git_history.py').read_bytes(), 0o755)
            add('_archive/RELEASE_SNAPSHOT.json', (json.dumps(snapshot, indent=2) + '\n').encode())
            readme = f'''# BFGS paper and complete companion — author-review source snapshot

Current source commit: {commit}

The outer folder is {ROOT.name}; every committed repository file retains its
exact relative path. The current delivered PDFs are release/BFGS_Journal_Article.pdf
and release/BFGS_Complete_Companion.pdf. Their current hashes and the source freeze
identity are in _archive/RELEASE_SNAPSHOT.json.

METADATA SCOPE: _archive/RELEASE_SNAPSHOT.json identifies this package. Any
committed release/SOURCE_MANIFEST.json or release/history/*/SOURCE_MANIFEST.json
is preserved historical evidence for an EARLIER package, explicitly classified
in that snapshot; it is not the receipt for this ZIP. This ZIP's own hash is
recorded in the external SOURCE_MANIFEST.json after packaging. Existing committed
release/validation evidence also predates this new extraction validation. The
source freeze does not claim a validation run that has not yet happened.

The archive includes the exact committed source tree, original corrected research,
Lean sources and pinned dependency records, complete correspondence, actual audits,
review records and the Git bundle required by immutable historical checks. It
excludes untracked user changes, dependency caches, compiled objects and build
debris. Actual compiler and review logs are retained as evidence.

In a fresh extraction restore history BEFORE building or editing, because the
helper checks the original member hashes and refuses an existing .git:

    python3 _archive/restore_git_history.py
    bash editorial/build.sh
    python3 editorial/verify_historical_baseline.py
    python3 editorial/verify_release_inputs.py

Entry points are paper/master.tex and companion/master.tex. The unchanged
historical gate is replayed at its exact original release commit; the wrapper
preserves the later-HEAD citation-only failure and verifies the frozen inputs.
Current article/companion checks and supplemental Lean audits are separate.

Fresh Lean compilation requires the pinned toolchain and dependencies omitted
as reproducible caches. Follow bfgs_lean_stage1/README.md and its bootstrap
instructions. Once those are available, reproduce the current new supplements:

    python3 editorial/narrative_rebuild/positive_formal/verify.py
    python3 editorial/narrative_rebuild/negative_formal/verify.py

Their own modules are freshly compiled. Retained original-library audit logs
state what was actually built; no new empty-cache library build is implied.
_archive/CONTENTS.json records the bytes, permissions and hashes of every other
archive member. The delivered text is for author review; reserved human actions
remain in editorial/AI_AND_AUTHOR_ACTIONS.md.
'''
            add('AUTHOR_REVIEW_README.md', readme.encode())
            contents = {'schema_version': 2, 'source_commit': commit, 'root_directory': ROOT.name,
                        'source_paths': 'Exact repository-relative paths, preserved without flattening',
                        'release_snapshot': '_archive/RELEASE_SNAPSHOT.json',
                        'source_files': len(source_names), 'files': dict(files)}
            add('_archive/CONTENTS.json', (json.dumps(contents, indent=2) + '\n').encode())
        with zipfile.ZipFile(staged) as z:
            assert z.testzip() is None and len(z.namelist()) == len(set(z.namelist()))
            assert set(z.namelist()) == {prefix + name for name in files}
            for name, record in files.items():
                info = z.getinfo(prefix + name)
                assert sha(z.read(info)) == record['sha256'], name
                assert (info.external_attr >> 16) & 0o777 == record['mode'], name
        assert git('rev-parse', 'HEAD').decode().strip() == commit
        assert not git('status', '--porcelain', '--untracked-files=no'), 'Tracked source changed during packaging.'
        if path.exists() and sha(path.read_bytes()) != sha(staged.read_bytes()):
            old = sha(path.read_bytes())
            assert any(sha(p.read_bytes()) == old for p in (OUT / 'history').rglob('*.zip')), 'Preserve the previous ZIP under release/history before replacing it.'
        staged.replace(path)
    summary = {'schema_version': 2, 'status': 'PASS', 'scope': 'Package creation and member integrity; extraction validation is a later recorded step.',
               'source_commit': commit, 'root_directory': ROOT.name, 'archive': str(path.relative_to(ROOT)),
               'bytes': path.stat().st_size, 'sha256': sha(path.read_bytes()), 'members': len(files),
               'source_files': len(source_names), 'original_directory_structure_preserved': True,
               'excluded': 'Dependency caches, raw .git, compiled objects, untracked changes and temporary build files',
               'pdfs': pdfs, 'archive_release_snapshot': '_archive/RELEASE_SNAPSHOT.json',
               'committed_prior_package_receipts': receipts}
    temp_manifest = OUT / 'work/SOURCE_MANIFEST.pending.json'
    temp_manifest.write_text(json.dumps(summary, indent=2) + '\n')
    temp_manifest.replace(OUT / 'SOURCE_MANIFEST.json')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
