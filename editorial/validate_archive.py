#!/usr/bin/env python3
"""Rebuild both documents and replay evidence checks in a fresh source extraction."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import datetime
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import time
import zipfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'release/validation'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    summary_path = OUT / 'SUMMARY.json'
    if summary_path.exists():
        raise RuntimeError('Preserve the previous validation run before rerunning.')
    manifest = json.loads((ROOT / 'release/SOURCE_MANIFEST.json').read_text())
    archive = ROOT / manifest['archive']
    commands = []
    summary = {
        'status': 'RUNNING', 'source_commit': manifest['source_commit'],
        'archive_sha256': sha(archive),
        'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'scope': 'Fresh extraction, complete document regeneration, all-page pixel comparison and historical/current evidence validation. No empty-cache Lean compilation is claimed.',
        'commands': commands,
    }

    def run(argv, name, cwd):
        start = time.monotonic()
        stdout = OUT / (name + '.stdout.log')
        stderr = OUT / (name + '.stderr.log')
        with stdout.open('wb') as out, stderr.open('wb') as err:
            result = subprocess.run(argv, cwd=cwd, stdout=out, stderr=err)
        commands.append({
            'command': argv, 'cwd': str(cwd), 'exit_code': result.returncode,
            'seconds': time.monotonic() - start,
            'stdout': str(stdout.relative_to(ROOT)), 'stdout_sha256': sha(stdout),
            'stderr': str(stderr.relative_to(ROOT)), 'stderr_sha256': sha(stderr),
        })
        if result.returncode:
            raise RuntimeError(name + ' failed; see ' + str(stderr))

    try:
        assert sha(archive) == manifest['sha256']
        with tempfile.TemporaryDirectory(prefix='archive-replay-', dir=ROOT / 'release/work') as tmp:
            temp = Path(tmp)
            with zipfile.ZipFile(archive) as z:
                names = z.namelist()
                assert len(names) == len(set(names)) and z.testzip() is None
                prefix = ROOT.name + '/'
                for name in names:
                    p = Path(name)
                    assert name.startswith(prefix) and not p.is_absolute() and '..' not in p.parts
                contents = json.loads(z.read(prefix + '_archive/CONTENTS.json'))
                assert contents['source_commit'] == manifest['source_commit']
                assert set(names) == {prefix + p for p in contents['files']} | {prefix + '_archive/CONTENTS.json'}
                for name, data in contents['files'].items():
                    raw = z.read(prefix + name)
                    assert len(raw) == data['bytes'] and hashlib.sha256(raw).hexdigest() == data['sha256'], name
                z.extractall(temp)
            tree = temp / ROOT.name
            assert not (tree / '.git').exists()
            assert not (tree / 'paper/build').exists() and not (tree / 'companion/build').exists()
            summary['fresh_extraction'] = True
            summary['all_archive_member_hashes_verified'] = len(contents['files'])
            run([sys.executable, '_archive/restore_git_history.py'], '01_restore_history', tree)
            head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=tree, text=True).strip()
            assert head == manifest['source_commit']
            summary['restored_head'] = head
            run(['bash', 'editorial/build.sh'], '02_build_documents', tree)
            checks = json.loads((tree / 'editorial/logs/document_checks.json').read_text())
            assert checks['status'] == 'PASS'
            for name in ['paper_build.log', 'companion_build.log', 'figure_build.log', 'document_checks.json']:
                shutil.copy2(tree / 'editorial/logs' / name, OUT / name)
            reviews = json.loads((ROOT / 'editorial/reviews/render_manifest.json').read_text())
            documents = []

            def compare_document(review):
                name = review['document']
                pdf = tree / name / 'build/master.pdf'
                delivered = tree / 'release' / ('BFGS_Journal_Article.pdf' if name == 'paper' else 'BFGS_Complete_Companion.pdf')
                check = next(c for c in checks['documents'] if c['document'] == name)
                assert check['pages'] == review['page_count'] and not check['errors'] and not check['overfull_warnings']
                assert sha(delivered) == review['pdf_sha256']
                old_text = subprocess.check_output(['pdftotext', '-layout', str(delivered), '-'])
                new_text = subprocess.check_output(['pdftotext', '-layout', str(pdf), '-'])
                assert old_text == new_text, name + ' extracted PDF text differs'
                render = temp / ('render-' + name)
                render.mkdir()
                run(['pdftoppm', '-r', '100', '-png', str(pdf), str(render / 'page')], '03_render_' + name, tree)
                images = sorted(render.glob('page-*.png'))
                assert len(images) == review['page_count']
                assert [sha(p) for p in images] == [p['sha256'] for p in review['pages']], name + ' page pixels differ'
                return {
                    'document': name, 'pages': check['pages'], 'rebuilt_pdf_sha256': sha(pdf),
                    'delivered_pdf_sha256': sha(delivered), 'byte_identical': sha(pdf) == sha(delivered),
                    'all_pages_pixel_identical_to_visually_reviewed_pdf': True,
                    'paginated_text_identical': True, 'references_resolved': True, 'overfull_boxes': 0,
                }

            with ThreadPoolExecutor(max_workers=2) as pool:
                documents = list(pool.map(compare_document, reviews['documents']))
            summary['documents'] = documents
            run([sys.executable, 'editorial/generate_companion.py', '--check'], '04_companion_preservation', tree)
            run([sys.executable, 'editorial/verify_release_inputs.py'], '05_release_inputs', tree)
            run([sys.executable, 'editorial/verify_historical_baseline.py', '--run-id', 'archive_validation'], '06_historical_gate', tree)
            shutil.copytree(tree / 'editorial/historical_baseline/runs/archive_validation', OUT / 'historical_baseline')
            summary['historical_gate'] = json.loads((OUT / 'historical_baseline/SUMMARY.json').read_text())['status']
            summary['status'] = 'PASS'
        summary['temporary_extraction_removed'] = True
    except Exception as error:
        summary.update(status='FAIL', failure=str(error))
    summary['ended_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    summary_path.write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    return 0 if summary['status'] == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
