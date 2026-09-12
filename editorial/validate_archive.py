#!/usr/bin/env python3
"""Replay a source archive in a fresh extraction, retaining every validation run."""
from pathlib import Path, PurePosixPath
from concurrent.futures import ThreadPoolExecutor
import argparse
import datetime
import hashlib
import json
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import threading
import time
import zipfile

ROOT = Path(__file__).resolve().parents[1]
PDFS = {'paper': 'BFGS_Journal_Article.pdf', 'companion': 'BFGS_Complete_Companion.pdf'}
FREEZE_STATUSES = {'AWAITING_ARCHIVE_VALIDATION', 'SOURCE_REVIEWED_AWAITING_ARCHIVE_VALIDATION'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def safe_relative(name):
    p = PurePosixPath(name)
    assert name and '\\' not in name and not p.is_absolute() and '..' not in p.parts and p.as_posix() == name, name
    return p


def main():
    if not __debug__:
        raise RuntimeError('Run without Python optimization so integrity assertions remain enabled.')
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--run-id', help='New run under release/validation/runs; never overwrite an existing run.')
    group.add_argument('--output-dir', help='New repository-local directory for this validation run.')
    parser.add_argument('--manifest', default='release/SOURCE_MANIFEST.json', help='External package-creation receipt.')
    parser.add_argument('--lean-cache-root', default=str(ROOT / 'bfgs_lean_stage1'),
                        help='Pinned host project supplying existing .lake and .toolchain caches; its frozen sources must match.')
    args = parser.parse_args()
    run_id = args.run_id or datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S_%fZ')
    if not re.fullmatch(r'[A-Za-z0-9_-]+', run_id):
        raise RuntimeError('run-id must use letters, digits, underscores or hyphens')
    out = (ROOT / args.output_dir).resolve() if args.output_dir else ROOT / 'release/validation/runs' / run_id
    if not out.is_relative_to(ROOT) or out == ROOT:
        raise RuntimeError('Validation output must be a new directory inside this repository.')
    out.mkdir(parents=True, exist_ok=False)
    work = ROOT / 'release/work'
    commands = []
    lock = threading.Lock()
    temp_path = None
    summary = {
        'status': 'RUNNING', 'run_id': run_id, 'output_directory': str(out.relative_to(ROOT)),
        'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'scope': 'Fresh source extraction, document regeneration, all-page pixel comparison, fresh supplemental Lean compilation/full structural audits using disclosed pinned host library caches, and historical/current evidence validation. No empty-cache or fresh original-library build is claimed.',
        'commands': commands,
    }

    def run(argv, name, cwd):
        start = time.monotonic()
        stdout = out / (name + '.stdout.log')
        stderr = out / (name + '.stderr.log')
        assert not stdout.exists() and not stderr.exists(), 'Duplicate command label: ' + name
        with stdout.open('wb') as output, stderr.open('wb') as error:
            result = subprocess.run(argv, cwd=cwd, stdout=output, stderr=error)
        record = {'command': argv, 'cwd': str(cwd), 'exit_code': result.returncode,
                  'seconds': time.monotonic() - start,
                  'stdout': str(stdout.relative_to(ROOT)), 'stdout_sha256': sha(stdout),
                  'stderr': str(stderr.relative_to(ROOT)), 'stderr_sha256': sha(stderr)}
        with lock:
            commands.append(record)
            save(out / 'commands.json', commands)
        if result.returncode:
            raise RuntimeError(name + ' failed; see ' + str(stderr))
        return stdout.read_text()

    def attach_pinned_library_cache(tree):
        host = Path(args.lean_cache_root).resolve()
        project = tree / 'bfgs_lean_stage1'
        register = project / 'master_report/audit/fresh/INPUTS.json'
        frozen = json.loads(register.read_text())
        assert sha(register) == sha(host / 'master_report/audit/fresh/INPUTS.json')
        for name, expected in frozen.items():
            relative = 'master_report/audit/' + name[len('@audit/'):] if name.startswith('@audit/') else name
            assert sha(project / relative) == expected == sha(host / relative), 'Host/extraction frozen-input mismatch: ' + name
        for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
            assert sha(project / name) == sha(host / name), 'Host/extraction pinned-dependency mismatch: ' + name
        packages = json.loads((project / 'lake-manifest.json').read_text())['packages']
        package_records = []
        for i, package in enumerate(packages):
            assert package['type'] == 'git', 'Unreviewed dependency package type'
            path = host / '.lake/packages' / package['name']
            actual = run(['git', 'rev-parse', 'HEAD'], f'07_dependency_{i:02d}_revision', path).strip()
            assert actual == package['rev'], 'Cached dependency revision mismatch: ' + package['name']
            dirty = run(['git', 'status', '--porcelain', '--untracked-files=no'], f'07_dependency_{i:02d}_clean', path)
            assert not dirty.strip(), 'Cached dependency has tracked changes: ' + package['name']
            package_records.append({'name': package['name'], 'path': str(path.resolve()),
                                    'revision': actual, 'tracked_worktree_clean': True})
        links = []
        for name in ['.lake', '.toolchain']:
            source = host / name
            destination = project / name
            assert source.is_dir() and not destination.exists() and not destination.is_symlink()
            destination.symlink_to(source.resolve(), target_is_directory=True)
            links.append({'extraction_relative_path': str(destination.relative_to(tree)),
                          'host_cache': str(source.resolve()), 'kind': 'reused library/toolchain cache'})
        assert (project / '.lake/build/lib/lean/BfgsVerification.olean').is_file(), 'Pinned compiled original library is required.'
        summary['lean_cache_reuse'] = {'scope': 'Only .lake and .toolchain are linked after source/history validation. .cache is not linked. Supplemental own modules are compiled in fresh extraction-local output directories.',
                                      'frozen_original_inputs_matched': len(frozen), 'links': links,
                                      'dependency_checkouts': package_records, 'fresh_original_library_build': False}

    try:
        work.mkdir(parents=True, exist_ok=True)
        manifest_path = (ROOT / args.manifest).resolve()
        assert manifest_path.is_relative_to(ROOT)
        manifest = json.loads(manifest_path.read_text())
        assert manifest['schema_version'] == 2, 'This validator expects the explicit version-2 release-snapshot metadata.'
        archive = ROOT / safe_relative(manifest['archive'])
        summary.update(source_commit=manifest['source_commit'], archive_sha256=sha(archive),
                       manifest=str(manifest_path.relative_to(ROOT)), manifest_sha256=sha(manifest_path))
        assert sha(archive) == manifest['sha256'] and archive.stat().st_size == manifest['bytes']
        with tempfile.TemporaryDirectory(prefix='archive-replay-', dir=work) as tmp:
            temp = Path(tmp)
            temp_path = temp
            with zipfile.ZipFile(archive) as z:
                names = z.namelist()
                assert len(names) == len(set(names)) == manifest['members'] and z.testzip() is None
                root_name = manifest['root_directory']
                assert safe_relative(root_name).parts == (root_name,)
                prefix = root_name + '/'
                modes = {}
                for info in z.infolist():
                    name = info.filename
                    safe_relative(name)
                    assert name.startswith(prefix)
                    mode = info.external_attr >> 16
                    assert info.create_system == 3 and stat.S_ISREG(mode), 'Nonregular archive member: ' + name
                    modes[name] = stat.S_IMODE(mode)
                contents = json.loads(z.read(prefix + '_archive/CONTENTS.json'))
                assert contents['schema_version'] == 2 and contents['root_directory'] == root_name
                assert contents['source_commit'] == manifest['source_commit']
                assert contents['source_files'] == manifest['source_files']
                assert set(names) == {prefix + name for name in contents['files']} | {prefix + '_archive/CONTENTS.json'}
                for name, data in contents['files'].items():
                    safe_relative(name)
                    raw = z.read(prefix + name)
                    assert len(raw) == data['bytes'] and hashlib.sha256(raw).hexdigest() == data['sha256'], name
                    assert modes[prefix + name] == data['mode'], 'Mode mismatch: ' + name
                snapshot = json.loads(z.read(prefix + contents['release_snapshot']))
                assert snapshot['source_commit'] == manifest['source_commit'] and snapshot['root_directory'] == root_name
                assert snapshot['status'] == 'PACKAGED_SOURCE_SNAPSHOT_AWAITING_EXTRACTION_VALIDATION'
                assert snapshot['extraction_validation']['status'] == 'NOT_YET_RUN'
                assert snapshot['pdfs'] == manifest['pdfs']
                z.extractall(temp)
                for name, mode in modes.items():
                    (temp / name).chmod(mode)
            tree = temp / root_name
            assert not (tree / '.git').exists()
            assert not (tree / 'paper/build').exists() and not (tree / 'companion/build').exists()
            assert not (tree / 'bfgs_lean_stage1/.lake').exists() and not (tree / 'bfgs_lean_stage1/.toolchain').exists()
            freeze = json.loads((tree / 'release/RELEASE.json').read_text())
            assert freeze['status'] in FREEZE_STATUSES
            assert freeze.get('source_archive') is None and freeze.get('extraction_validation') is None
            assert sha(tree / 'release/RELEASE.json') == snapshot['source_freeze_metadata']['sha256']
            assert all(all(freeze['pdfs'][name][key] == value for key, value in record.items()) for name, record in snapshot['pdfs'].items())
            for receipt in snapshot['committed_prior_package_receipts']:
                source = tree / safe_relative(receipt['path'])
                old = json.loads(source.read_text())
                assert sha(source) == receipt['file_sha256']
                assert old.get('source_commit') == receipt['source_commit'] != manifest['source_commit']
                assert old.get('sha256') == receipt['archive_sha256']
            summary['fresh_extraction'] = True
            summary['all_archive_member_hashes_verified'] = len(contents['files'])
            summary['archive_metadata_scope_verified'] = snapshot
            run([sys.executable, '_archive/restore_git_history.py'], '01_restore_history', tree)
            head = run(['git', 'rev-parse', 'HEAD'], '01_restored_head', tree).strip()
            assert head == manifest['source_commit']
            assert not run(['git', 'status', '--porcelain', '--untracked-files=no'], '01_restored_tracked_clean', tree).strip()
            tracked = set(run(['git', 'ls-tree', '-r', '--name-only', '-z', 'HEAD'], '01_tracked_inventory', tree).strip('\0').split('\0'))
            extras = {'_archive/history.bundle', '_archive/restore_git_history.py', '_archive/RELEASE_SNAPSHOT.json', 'AUTHOR_REVIEW_README.md'}
            assert len(tracked) == manifest['source_files'] and set(contents['files']) == tracked | extras
            expected_receipts = {name for name in tracked if name == 'release/SOURCE_MANIFEST.json' or (name.startswith('release/history/') and name.endswith('/SOURCE_MANIFEST.json'))}
            assert expected_receipts == {r['path'] for r in snapshot['committed_prior_package_receipts']}
            summary['restored_head'] = head
            run(['bash', 'editorial/build.sh'], '02_build_documents', tree)
            checks = json.loads((tree / 'editorial/logs/document_checks.json').read_text())
            assert checks['status'] == 'PASS'
            for name in ['paper_build.log', 'companion_build.log', 'figure_build.log', 'document_checks.json']:
                shutil.copy2(tree / 'editorial/logs' / name, out / name)
            reviews = json.loads((tree / 'editorial/reviews/render_manifest.json').read_text())
            assert len(reviews['documents']) == 2 and {r['document'] for r in reviews['documents']} == set(PDFS)

            def compare_document(review):
                name = review['document']
                pdf = tree / name / 'build/master.pdf'
                delivered = tree / 'release' / PDFS[name]
                check = next(c for c in checks['documents'] if c['document'] == name)
                assert check['pages'] == review['page_count'] and not check['errors'] and not check['overfull_warnings']
                assert sha(delivered) == review['pdf_sha256'] == snapshot['pdfs'][PDFS[name]]['sha256']
                old_text = run(['pdftotext', '-layout', str(delivered), '-'], '03_text_delivered_' + name, tree)
                new_text = run(['pdftotext', '-layout', str(pdf), '-'], '03_text_rebuilt_' + name, tree)
                assert old_text == new_text, name + ' extracted PDF text differs'
                render = temp / ('render-' + name)
                render.mkdir()
                run(['pdftoppm', '-r', '100', '-png', str(pdf), str(render / 'page')], '03_render_' + name, tree)
                images = sorted(render.glob('page-*.png'))
                assert len(images) == review['page_count']
                assert [sha(p) for p in images] == [p['sha256'] for p in review['pages']], name + ' page pixels differ'
                return {'document': name, 'pages': check['pages'], 'rebuilt_pdf_sha256': sha(pdf),
                        'delivered_pdf_sha256': sha(delivered), 'byte_identical': sha(pdf) == sha(delivered),
                        'all_pages_pixel_identical_to_visually_reviewed_pdf': True,
                        'paginated_text_identical': True, 'references_resolved': True, 'overfull_boxes': 0}

            with ThreadPoolExecutor(max_workers=2) as pool:
                summary['documents'] = list(pool.map(compare_document, reviews['documents']))
            run([sys.executable, 'editorial/generate_companion.py', '--check'], '04_companion_preservation', tree)
            attach_pinned_library_cache(tree)
            supplement_records = []
            register = json.loads((tree / 'editorial/narrative_rebuild/FORMAL_SUPPLEMENTS.json').read_text())
            assert len(register['supplements']) == 2 and {r['name'] for r in register['supplements']} == {'positive_formal', 'negative_formal'}
            root_contracts = json.loads((tree / 'editorial/root_contract_review.json').read_text())
            geometry = root_contracts['supplemental_structural_audit']
            assert geometry['name'] == 'geometry_formal'
            assert geometry['summary'] == 'editorial/satisfaction_review/formal/runs/geometry_structural_01/SUMMARY.json'
            assert geometry['declarations'] == 'editorial/satisfaction_review/formal/runs/geometry_structural_01/declarations.json'
            branch = root_contracts['supplemental_branch_regularity_audit']
            assert branch['name'] == 'branch_regularity_formal'
            assert branch['summary'] == 'editorial/satisfaction_review/branch_formal/runs/branch_regularity_01/SUMMARY.json'
            assert branch['declarations'] == 'editorial/satisfaction_review/branch_formal/runs/branch_regularity_01/declarations.json'
            replay_plans = [(next(r for r in register['supplements'] if r['name'] == name),
                             tree / 'editorial/narrative_rebuild' / name)
                            for name in ['positive_formal', 'negative_formal']]
            replay_plans.append((geometry, tree / 'editorial/satisfaction_review/formal'))
            replay_plans.append((branch, tree / 'editorial/satisfaction_review/branch_formal'))
            for record, base in replay_plans:
                name = record['name']
                assert sha(tree / record['summary']) == record['summary_sha256']
                assert sha(tree / record['declarations']) == record['declarations_sha256']
                replay_id = 'archive_validation_' + run_id
                replay = base / 'runs' / replay_id
                try:
                    run([sys.executable, str(base / 'verify.py'), '--run-id', replay_id], '08_fresh_' + name, tree)
                finally:
                    if replay.is_dir():
                        shutil.copytree(replay, out / name, ignore=shutil.ignore_patterns('build'))
                fresh = json.loads((replay / 'SUMMARY.json').read_text())
                old = json.loads((tree / record['summary']).read_text())
                assert fresh['status'] == 'PASS' and not fresh['unchecked_missing_unsafe_partial']
                assert fresh['kernel_root_type_and_value_agreement'] is True
                assert set(fresh['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
                assert fresh['module_owned_declarations'] == old['module_owned_declarations']
                assert fresh['transitive_checked_declarations'] == old['transitive_checked_declarations']
                actual = json.loads((replay / 'declarations.json').read_text())
                expected = json.loads((tree / record['declarations']).read_text())
                fields = ['name', 'kind', 'signature', 'axioms', 'unsafe', 'partial']
                assert [{key: row[key] for key in fields} for row in actual] == [{key: row[key] for key in fields} for row in expected]
                assert all(row['ordinary_collector_agrees'] for row in actual)
                if name == 'geometry_formal':
                    assert fresh['module_owned_declarations'] == 14
                    assert set(fresh['compiled_olean_sha256']) == {'ArticleGeometry', 'ConvexBalance'}
                    for module, digest in fresh['compiled_olean_sha256'].items():
                        assert sha(replay / 'build' / (module + '.olean')) == digest
                    geometry_fields = fields + ['module']
                    def geometry_types(rows):
                        assert len({row['name'] for row in rows}) == len(rows)
                        return sorted(({key: row[key] for key in geometry_fields} for row in rows), key=lambda row: row['name'])
                    assert geometry_types(actual) == geometry_types(expected) == geometry_types(root_contracts['supplemental_declarations'])
                if name == 'branch_regularity_formal':
                    assert fresh['module_owned_declarations'] == 3
                    assert {row['module'] for row in actual} == {'ArticleBranchRegularity'}
                    assert {row['name'] for row in actual} == {
                        'ArticleBranchRegularity.branch_not_twice_differentiable_zero',
                        'ArticleBranchRegularity.whitened_branch_not_twice_differentiable_zero',
                        'ArticleBranchRegularity.smoothLocalFailure_with_branch_obstruction'}
                    assert sha(replay / 'build/ArticleBranchRegularity.olean') == fresh['compiled_olean_sha256']
                supplement_records.append({'name': name, 'status': 'PASS', 'run_id': replay_id,
                                           'module_owned_declarations': fresh['module_owned_declarations'],
                                           'transitive_checked_declarations': fresh['transitive_checked_declarations'],
                                           'same_exact_types_as_recorded_source_audit': True,
                                           'summary': str((out / name / 'SUMMARY.json').relative_to(ROOT)),
                                           'summary_sha256': sha(out / name / 'SUMMARY.json')})
            summary['fresh_supplemental_audits'] = supplement_records
            run([sys.executable, 'editorial/verify_release_inputs.py'], '09_release_inputs', tree)
            historical_id = 'archive_validation_' + run_id
            historical_run = tree / 'editorial/historical_baseline/runs' / historical_id
            try:
                run([sys.executable, 'editorial/verify_historical_baseline.py', '--run-id', historical_id], '10_historical_gate', tree)
            finally:
                if historical_run.is_dir():
                    shutil.copytree(historical_run, out / 'historical_baseline')
            summary['historical_gate'] = json.loads((out / 'historical_baseline/SUMMARY.json').read_text())['status']
            assert summary['historical_gate'] == 'PASS'
            summary['status'] = 'PASS'
        summary['temporary_extraction_removed'] = True
    except Exception as error:
        summary.update(status='FAIL', failure=str(error))
    finally:
        if temp_path is not None:
            summary['temporary_extraction_removed'] = not temp_path.exists()
            if temp_path.exists():
                summary.update(status='FAIL', retained_temporary_extraction=str(temp_path))
        summary['ended_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        summary['commands_sha256'] = sha(out / 'commands.json') if commands else None
        save(out / 'SUMMARY.json', summary)
    print(json.dumps(summary, indent=2))
    return 0 if summary['status'] == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
