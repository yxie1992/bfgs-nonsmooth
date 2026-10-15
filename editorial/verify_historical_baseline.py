#!/usr/bin/env python3
"""Run the unchanged original public gate at its frozen historical release.

The old citation-only gate compares every tracked Lean path in the repository
with an earlier commit. Later article-only Lean additions therefore make that
historical gate fail at current HEAD, even when its sealed inputs are identical.
This wrapper preserves that failure, compares the frozen inputs, and runs the
entire unmodified gate in a clean detached worktree at the historical release.
It does not replace the current article/companion or supplemental Lean gates.
Git history (including the baseline) must first be restored in an archive.

Release tooling T1 (October 2026 edition): the added paths that the wrapper
accepts in the global Lean diff are recorded in ADDED_LEAN_SCOPES. Besides the
added editorial Lean files of the September supplements, they now include the
added October package bfgs_lean_article/ (status A only), which requires the main
library ../bfgs_lean_stage1 by path and changes none of its files. Relative to
the citation baseline every path in these scopes is new, so the scope test cannot
see later edits there: the September editorial Lean files are therefore required
unchanged since the 13 September release 3e8b5c6 (any added, modified, deleted or
renamed editorial/**/*.lean path fails), and the October package is bound by
editorial/verify_release_inputs.py (T3). A modified, deleted or renamed Lean path
of the main library still fails. The diff is read with -z, so a non-ASCII path is
not misread. The legacy gate, its expected failure at the current commit and every
other check are unchanged; SUMMARY.json records the allowed scopes and the diff
entries of each scope.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '00362c0249262d182866f14bac756a7c4edac95c'
SEPTEMBER_RELEASE = '3e8b5c6ff5f4ef663718c74776ecc78ca3527db4'
PROJECT_NAME = 'bfgs_lean_stage1'
GATE = 'scripts/verify_rigorous_master_report.py'
ATTRIBUTION_GATE = 'scripts/verify_report_attributions.py'
LEAN_PATHS = ['*.lean', '*lean-toolchain', '*lakefile.toml', '*lake-manifest.json']
# Added (status A) paths that the historical global-diff assertion may meet at
# the current commit, each with its recorded reason (T1, October 2026).
ADDED_LEAN_SCOPES = [
    {'scope': 'editorial/**/*.lean', 'status': 'A',
     'reason': 'Added article-only editorial Lean supplements (September 2026); compiled and audited by their own runners.'},
    {'scope': 'bfgs_lean_article/**', 'status': 'A',
     'reason': 'Added October 2026 article package (supplements compiled in place, new modules, Lean coverage modules); '
               'it requires the unchanged main library ../bfgs_lean_stage1 by path and modifies none of its files.'},
]


def added_scope(status, name):
    """The recorded scope of an allowed added Lean path, or None."""
    parts = Path(name).parts
    if status != 'A' or not parts:
        return None
    if parts[0] == 'editorial' and name.endswith('.lean'):
        return ADDED_LEAN_SCOPES[0]['scope']
    if parts[0] == 'bfgs_lean_article' and len(parts) > 1:
        return ADDED_LEAN_SCOPES[1]['scope']
    return None


def name_status(text):
    """Records of `git diff --name-status -z`: [status, path], or [status, 'old<TAB>new'] for a rename or copy."""
    fields = text.split('\0')
    if fields and fields[-1] == '':
        fields.pop()
    rows, i = [], 0
    while i < len(fields):
        status = fields[i]
        count = 2 if status[:1] in ('R', 'C') else 1
        require(status and i + count < len(fields) + 1 and len(fields[i + 1:i + 1 + count]) == count,
                'Unexpected Git diff record format')
        rows.append([status, '\t'.join(fields[i + 1:i + 1 + count])])
        i += 1 + count
    return rows


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def artifact(project, name):
    relative = Path(name)
    require(not relative.is_absolute() and '..' not in relative.parts,
            'Invalid frozen artifact path: ' + name)
    path = (project / relative).resolve()
    require(path.is_relative_to(project.resolve()) and path.is_file(),
            'Missing or escaping frozen artifact: ' + name)
    return path


def compare_frozen_artifacts(current, historical):
    """Bind the historical PASS to unchanged inputs delivered at current HEAD."""
    now = current / PROJECT_NAME
    old = historical / PROJECT_NAME
    input_name = 'master_report/audit/fresh/INPUTS.json'
    original_inputs = json.loads(artifact(old, input_name).read_text())
    require(artifact(now, input_name).read_bytes() == artifact(old, input_name).read_bytes(),
            'Delivered historical audit input register changed at current HEAD')
    checked_inputs = {}
    for name, expected in original_inputs.items():
        relative = ('master_report/audit/' + name[len('@audit/'):]
                    if name.startswith('@audit/') else name)
        require(digest(artifact(old, relative)) == expected,
                'Historical input does not match its own register: ' + name)
        require(digest(artifact(now, relative)) == expected,
                'Current HEAD changed a historical audit input: ' + name)
        checked_inputs[name] = expected

    manifest_name = 'master_report/MANIFEST.json'
    require(artifact(now, manifest_name).read_bytes() == artifact(old, manifest_name).read_bytes(),
            'Current HEAD changed the sealed original manifest')
    manifest = json.loads(artifact(old, manifest_name).read_text())
    checked_release = {}
    for name, expected in manifest['files'].items():
        require(digest(artifact(old, name)) == expected,
                'Historical sealed artifact hash mismatch: ' + name)
        require(digest(artifact(now, name)) == expected,
                'Current HEAD changed a sealed original artifact: ' + name)
        checked_release[name] = expected
    for script in [GATE, ATTRIBUTION_GATE]:
        require(artifact(now, script).read_bytes() == artifact(old, script).read_bytes(),
                'Legacy validator changed at current HEAD: ' + script)
    return {
        'status': 'PASS',
        'unchanged_historical_audit_inputs': len(checked_inputs),
        'unchanged_sealed_original_artifacts': len(checked_release),
        'audit_input_sha256': checked_inputs,
        'sealed_original_artifact_sha256': checked_release,
        'manifest_sha256': digest(artifact(old, manifest_name)),
        'unmodified_validator_sha256': {
            script: digest(artifact(old, script)) for script in [GATE, ATTRIBUTION_GATE]
        },
    }


def main():
    require(__debug__, 'Run without Python optimization; all legacy assertions must remain enabled.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-id', default=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ'))
    parser.add_argument('--node', default=os.environ.get('BFGS_NODE') or shutil.which('node'))
    parser.add_argument('--keep-worktrees', action='store_true',
                        help='Keep only this run\'s isolated worktrees for inspection; paths are logged.')
    args = parser.parse_args()
    require(re.fullmatch(r'[A-Za-z0-9_.-]+', args.run_id) is not None
            and args.run_id not in {'.', '..'}, 'Invalid run-id')
    node = shutil.which(args.node) if args.node else None
    require(node is not None, 'Node.js is required by the unchanged public gate; pass --node.')

    run = ROOT / 'editorial/historical_baseline/runs' / args.run_id
    run.mkdir(parents=True, exist_ok=False)
    work = ROOT / 'release/work' / ('historical-baseline-' + args.run_id)
    commands = []
    created = []
    attempted = []
    work_created = False
    summary = {
        'status': 'RUNNING', 'started_utc': utc(), 'baseline_commit': BASELINE,
        'scope': 'Historical original-release gate plus unchanged frozen inputs; not a current article/companion verification substitute.',
        'logs': str(run.relative_to(ROOT)), 'work_root': str(work),
        'legacy_checks_modified_or_skipped': False,
        'fresh_lean_compilation': False,
    }

    def command(argv, label, cwd=ROOT):
        start = utc()
        timer = time.monotonic()
        stdout = run / (label + '.stdout.log')
        stderr = run / (label + '.stderr.log')
        with stdout.open('wb') as out, stderr.open('wb') as err:
            result = subprocess.run(argv, cwd=cwd, stdout=out, stderr=err)
        record = {
            'id': label, 'command': argv, 'cwd': str(cwd), 'started_utc': start,
            'ended_utc': utc(), 'elapsed_seconds': time.monotonic() - timer,
            'exit_code': result.returncode,
            'stdout': str(stdout.relative_to(ROOT)), 'stderr': str(stderr.relative_to(ROOT)),
            'stdout_sha256': digest(stdout), 'stderr_sha256': digest(stderr),
        }
        commands.append(record)
        write(run / 'commands.json', commands)
        return result.returncode, stdout.read_text(), stderr.read_text()

    def git(*argv, label, cwd=ROOT):
        code, out, err = command(['git', *argv], label, cwd)
        require(code == 0, 'Git command failed (' + label + '): ' + err.strip())
        return out.strip()

    try:
        work.mkdir(parents=True, exist_ok=False)
        work_created = True
        require(Path(git('rev-parse', '--show-toplevel', label='00_repository')).resolve() == ROOT,
                'Run the wrapper from its actual repository tree')
        current_commit = git('rev-parse', 'HEAD', label='01_current_commit')
        summary['current_commit'] = current_commit
        git('cat-file', '-e', BASELINE + '^{commit}', label='02_required_baseline_history')
        git('merge-base', '--is-ancestor', BASELINE, current_commit, label='03_baseline_ancestor')
        code, _, _ = command([node, '--version'], '04_node_version')
        require(code == 0, 'Node.js version check failed')

        for name, commit in [('current_head', current_commit), ('historical_baseline', BASELINE)]:
            path = work / name
            attempted.append(path)
            git('worktree', 'add', '--detach', str(path), commit, label='05_add_' + name)
            created.append(path)
            require(git('rev-parse', 'HEAD', label='06_head_' + name, cwd=path) == commit,
                    'Wrong isolated worktree commit: ' + name)
            require(not git('status', '--porcelain', '--untracked-files=all',
                            label='07_clean_' + name, cwd=path),
                    'Isolated worktree is not clean: ' + name)

        current, historical = work / 'current_head', work / 'historical_baseline'
        frozen = compare_frozen_artifacts(current, historical)
        write(run / 'frozen_input_comparison.json', frozen)
        summary['frozen_input_comparison'] = {
            key: frozen[key] for key in ['status', 'unchanged_historical_audit_inputs',
                                         'unchanged_sealed_original_artifacts']
        }
        summary['frozen_input_comparison_sha256'] = digest(run / 'frozen_input_comparison.json')

        citation_baseline = json.loads((historical / PROJECT_NAME /
            'master_report/authoring/citation_revision/BASELINE.json').read_text())['source_commit']
        changed_text = git('diff', '--name-status', '-z', citation_baseline, '--', *LEAN_PATHS,
                           label='08_current_global_lean_diff', cwd=current)
        changed = name_status(changed_text)
        require(all(len(row) == 2 for row in changed), 'Unexpected Git diff record format')
        summary['historical_citation_baseline'] = citation_baseline
        summary['current_global_lean_diff'] = changed
        # Relative to the citation baseline every editorial supplement path is 'added', so the scope test
        # below cannot see a later edit, rename or deletion there; bind them to the 13 September release.
        git('cat-file', '-e', SEPTEMBER_RELEASE + '^{commit}', label='08b_september_release_history')
        since_september = git('diff', '--name-status', SEPTEMBER_RELEASE, current_commit, '--', 'editorial/*.lean',
                              label='08c_editorial_lean_since_september_release')
        require(not since_september, 'Editorial Lean files changed since the 13 September release: '
                + since_september[:400])
        summary['editorial_lean_unchanged_since_september_release'] = SEPTEMBER_RELEASE

        argv = [sys.executable, GATE, '--node', node]
        code, out, err = command(argv, '09_current_head_public_gate', current / PROJECT_NAME)
        summary['current_head_public_gate_exit_code'] = code
        summary['allowed_added_lean_scopes'] = ADDED_LEAN_SCOPES
        summary['current_global_lean_diff_by_scope'] = {
            scope['scope']: sum(1 for status, name in changed if added_scope(status, name) == scope['scope'])
            for scope in ADDED_LEAN_SCOPES}
        if changed:
            require(all(added_scope(status, name) is not None for status, name in changed),
                    'Current history differs beyond added editorial Lean files and the added article package; '
                    'investigate explicitly')
            require(code != 0 and 'Changed Lean proof or toolchain inputs' in err
                    and 'verify_report_attributions.py' in err,
                    'Current HEAD did not fail at the expected unchanged historical global-diff assertion')
            summary['current_head_result'] = 'EXPECTED_HISTORICAL_SCOPE_FAILURE_RECORDED'
        else:
            require(code == 0 and json.loads(out)['status'] == 'PASS',
                    'Current HEAD has no new Lean paths but its original gate failed')
            summary['current_head_result'] = 'PASS_NO_ADDED_LEAN_PATHS'

        code, out, _ = command(argv, '10_historical_baseline_public_gate', historical / PROJECT_NAME)
        require(code == 0, 'The unchanged historical public gate failed at its recorded baseline')
        gate_result = json.loads(out)
        require(gate_result['status'] == 'PASS' and gate_result['before_seal'] is False,
                'Historical gate did not validate the complete sealed release')
        write(run / 'historical_public_gate.json', gate_result)
        summary['historical_public_gate'] = gate_result
        for name in ['current_head', 'historical_baseline']:
            require(not git('status', '--porcelain', '--untracked-files=all',
                            label='11_after_clean_' + name, cwd=work / name),
                    'Legacy read-only checks changed the isolated tracked/untracked source state')
        summary['status'] = 'PASS'
    except Exception as error:
        summary.update(status='FAIL', failure=str(error))
    finally:
        cleanup = []
        registered = set(created)
        removed = set()
        if not args.keep_worktrees:
            # A failed checkout may already have registered its attempted path.
            # Inspect registration before cleaning only paths owned by this run.
            if attempted:
                try:
                    code, listing, err = command(['git', 'worktree', 'list', '--porcelain', '-z'],
                                                  '12_cleanup_registration')
                    require(code == 0, 'Could not inspect worktree registration: ' + err.strip())
                    registered.update(Path(record[len('worktree '):]) for record in listing.split('\0')
                                      if record.startswith('worktree '))
                except Exception as error:
                    summary.update(status='FAIL', cleanup_registration_failure=str(error))
            for path in reversed(attempted):
                if path not in registered:
                    continue
                try:
                    code, _, err = command(['git', 'worktree', 'remove', str(path)],
                                           '13_remove_' + path.name)
                    cleanup.append({'path': str(path), 'exit_code': code, 'stderr': err.strip()})
                    if code != 0:
                        summary.update(status='FAIL', cleanup_failure='Could not remove own worktree: ' + str(path))
                    else:
                        removed.add(path)
                except Exception as error:
                    cleanup.append({'path': str(path), 'exception': str(error)})
                    summary.update(status='FAIL', cleanup_failure=str(error))
            if work_created:
                try:
                    if not any(work.iterdir()):
                        work.rmdir()
                    else:
                        summary.update(status='FAIL', cleanup_failure='Owned work directory is not empty: ' + str(work))
                except Exception as error:
                    summary.update(status='FAIL', cleanup_failure=str(error))
        summary['cleanup'] = cleanup
        summary['attempted_worktree_paths'] = [str(path) for path in attempted]
        summary['worktrees_retained'] = [str(path) for path in attempted
                                         if path.exists() or (path in registered and path not in removed)]
        summary['ended_utc'] = utc()
        summary['commands_sha256'] = digest(run / 'commands.json') if commands else None
        summary['wrapper_sha256'] = digest(Path(__file__).resolve())
        write(run / 'SUMMARY.json', summary)
    print(json.dumps(summary, indent=2))
    return 0 if summary['status'] == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
