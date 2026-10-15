#!/usr/bin/env python3
"""Replay the unchanged 13 September correspondence check at its own release commit.

Release tooling T2 (October 2026 edition). The 13 September bounded refresh,
editorial/scientific_exposition_20260913/refresh_correspondence.py --check, rejects
every statement change by design. Since the October corrections change named
statements and displays, it fails at the current commit. This wrapper keeps it
as a historical check instead of dropping it:

1. the script, its retained inputs (prior_mapping/, the N-review records and its
   receipt mapping_refresh.json) and the helper it imports are unchanged at the
   current commit, in git and in the working tree;
2. the unchanged script is run with --check in a clean detached worktree at the
   release commit 3e8b5c6 and must pass there, with its recorded counts;
3. it is also run at the current commit, and its failure there is recorded as
   expected when it is one of the script's own assertions (a pass there is
   recorded as PASS_AT_CURRENT_COMMIT).

Inputs are compared as git sees them (tracked files, and untracked files that
are not ignored), so an ignored .DS_Store is not an input. An existing run
directory is reported as a failure; it is never reused or overwritten.

The current role of the check passes to the October correspondence revision,
editorial/release_20261015/refresh_correspondence.py --check. Nothing is
written outside this run's directory and its own temporary worktree. Git history
(including the release commit) must first be restored in an archive.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
RELEASE_COMMIT = '3e8b5c6ff5f4ef663718c74776ecc78ca3527db4'
REVISION = 'editorial/scientific_exposition_20260913'
SCRIPT = REVISION + '/refresh_correspondence.py'
UNCHANGED = [
    SCRIPT,
    REVISION + '/prior_mapping',
    REVISION + '/N1_review.json',
    REVISION + '/N2_review.json',
    REVISION + '/N3_N4_review.json',
    REVISION + '/N5_review.json',
    REVISION + '/mapping_refresh.json',
    'editorial/active_tex_sources.py',
]
EXPECTED_PASS = 'PASS: 31 named contracts; 52 existing labeled displays; exact algorithm; immutable evidence; current bytes match'


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def tree_files(listing, root):
    """SHA-256 of each file of a NUL-separated `git ls-files` listing (None for a tracked file that is missing)."""
    files = {}
    for name in sorted(n for n in listing.split('\0') if n):
        path = root / name
        files[name] = digest(path) if path.is_file() else None
    return files


def main():
    require(__debug__, 'Run without Python optimization; all assertions must remain enabled.')
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--run-id', default=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ'))
    parser.add_argument('--keep-worktree', action='store_true',
                        help='Keep only this run\'s isolated worktree for inspection; its path is logged.')
    args = parser.parse_args()
    require(re.fullmatch(r'[A-Za-z0-9_.-]+', args.run_id) is not None
            and args.run_id not in {'.', '..'}, 'Invalid run-id')

    run = ROOT / 'editorial/historical_correspondence/runs' / args.run_id
    try:
        run.mkdir(parents=True, exist_ok=False)
    except FileExistsError:
        print(json.dumps({'status': 'FAIL', 'failure': 'Run directory already exists (never reused): '
                          + str(run.relative_to(ROOT))}, indent=2))
        return 1
    work = ROOT / 'release/work' / ('historical-correspondence-' + args.run_id)
    worktree = work / 'release_commit'
    commands = []
    attempted = False
    work_created = False
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    summary = {
        'status': 'RUNNING', 'started_utc': utc(), 'release_commit': RELEASE_COMMIT,
        'scope': 'Historical 13 September correspondence check, replayed unchanged at its release commit; its '
                 'current role belongs to editorial/release_20261015/refresh_correspondence.py --check.',
        'script': SCRIPT, 'logs': str(run.relative_to(ROOT)), 'work_root': str(work),
        'historical_check_modified_or_skipped': False,
    }

    def command(argv, label, cwd=ROOT):
        start = utc()
        timer = time.monotonic()
        stdout = run / (label + '.stdout.log')
        stderr = run / (label + '.stderr.log')
        with stdout.open('wb') as out, stderr.open('wb') as err:
            result = subprocess.run(argv, cwd=cwd, stdout=out, stderr=err, env=environment)
        commands.append({
            'id': label, 'command': argv, 'cwd': str(cwd), 'started_utc': start,
            'ended_utc': utc(), 'elapsed_seconds': time.monotonic() - timer,
            'exit_code': result.returncode,
            'stdout': str(stdout.relative_to(ROOT)), 'stderr': str(stderr.relative_to(ROOT)),
            'stdout_sha256': digest(stdout), 'stderr_sha256': digest(stderr),
        })
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
        git('cat-file', '-e', RELEASE_COMMIT + '^{commit}', label='02_required_release_commit')
        git('merge-base', '--is-ancestor', RELEASE_COMMIT, current_commit, label='03_release_commit_ancestor')
        code, _, _ = command(['git', 'diff', '--quiet', RELEASE_COMMIT, current_commit, '--', *UNCHANGED],
                             '04_unchanged_in_history')
        require(code == 0, 'The historical correspondence script or its inputs changed after the release commit')

        attempted = True
        git('worktree', 'add', '--detach', str(worktree), RELEASE_COMMIT, label='05_add_release_commit')
        require(git('rev-parse', 'HEAD', label='06_head_release_commit', cwd=worktree) == RELEASE_COMMIT,
                'Wrong isolated worktree commit')
        require(not git('status', '--porcelain', '--untracked-files=all', label='07_clean_release_commit',
                        cwd=worktree), 'Isolated worktree is not clean')
        listing = ['ls-files', '-z', '--cached', '--others', '--exclude-standard', '--', *UNCHANGED]
        current_files = tree_files(git(*listing, label='07b_inputs_current'), ROOT)
        release_files = tree_files(git(*listing, label='07c_inputs_release_commit', cwd=worktree), worktree)
        require(None not in release_files.values() and all(
                    any(name == relative or name.startswith(relative + '/') for name in release_files)
                    for relative in UNCHANGED), 'Historical correspondence inputs missing at the release commit')
        require(current_files == release_files,
                'The working tree changes the historical correspondence script or its inputs')
        write(run / 'unchanged_inputs.json', release_files)
        summary['unchanged_inputs'] = {'paths': UNCHANGED, 'files': len(release_files),
                                       'sha256': digest(run / 'unchanged_inputs.json'),
                                       'equal_in_history_and_working_tree': True}

        argv = [sys.executable, SCRIPT, '--check']
        code, out, err = command(argv, '08_release_commit_check', worktree)
        require(code == 0 and out.strip() == EXPECTED_PASS,
                'The unchanged 13 September correspondence check failed at its release commit')
        summary['release_commit_result'] = out.strip()
        require(not git('status', '--porcelain', '--untracked-files=all', label='09_after_clean_release_commit',
                        cwd=worktree), 'The historical check changed its isolated worktree')

        code, out, err = command(argv, '10_current_commit_check', ROOT)
        summary['current_commit_exit_code'] = code
        if code == 0:
            summary['current_commit_result'] = 'PASS_AT_CURRENT_COMMIT'
            summary['current_commit_output'] = out.strip()
        else:
            lines = [line for line in err.strip().splitlines() if line.strip()]
            require(lines and lines[-1].startswith('AssertionError'),
                    'The historical check failed at the current commit, but not at one of its own assertions')
            summary['current_commit_result'] = 'EXPECTED_HISTORICAL_SCOPE_FAILURE_RECORDED'
            summary['current_commit_failure'] = lines[-1]
        summary['status'] = 'PASS'
    except Exception as error:
        summary.update(status='FAIL', failure=str(error))
    finally:
        cleanup = []
        if attempted and not args.keep_worktree:
            try:
                code, listing, err = command(['git', 'worktree', 'list', '--porcelain', '-z'], '11_cleanup_registration')
                registered = {Path(record[len('worktree '):]) for record in listing.split('\0')
                              if record.startswith('worktree ')} if code == 0 else set()
                if code != 0:
                    summary.update(status='FAIL', cleanup_registration_failure=err.strip())
                if worktree in registered or worktree.resolve() in registered:
                    code, _, err = command(['git', 'worktree', 'remove', str(worktree)], '12_remove_release_commit')
                    cleanup.append({'path': str(worktree), 'exit_code': code, 'stderr': err.strip()})
                    if code != 0:
                        summary.update(status='FAIL', cleanup_failure='Could not remove own worktree: ' + str(worktree))
            except Exception as error:
                cleanup.append({'path': str(worktree), 'exception': str(error)})
                summary.update(status='FAIL', cleanup_failure=str(error))
        if work_created and not args.keep_worktree:
            try:
                if not any(work.iterdir()):
                    work.rmdir()
                else:
                    summary.update(status='FAIL', cleanup_failure='Owned work directory is not empty: ' + str(work))
            except Exception as error:
                summary.update(status='FAIL', cleanup_failure=str(error))
        summary['cleanup'] = cleanup
        summary['worktree_retained'] = worktree.exists()
        summary['ended_utc'] = utc()
        summary['commands_sha256'] = digest(run / 'commands.json') if commands else None
        summary['wrapper_sha256'] = digest(Path(__file__).resolve())
        write(run / 'SUMMARY.json', summary)
    print(json.dumps(summary, indent=2))
    return 0 if summary['status'] == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
