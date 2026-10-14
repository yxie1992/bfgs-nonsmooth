#!/usr/bin/env python3
"""Replay every project module through the Lean kernel with lean4checker.

lean4checker (https://github.com/leanprover/lean4checker) loads the imports of a
module and replays every declaration stored in that module's .olean through the
Lean kernel. It therefore detects declarations that entered the environment
without a kernel check (for example through `debug.skipKernelTC` or other
environment manipulation), which `#print axioms` cannot see.

This script runs it on every module of the main library, the article
supplements and this package (the import closure of this package's default
targets, restricted to project sources), one module per process. Modules that
contain only `import` lines declare nothing and are listed instead of replayed
(lean4checker cannot target them alone, since it also selects every module
whose name extends theirs). Mathlib and Lean core are not replayed.

Usage (from bfgs_lean_article/, after `lake build`):
    python3 scripts/kernel_replay.py --checker-repo PATH [--self-test] [--jobs 8] [--report KERNEL_REPLAY.json]

PATH is a checkout of lean4checker at the tag matching `lean-toolchain`, built
with `lake build`. With --self-test the checker's own `test.sh` runs first; it
must detect the deliberately forged declarations in its test modules.
"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse, datetime, hashlib, json, re, subprocess, sys, time, tomllib

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
ROOT = PACKAGE.parent
PACKAGES = [PACKAGE, ROOT / 'bfgs_lean_stage1']
COMMENT = re.compile(r'/-.*?-/|--[^\n]*', re.S)


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def command_output(command, cwd):
    return subprocess.run(command, cwd=cwd, capture_output=True, text=True).stdout.strip()


def source_dirs():
    dirs = []
    for package in PACKAGES:
        config = tomllib.loads((package / 'lakefile.toml').read_text())
        for lib in config.get('lean_lib', []):
            dirs.append((package / lib.get('srcDir', '.')).resolve())
    return list(dict.fromkeys(dirs))


def resolve(module, dirs):
    relative = Path(*module.split('.')).with_suffix('.lean')
    return next((d / relative for d in dirs if (d / relative).is_file()), None)


def code_lines(path):
    return [line for line in COMMENT.sub('', path.read_text()).splitlines() if line.strip()]


def project_modules():
    """Import closure of the default targets, restricted to project sources."""
    dirs = source_dirs()
    pending = list(tomllib.loads((PACKAGE / 'lakefile.toml').read_text())['defaultTargets'])
    modules = {}
    while pending:
        module = pending.pop()
        if module in modules:
            continue
        path = resolve(module, dirs)
        if path is None:  # Mathlib or Lean core
            continue
        modules[module] = path
        pending += [m for line in code_lines(path) if line.startswith('import ') for m in line.split()[1:]]
    return modules


def replay(checker, module):
    started = time.monotonic()
    result = subprocess.run(['lake', 'env', str(checker), module], cwd=PACKAGE, capture_output=True, text=True)
    output = (result.stdout + result.stderr).strip()
    return module, result.returncode, round(time.monotonic() - started, 1), output[-2000:]


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--checker-repo', type=Path, required=True)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--jobs', type=int, default=8)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    started = now()
    source_commit = command_output(['git', 'rev-parse', 'HEAD'], ROOT)
    source_tree_clean = command_output(['git', 'status', '--porcelain'], ROOT) == ''
    repo = args.checker_repo.resolve()
    checker = repo / '.lake' / 'build' / 'bin' / 'lean4checker'

    self_test = None
    if args.self_test:
        test = subprocess.run(['bash', 'test.sh'], cwd=repo, capture_output=True, text=True)
        self_test = 'PASS' if test.returncode == 0 and 'All commands produced the expected errors.' in test.stdout else 'FAIL'
        if self_test == 'FAIL':
            print(test.stdout[-3000:], test.stderr[-3000:], file=sys.stderr)

    modules = project_modules()
    names = sorted(modules)
    prefixes = {m for m in names if any(o.startswith(m + '.') for o in names)}
    imports_only = sorted(m for m in prefixes if all(l.startswith('import ') for l in code_lines(modules[m])))
    targets = [m for m in names if m not in imports_only]
    with ThreadPoolExecutor(max(1, args.jobs)) as pool:
        results = list(pool.map(lambda m: replay(checker, m), targets))
    failures = [{'module': m, 'exit_code': c, 'output': o} for m, c, _, o in results if c != 0]

    roots = {}
    for m in names:
        roots[m.split('.')[0]] = roots.get(m.split('.')[0], 0) + 1
    seconds = {m: s for m, _, s, _ in results}
    passed = not failures and self_test != 'FAIL'
    report = {
        'status': 'PASS' if passed else 'FAIL',
        'started_utc': started,
        'finished_utc': now(),
        'lean_version': command_output(['lake', 'env', 'lean', '--version'], PACKAGE),
        'source_commit': source_commit,
        'source_tree_clean': source_tree_clean,
        'command': 'python3 scripts/kernel_replay.py --checker-repo PATH' + (' --self-test' if args.self_test else ''),
        'checker': {
            'tool': 'lean4checker',
            'tag': command_output(['git', 'describe', '--tags', '--exact-match'], repo),
            'commit': command_output(['git', 'rev-parse', 'HEAD'], repo),
            'binary_sha256': hashlib.sha256(checker.read_bytes()).hexdigest(),
            'self_test': self_test,
        },
        'scope': 'every declaration of every project module (main library, article supplements, this package) '
                 'replayed through the Lean kernel on top of its imports; Mathlib and Lean core not replayed',
        'modules_in_closure': len(names),
        'modules_by_root': roots,
        'modules_replayed': len(targets),
        'imports_only_modules_not_replayed': imports_only,
        'failures': failures,
        'slowest_modules_seconds': dict(sorted(seconds.items(), key=lambda t: -t[1])[:10]),
    }
    if args.report:
        args.report.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps(report, indent=2, ensure_ascii=False))
    return 0 if passed else 1


if __name__ == '__main__':
    sys.exit(main())
