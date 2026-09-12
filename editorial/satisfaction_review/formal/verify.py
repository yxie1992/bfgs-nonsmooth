#!/usr/bin/env python3
"""Freshly compile unchanged article geometry proofs with the full structural auditor."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, subprocess, sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PROJECT = ROOT / 'bfgs_lean_stage1'
SOURCE = ROOT / 'editorial/article_formal'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def save(path, obj):
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n')

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--run-id', default=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
args = parser.parse_args()
if not args.run_id or any(c not in 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-' for c in args.run_id):
    raise SystemExit('Use only letters, numbers, underscore or hyphen in run-id')
run = HERE / 'runs' / args.run_id
run.mkdir(parents=True, exist_ok=False)
build = run / 'build'
build.mkdir()
env = os.environ.copy()
elan = PROJECT / '.toolchain/elan'
if (elan / 'bin/lake').is_file():
    env['ELAN_HOME'] = str(elan)
    env['PATH'] = str(elan / 'bin') + os.pathsep + env['PATH']
env['XDG_CACHE_HOME'] = str(PROJECT / '.cache')
env['MATHLIB_CACHE_DIR'] = str(PROJECT / '.cache/mathlib')
commands = []
summary = {'status': 'RUNNING', 'run_directory': str(run.relative_to(ROOT)),
           'scope': 'Fresh unchanged article geometry proof compilation and stricter type/value/structural dependency audit; pinned original library objects are reused.',
           'fresh_original_library_build': False}

def invoke(command, tag, runenv=env):
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    out = run / (tag + '.stdout.log')
    err = run / (tag + '.stderr.log')
    with out.open('wb') as stdout, err.open('wb') as stderr:
        result = subprocess.run(command, cwd=PROJECT, env=runenv, stdout=stdout, stderr=stderr)
    commands.append({'command': command, 'cwd': str(PROJECT), 'started_utc': start,
                     'exit_code': result.returncode, 'stdout': str(out.relative_to(ROOT)),
                     'stderr': str(err.relative_to(ROOT)), 'stdout_sha256': sha(out),
                     'stderr_sha256': sha(err)})
    save(run / 'commands.json', commands)
    if result.returncode:
        raise RuntimeError(f'{tag} exited {result.returncode}; inspect the retained logs')
    return out.read_text()

try:
    baseline = json.loads((ROOT / 'editorial/BASELINE.json').read_text())
    for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'master_report/DECLARATION_INDEX.json']:
        p = PROJECT / name
        if sha(p) != baseline['files'][str(p.relative_to(ROOT))]:
            raise RuntimeError('Pinned input differs from original baseline: ' + name)
    register = PROJECT / 'master_report/audit/fresh/INPUTS.json'
    frozen = json.loads(register.read_text())
    input_paths = {}
    for name, expected in frozen.items():
        p = PROJECT / ('master_report/audit/' + name[len('@audit/'):] if name.startswith('@audit/') else name)
        if sha(p) != expected:
            raise RuntimeError('Historical audit input differs: ' + name)
        input_paths[str(p.relative_to(ROOT))] = p
    for name in ['DependencyAudit.lean', 'verify.py']:
        p = HERE / name
        input_paths[str(p.relative_to(ROOT))] = p
    for p in [register, PROJECT / 'master_report/DECLARATION_INDEX.json', ROOT / 'editorial/BASELINE.json', SOURCE / 'ArticleGeometry.lean', SOURCE / 'ConvexBalance.lean']:
        input_paths[str(p.relative_to(ROOT))] = p
    inputs = {name: sha(p) for name, p in sorted(input_paths.items())}
    save(run / 'INPUTS.json', inputs)
    version = invoke(['lake', 'env', 'lean', '--version'], '00_version').strip()
    expected = (PROJECT / 'lean-toolchain').read_text().strip().rsplit(':v', 1)[-1]
    if not version.startswith('Lean (version ' + expected + ','):
        raise RuntimeError('Actual compiler does not match pinned Lean version: ' + version)
    commit = invoke(['git', 'rev-parse', 'HEAD'], '01_commit').strip()
    search = invoke(['lake', 'env', 'printenv', 'LEAN_PATH'], '02_search_path').strip()
    for number, name in enumerate(['ArticleGeometry', 'ConvexBalance'], 3):
        invoke(['lake', 'env', 'lean', '-R', str(SOURCE), '-o', str(build / (name + '.olean')),
                str(SOURCE / (name + '.lean'))], f'{number:02d}_{name}')
    audit_env = env.copy()
    audit_env['LEAN_PATH'] = str(build) + os.pathsep + search
    audit_env['BFGS_GEOMETRY_STRUCTURAL_AUDIT_OUT'] = str(run)
    invoke(['lean', '-R', str(HERE), str(HERE / 'DependencyAudit.lean')], '05_dependency_audit', audit_env)
    result = json.loads((run / 'audit_summary.json').read_text())
    if result['status'] != 'PASS':
        raise RuntimeError('Dependency audit did not pass')
    if {name: sha(p) for name, p in sorted(input_paths.items())} != inputs:
        raise RuntimeError('Compiler/audit inputs changed during this run')
    summary.update(result)
    summary.update({'lean_version': version, 'source_commit': commit,
                    'frozen_original_audit_inputs_unchanged': len(frozen),
                    'input_hashes_sha256': sha(run / 'INPUTS.json'),
                    'source_sha256': {name: value for name, value in inputs.items()
                                      if name.startswith(str(HERE.relative_to(ROOT))) or name.startswith(str(SOURCE.relative_to(ROOT)))},
                    'declarations_sha256': sha(run / 'declarations.json'),
                    'dependency_graph_sha256': sha(run / 'dependency_graph.json'),
                    'compiled_olean_sha256': {name: sha(build / (name + '.olean')) for name in ['ArticleGeometry', 'ConvexBalance']}})
except Exception as error:
    summary.update(status='FAIL', failure=str(error))
finally:
    summary['ended_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    summary['commands_sha256'] = sha(run / 'commands.json') if commands else None
    save(run / 'SUMMARY.json', summary)
print(json.dumps(summary, indent=2, ensure_ascii=False))
sys.exit(0 if summary['status'] == 'PASS' else 1)
