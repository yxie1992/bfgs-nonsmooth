#!/usr/bin/env python3
"""Bind reused Lean caches to a logged pinned Lake build; verify without rebuilding.

This records trusted incremental-build provenance, not a clean source rebuild or
independent re-typechecking of imported .olean files. All recorded paths are
repository-relative so --root can target a fresh extraction whose .lake and
.toolchain directories are explicit links to the checked host cache.
"""
from pathlib import Path, PurePosixPath
import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import time

DEFAULT_ROOT = Path(__file__).resolve().parents[2]
PROJECT_REL = 'bfgs_lean_stage1'
SCRIPT_REL = 'editorial/satisfaction_review/cache_binding.py'
RUNS_REL = 'editorial/satisfaction_review/cache_binding/runs'
SCHEMA = 2
SCOPE = ('Exact reused-object/source/Lake-trace byte binding around an ordinary pinned '
         'lake build BfgsVerification plus independent read-only recomputation of '
         'every cached .olean binary Lake hash and comparison with every existing '
         '.olean.hash. The earlier --rehash attempt failed on upstream tracked '
         'ProofWidgets JS metadata and is not claimed successful. All .olean files on the recorded '
         'Lake search path are sealed, a disclosed superset of actual imports. '
         'Trusted prior cache, compiler, Lake and execution environment remain '
         'assumptions; no clean original-library or Mathlib rebuild is claimed.')
PRIOR_RUN = RUNS_REL + '/cache_binding_01'
HASH_CHECKER = '''import Lake
open Lake System Lean

def main (args : List String) : IO UInt32 := do
  let [input] := args | throw <| IO.userError "expected one input list"
  let root := (← IO.currentDir).parent.getD "."
  let names := (← IO.FS.readFile input).splitOn "\\n" |>.filter (· != "")
  let mut rows : Array Json := #[]
  let mut mismatches := 0
  for name in names do
    let path := root / name
    let actual ← computeBinFileHash path
    let hashFile := FilePath.mk (path.toString ++ ".hash")
    let present ← hashFile.pathExists
    let cached ← if present then Hash.load? hashFile else pure none
    if present && cached != some actual then
      mismatches := mismatches + 1
    rows := rows.push <| Json.mkObj [
      ("path", toJson name), ("actual_lake_binary_hash", toJson actual.toString),
      ("hash_sidecar_present", toJson present),
      ("recorded_lake_binary_hash", toJson (cached.map toString))]
  IO.println <| (Json.mkObj [("objects", Json.arr rows),
    ("mismatch_count", toJson mismatches)]).compress
  return if mismatches == 0 then 0 else 1
'''


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def sha(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(chunk)
    return value.hexdigest()


def save(path, obj):
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n')


def relative(name):
    require(isinstance(name, str) and name, 'Empty/non-string repository path')
    value = PurePosixPath(name)
    require(not value.is_absolute() and '..' not in value.parts and
            '\\' not in name and value.as_posix() == name,
            'Unsafe repository-relative path: ' + name)
    return Path(*value.parts)


def file_record(path):
    require(path.is_file(), 'Missing file: ' + str(path))
    return {'sha256': sha(path), 'bytes': path.stat().st_size}


def command_environment(project):
    env = os.environ.copy()
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    env['GIT_OPTIONAL_LOCKS'] = '0'
    elan = project / '.toolchain/elan'
    require((elan / 'bin/lake').is_file(), 'Pinned local elan/lake is required')
    env.update(ELAN_HOME=str(elan),
               PATH=str(elan / 'bin') + os.pathsep + env.get('PATH', ''),
               XDG_CACHE_HOME=str(project / '.cache'),
               MATHLIB_CACHE_DIR=str(project / '.cache/mathlib'))
    return env


def frozen_inputs(root):
    project = root / PROJECT_REL
    baseline_path = root / 'editorial/BASELINE.json'
    baseline = json.loads(baseline_path.read_text())
    register = project / 'master_report/audit/fresh/INPUTS.json'
    frozen = json.loads(register.read_text())
    require(isinstance(frozen, dict) and frozen, 'Empty frozen source register')
    paths = {SCRIPT_REL, 'editorial/BASELINE.json',
             PROJECT_REL + '/master_report/audit/fresh/INPUTS.json',
             PROJECT_REL + '/master_report/DECLARATION_INDEX.json'}
    for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                 'master_report/DECLARATION_INDEX.json']:
        rel = PROJECT_REL + '/' + name
        require(sha(root / rel) == baseline['files'][rel],
                'Pinned baseline input differs: ' + rel)
        paths.add(rel)
    for name, expected in frozen.items():
        rel = ('master_report/audit/' + name[len('@audit/'):]
               if name.startswith('@audit/') else name)
        rel = PROJECT_REL + '/' + str(relative(rel))
        require(sha(root / rel) == expected, 'Frozen source input differs: ' + name)
        paths.add(rel)
    records = {name: file_record(root / name) for name in sorted(paths)}
    return frozen, records


def logical_path(root, raw, cwd):
    """Map resolved cache paths back through the extraction's explicit links."""
    path = Path(raw)
    path = Path(os.path.abspath(path if path.is_absolute() else cwd / path))
    if path.is_relative_to(root):
        return path.relative_to(root).as_posix()
    resolved = path.resolve()
    for part in ['.toolchain', '.lake']:
        anchor = root / PROJECT_REL / part
        if resolved.is_relative_to(anchor.resolve()):
            return (Path(PROJECT_REL) / part / resolved.relative_to(anchor.resolve())).as_posix()
    raise RuntimeError('Search/compiler path is outside the pinned project caches: ' + str(path))


def expected_project_objects(frozen):
    sources = [name for name in frozen
               if name == 'BfgsVerification.lean' or
               (name.startswith('BfgsVerification/') and name.endswith('.lean'))]
    require(sources, 'Frozen register has no original project Lean sources')
    return {PROJECT_REL + '/.lake/build/lib/lean/' + str(Path(name).with_suffix('.olean'))
            for name in sources}


def project_trace_state(root, frozen):
    prefix = root / PROJECT_REL / '.lake/build/lib/lean'
    actual = {p.relative_to(root).as_posix() for p in prefix.rglob('*.olean')}
    require(actual == expected_project_objects(frozen),
            'Project object inventory differs from frozen original sources: ' +
            json.dumps({'missing': sorted(expected_project_objects(frozen) - actual),
                        'extra': sorted(actual - expected_project_objects(frozen))}))
    state = {}
    for name in sorted(actual):
        obj = root / name
        trace = obj.with_suffix('.trace')
        require(trace.is_file(), 'Missing project trace; explicit rebuild/review required: ' + str(trace))
        value = json.loads(trace.read_text())
        require(isinstance(value.get('depHash'), str) and value['depHash'].isdigit()
                and isinstance(value.get('log'), list) and value['log'],
                'Invalid project Lake trace: ' + str(trace))
        state[trace.relative_to(root).as_posix()] = file_record(trace)
    return state


def package_states(root, invoke):
    project = root / PROJECT_REL
    packages = json.loads((project / 'lake-manifest.json').read_text())['packages']
    result = []
    for index, package in enumerate(packages):
        require(package['type'] == 'git', 'Unreviewed dependency package type')
        folder = project / '.lake/packages' / relative(package['name'])
        rev = invoke(['git', 'rev-parse', 'HEAD'], f'dependency_{index:02}_revision', folder).strip()
        dirty = invoke(['git', 'status', '--porcelain', '--untracked-files=all'],
                       f'dependency_{index:02}_clean', folder).strip()
        require(rev == package['rev'] and not dirty,
                'Wrong or dirty pinned dependency: ' + package['name'])
        result.append({'name': package['name'], 'revision': rev,
                       'tracked_and_nonignored_untracked_clean': True})
    return result


def source_candidate(root, obj_name, directory):
    obj = Path(obj_name)
    module = obj.relative_to(Path(directory)).with_suffix('.lean')
    marker = '/.lake/build/lib/lean'
    if directory.endswith(marker):
        base = directory[:-len(marker)]
        return (Path(base) / module).as_posix()
    if directory.endswith('/lib/lean') and '/.toolchain/' in directory:
        base = Path(directory[:-len('/lib/lean')]) / 'src/lean'
        if module.parts[0] == 'Lake' or module.as_posix() in ['Lake.lean', 'LakeMain.lean']:
            base = base / 'lake'
        return (base / module).as_posix()
    raise RuntimeError('Unreviewed Lean search directory: ' + directory)


def cache_inventory(root, directories):
    objects, files = {}, {}
    for directory in directories:
        prefix = root / relative(directory)
        if not prefix.exists():
            # Lake may include unused, never-built packages in LEAN_PATH.
            # Their absence is explicitly sealed by search_directory_state.
            continue
        require(prefix.is_dir(), 'Non-directory Lean search path: ' + directory)
        for path in sorted(prefix.rglob('*.olean')):
            name = path.relative_to(root).as_posix()
            require(name not in objects, 'Overlapping Lean search directories: ' + name)
            source = source_candidate(root, name, directory)
            candidates = {'source': source,
                          'trace': path.with_suffix('.trace').relative_to(root).as_posix(),
                          'lake_output_hash': name + '.hash'}
            pair = {}
            for kind, candidate in candidates.items():
                present = (root / candidate).is_file()
                pair[kind] = {'path': candidate, 'present': present}
                if present:
                    files[candidate] = file_record(root / candidate)
            is_project = directory == PROJECT_REL + '/.lake/build/lib/lean'
            if is_project:
                require(all(item['present'] for item in pair.values()),
                        'Original project object lacks source/trace/output hash: ' + name)
            files[name] = file_record(path)
            objects[name] = {'search_directory': directory, 'paired': pair,
                             'original_project': is_project}
    require(objects, 'No cached .olean files found')
    return objects, dict(sorted(files.items()))


def search_directory_state(root, directories):
    result = {name: {'present': (root / relative(name)).is_dir()} for name in directories}
    require(result[PROJECT_REL + '/.lake/build/lib/lean']['present'], 'Missing original project object directory')
    core = [name for name in directories if '/.toolchain/' in name]
    require(len(core) == 1 and result[core[0]]['present'], 'Missing built-in standard-library object directory')
    return result


def check_output_hash_result(root, output, objects):
    data = json.loads(output)
    require(data['mismatch_count'] == 0, 'A cached .olean hash sidecar is stale')
    rows = data['objects']
    require([row['path'] for row in rows] == sorted(objects), 'Incomplete/reordered output hash check')
    for row in rows:
        pair = objects[row['path']]['paired']['lake_output_hash']
        require(row['hash_sidecar_present'] is pair['present'], 'Hash-sidecar presence differs')
        actual = row['actual_lake_binary_hash']
        require(isinstance(actual, str) and actual.isdigit() and int(actual) < 2**64,
                'Invalid computed Lake binary hash')
        if pair['present']:
            require((root / pair['path']).read_text() == actual and
                    row['recorded_lake_binary_hash'] == actual, 'Stale cached output hash: ' + row['path'])
        else:
            require(row['recorded_lake_binary_hash'] is None, 'Unexpected cached hash')
    return data


def check_receipts(root, manifest):
    """Bind receipt semantics as well as bytes; old absolute cwd is metadata only."""
    run = relative(manifest['run_directory'])
    require(run.parent.as_posix() == RUNS_REL, 'Unexpected binding run location')
    origin = Path(manifest['execution_root'])
    require(origin.is_absolute(), 'Missing historical execution root')
    project = origin / PROJECT_REL
    lake = str(project / '.toolchain/elan/bin/lake')
    expected = []
    def dependency_commands(phase):
        for index, package in enumerate(manifest['dependencies']):
            cwd = project / '.lake/packages' / relative(package['name'])
            expected.extend([
                (phase + f'_dependency_{index:02}_revision', ['git', 'rev-parse', 'HEAD'], str(cwd), package['revision']),
                (phase + f'_dependency_{index:02}_clean', ['git', 'status', '--porcelain', '--untracked-files=all'], str(cwd), '')])
    dependency_commands('before')
    expected.extend([
        ('before_lean_version', [lake, 'env', 'lean', '--version'], str(project), manifest['lean_version']),
        ('before_lake_version', [lake, '--version'], str(project), manifest['lake_version']),
        ('before_lean_executable', [lake, 'env', 'which', 'lean'], str(project), str(origin / manifest['lean_executable'])),
        ('before_search_path', [lake, 'env', 'printenv', 'LEAN_PATH'], str(project), None),
        ('before_validate_object_hashes', [lake, 'env', 'lean', '--run', str(origin / run / 'ObjectHashCheck.lean'),
                                           str(origin / run / 'object_paths.txt')], str(project), None),
        ('build_original_library', [lake, 'build', 'BfgsVerification'], str(project), None)])
    dependency_commands('after')
    expected.append(('after_validate_object_hashes', [lake, 'env', 'lean', '--run', str(origin / run / 'ObjectHashCheck.lean'),
                                                     str(origin / run / 'object_paths.txt')], str(project), None))
    command_path = run / 'commands.json'
    commands = json.loads((root / command_path).read_text())
    require(len(commands) == len(expected), 'Unexpected number of binding commands')
    evidence_names = {command_path.as_posix(), (run / 'project_traces_before.json').as_posix(),
                      (run / 'project_traces_after.json').as_posix(),
                      (run / 'ObjectHashCheck.lean').as_posix(), (run / 'object_paths.txt').as_posix()}
    require((root / run / 'ObjectHashCheck.lean').read_text() == HASH_CHECKER,
            'Output hash checker source differs from reviewed implementation')
    require((root / run / 'object_paths.txt').read_text() == ''.join(name + '\n' for name in sorted(manifest['objects'])),
            'Object hash input list differs from sealed object inventory')
    for command, (label, argv, cwd, stdout_value) in zip(commands, expected):
        require(command['command'] == argv and command['cwd'] == cwd and command['exit_code'] == 0,
                'Wrong/failed binding command: ' + label)
        for stream in ['stdout', 'stderr']:
            path = (run / (label + '.' + stream + '.log')).as_posix()
            require(command[stream] == path and sha(root / path) == command[stream + '_sha256'],
                    'Wrong command log binding: ' + label + '/' + stream)
            evidence_names.add(path)
        output = (root / command['stdout']).read_text().strip()
        if stdout_value is not None:
            require(output == stdout_value, 'Command output disagrees with manifest: ' + label)
        if label == 'before_search_path':
            # Absolute historical paths are normalized against the recorded root;
            # they are never followed on an extracted tree.
            directories = []
            for raw in output.split(os.pathsep):
                if raw:
                    path = Path(os.path.abspath(Path(raw) if Path(raw).is_absolute() else project / raw))
                    require(path.is_relative_to(origin), 'Recorded search path escaped original project')
                    directories.append(path.relative_to(origin).as_posix())
            require(directories == manifest['search_directories'], 'Search-path receipt disagrees with manifest')
        if label == 'build_original_library':
            require('Build completed successfully.' in output, 'Missing successful Lake build output')
        if label in ['before_validate_object_hashes', 'after_validate_object_hashes']:
            check_output_hash_result(root, output, manifest['objects'])
    require(evidence_names == set(manifest['evidence_files']), 'Incomplete/extra binding evidence inventory')
    for name, record in manifest['evidence_files'].items():
        require(file_record(root / relative(name)) == record, 'Changed binding evidence: ' + name)
    for phase in ['before', 'after']:
        require(json.loads((root / run / ('project_traces_' + phase + '.json')).read_text()) == manifest['project_traces'],
                'Before/after project trace receipt differs from manifest')
    require(json.loads((root / PRIOR_RUN / 'project_traces_before.json').read_text()) == manifest['project_traces'],
            'Project traces changed from the baseline preceding the failed --rehash attempt')
    require(json.loads((root / PRIOR_RUN / 'SUMMARY.json').read_text())['status'] == 'FAIL',
            'The failed --rehash attempt must remain recorded as failed')
    for name, record in manifest['prior_attempt_evidence'].items():
        require(Path(name).parent.as_posix() == PRIOR_RUN and file_record(root / relative(name)) == record,
                'Changed prior rehash failure/diagnostic evidence: ' + name)
    require(set(manifest['prior_attempt_evidence']) ==
            {p.relative_to(root).as_posix() for p in (root / PRIOR_RUN).iterdir() if p.is_file()},
            'Incomplete prior attempt/diagnosis evidence inventory')
    pinned = (root / PROJECT_REL / 'lean-toolchain').read_text().strip().rsplit(':v', 1)[-1]
    require(manifest['lean_version'].startswith('Lean (version ' + pinned + ','), 'Unpinned recorded compiler version')
    compiler = relative(manifest['lean_executable'])
    require(compiler.name == 'lean' and compiler.parent.name == 'bin' and
            (PROJECT_REL + '/.toolchain/elan/toolchains/') in compiler.as_posix(),
            'Compiler is not the pinned local toolchain executable')
    core = (compiler.parent.parent / 'lib/lean').as_posix()
    require(core in manifest['search_directories'], 'Missing built-in standard-library object directory')
    expected_dirs = {PROJECT_REL + '/.lake/packages/' + item['name'] + '/.lake/build/lib/lean'
                     for item in manifest['dependencies']}
    expected_dirs.update({core, PROJECT_REL + '/.lake/build/lib/lean'})
    require(set(manifest['search_directories']) == expected_dirs, 'Incomplete/unexpected pinned search path')
    require(len(set(manifest['search_directories'])) == len(manifest['search_directories']), 'Duplicate search directories')
    require(set(manifest['compiler_files']) == {compiler.as_posix(), compiler.with_name('lake').as_posix(),
                                               PROJECT_REL + '/.toolchain/elan/bin/lake'},
            'Incomplete compiler executable inventory')


def check_manifest(root, manifest_path):
    manifest = json.loads(manifest_path.read_text())
    require(manifest.get('schema_version') == SCHEMA and
            manifest.get('status') == 'SEALED_TRUSTED_INCREMENTAL_CACHE',
            'Unknown/incomplete cache manifest')
    require(manifest['inherited_LEAN_PATH_cleared'] is True and
            manifest['inherited_LEAN_SRC_PATH_cleared'] is True and
            manifest['successful_rehash_build'] is False and
            manifest['independent_cached_output_hash_validation'] is True and
            manifest['fresh_original_library_build'] is False and
            manifest['fresh_mathlib_build'] is False, 'Incorrect cache evidence scope')
    require(manifest['build_command'] == ['lake', 'build', 'BfgsVerification'],
            'Missing explicit ordinary-build receipt')
    check_receipts(root, manifest)
    frozen, current_inputs = frozen_inputs(root)
    require(current_inputs == manifest['pinned_input_files'], 'Pinned input manifest differs')
    env = os.environ.copy()
    env['GIT_OPTIONAL_LOCKS'] = '0'

    def read_command(argv, tag, cwd):
        result = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True)
        require(result.returncode == 0, tag + ' failed: ' + result.stderr)
        return result.stdout

    require(package_states(root, read_command) == manifest['dependencies'],
            'Dependency state differs from sealed cache')
    require(project_trace_state(root, frozen) == manifest['project_traces'],
            'Project traces changed since the binding run')
    require(search_directory_state(root, manifest['search_directories']) == manifest['search_directory_state'],
            'Search directory presence changed since binding')
    objects, files = cache_inventory(root, manifest['search_directories'])
    require(objects == manifest['objects'], 'Cached object or paired-file inventory differs')
    require(files == manifest['cache_files'], 'Cached object/source/trace bytes differ')
    for name, expected in manifest['compiler_files'].items():
        require(file_record(root / relative(name)) == expected,
                'Compiler/Lake executable differs: ' + name)
    require(package_states(root, read_command) == manifest['dependencies'],
            'Dependencies changed during cache verification')
    for name, expected in manifest['evidence_files'].items():
        require(file_record(root / relative(name)) == expected,
                'Binding command evidence differs: ' + name)
    return {'status': 'PASS', 'scope': SCOPE, 'read_only_check': True,
            'root': str(root), 'manifest': str(manifest_path),
            'manifest_sha256': sha(manifest_path), 'object_count': len(objects),
            'sealed_cache_file_count': len(files), 'source_input_count': len(current_inputs),
            'fresh_original_library_build': False, 'fresh_mathlib_build': False}


def seal(root, run_id):
    require(re.fullmatch(r'[A-Za-z0-9_-]+', run_id) is not None, 'Unsafe run id')
    out = root / RUNS_REL / run_id
    out.mkdir(parents=True, exist_ok=False)
    project = root / PROJECT_REL
    commands = []
    env = command_environment(project)
    lake = str(project / '.toolchain/elan/bin/lake')
    phase = 'before'
    summary = {'status': 'RUNNING', 'scope': SCOPE, 'started_utc': now(),
               'run_directory': out.relative_to(root).as_posix(),
               'fresh_original_library_build': False, 'fresh_mathlib_build': False}

    def invoke(argv, tag, cwd=project):
        label = phase + '_' + tag
        stdout = out / (label + '.stdout.log')
        stderr = out / (label + '.stderr.log')
        require(not stdout.exists() and not stderr.exists(), 'Duplicate command label')
        started, clock = now(), time.monotonic()
        with stdout.open('wb') as so, stderr.open('wb') as se:
            result = subprocess.run(argv, cwd=cwd, env=env, stdout=so, stderr=se)
        commands.append({'command': argv, 'cwd': str(cwd), 'started_utc': started,
                         'seconds': time.monotonic() - clock, 'exit_code': result.returncode,
                         'stdout': stdout.relative_to(root).as_posix(), 'stdout_sha256': sha(stdout),
                         'stderr': stderr.relative_to(root).as_posix(), 'stderr_sha256': sha(stderr)})
        save(out / 'commands.json', commands)
        require(result.returncode == 0, label + ' failed; inspect retained logs')
        return stdout.read_text()

    try:
        frozen, inputs_before = frozen_inputs(root)
        dependencies_before = package_states(root, invoke)
        traces_before = project_trace_state(root, frozen)
        require(traces_before == json.loads((root / PRIOR_RUN / 'project_traces_before.json').read_text()),
                'Project trace differs from baseline preceding failed --rehash; explicit review required')
        save(out / 'project_traces_before.json', traces_before)
        version = invoke([lake, 'env', 'lean', '--version'], 'lean_version').strip()
        pinned = (project / 'lean-toolchain').read_text().strip().rsplit(':v', 1)[-1]
        require(version.startswith('Lean (version ' + pinned + ','), 'Wrong actual Lean version')
        lake_version = invoke([lake, '--version'], 'lake_version').strip()
        compiler = logical_path(root, invoke([lake, 'env', 'which', 'lean'], 'lean_executable').strip(), project)
        toolchain_lake = str(Path(compiler).with_name('lake'))
        compiler_paths = {compiler, toolchain_lake, PROJECT_REL + '/.toolchain/elan/bin/lake'}
        compiler_before = {p: file_record(root / p) for p in sorted(compiler_paths)}
        search = invoke([lake, 'env', 'printenv', 'LEAN_PATH'], 'search_path').strip()
        directories = [logical_path(root, p, project) for p in search.split(os.pathsep) if p]
        require(len(set(directories)) == len(directories), 'Duplicate search directory')
        require(PROJECT_REL + '/.lake/build/lib/lean' in directories, 'Missing project search directory')
        require((Path(compiler).parent.parent / 'lib/lean').as_posix() in directories,
                'Lake search path omits the built-in standard-library object directory')
        directory_state_before = search_directory_state(root, directories)
        objects_before, files_before = cache_inventory(root, directories)
        checker = out / 'ObjectHashCheck.lean'
        checker.write_text(HASH_CHECKER)
        object_list = out / 'object_paths.txt'
        object_list.write_text(''.join(name + '\n' for name in sorted(objects_before)))
        check_command = [lake, 'env', 'lean', '--run', str(checker), str(object_list)]
        before_hashes = check_output_hash_result(root, invoke(check_command, 'validate_object_hashes'), objects_before)
        phase = 'build'
        invoke([lake, 'build', 'BfgsVerification'], 'original_library')
        phase = 'after'
        require(package_states(root, invoke) == dependencies_before, 'Dependency state changed during build')
        _, inputs_after = frozen_inputs(root)
        require(inputs_after == inputs_before, 'Pinned inputs changed during build')
        traces_after = project_trace_state(root, frozen)
        save(out / 'project_traces_after.json', traces_after)
        if traces_after != traces_before:
            changed = sorted(p for p in set(traces_before) | set(traces_after)
                             if traces_before.get(p) != traces_after.get(p))
            summary['changed_project_traces'] = changed
            raise RuntimeError('Ordinary build changed project traces; review rebuilt modules and rerun audits before a new seal. No manifest written.')
        require({p: file_record(root / p) for p in compiler_paths} == compiler_before,
                'Compiler/Lake executable changed during build')
        objects, files = cache_inventory(root, directories)
        require(search_directory_state(root, directories) == directory_state_before,
                'Search directory presence changed during build')
        require(objects == objects_before and files == files_before,
                'Cached object/source/trace/hash inventory or bytes changed during ordinary build; review required')
        after_hashes = check_output_hash_result(root, invoke(check_command, 'validate_object_hashes'), objects)
        require(after_hashes == before_hashes, 'Cached binary output hashes changed during build')
        require(set(p for p, v in objects.items() if v['original_project']) == expected_project_objects(frozen),
                'Not every frozen project module is in the cache binding')
        evidence_paths = [out / 'commands.json', out / 'project_traces_before.json', out / 'project_traces_after.json',
                          checker, object_list]
        evidence_paths += [root / c[k] for c in commands for k in ['stdout', 'stderr']]
        manifest = {'schema_version': SCHEMA, 'status': 'SEALED_TRUSTED_INCREMENTAL_CACHE',
                    'scope': SCOPE, 'created_utc': now(), 'run_directory': out.relative_to(root).as_posix(),
                    'execution_root': str(root), 'lean_executable': compiler,
                    'inherited_LEAN_PATH_cleared': True, 'inherited_LEAN_SRC_PATH_cleared': True,
                    'fresh_original_library_build': False, 'fresh_mathlib_build': False,
                    'successful_rehash_build': False, 'independent_cached_output_hash_validation': True,
                    'build_command': ['lake', 'build', 'BfgsVerification'],
                    'lean_version': version, 'lake_version': lake_version,
                    'compiler_files': compiler_before, 'dependencies': dependencies_before,
                    'pinned_input_files': inputs_before, 'project_traces': traces_after,
                    'search_directories': directories, 'search_directory_state': directory_state_before,
                    'objects': objects, 'cache_files': files,
                    'evidence_files': {p.relative_to(root).as_posix(): file_record(p) for p in evidence_paths},
                    'prior_attempt_evidence': {p.relative_to(root).as_posix(): file_record(p)
                                              for p in sorted((root / PRIOR_RUN).iterdir()) if p.is_file()},
                    'trust_boundary': 'SHA-256 authenticates bytes. Before/after independent binary Lake-hash validation authenticates every present .olean.hash used by the ordinary incremental build. Existing project traces must stay identical to the baseline preceding the failed --rehash attempt. The tracked upstream JS metadata exception is retained explicitly; --rehash did not succeed. Imported objects are not independently re-typechecked; compiler/runtime, Lake traces and prior cache creation remain trusted.'}
        manifest_path = out / 'MANIFEST.json'
        save(manifest_path, manifest)
        # A second complete read detects post-build mutations before accepting the seal.
        verification = check_manifest(root, manifest_path)
        summary.update(status='PASS', manifest=manifest_path.relative_to(root).as_posix(),
                       manifest_sha256=sha(manifest_path), verification=verification,
                       object_count=len(objects), sealed_cache_file_count=len(files),
                       original_project_objects=len(traces_after), lean_version=version)
    except Exception as error:
        summary.update(status='FAIL', failure=str(error))
    finally:
        summary['ended_utc'] = now()
        summary['commands_sha256'] = sha(out / 'commands.json') if commands else None
        save(out / 'SUMMARY.json', summary)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--seal', action='store_true')
    modes.add_argument('--check', action='store_true')
    parser.add_argument('--root', type=Path, default=DEFAULT_ROOT,
                        help='Repository/extraction root; cache paths remain relative and may traverse explicit cache links.')
    parser.add_argument('--run-id')
    parser.add_argument('--manifest', type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        if args.seal:
            require(args.manifest is None, '--seal writes a new manifest, never overwrites one')
            run_id = args.run_id or datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S_%fZ')
            result = seal(root, run_id)
        else:
            require(args.manifest is not None and args.run_id is None, '--check requires --manifest and no --run-id')
            path = args.manifest if args.manifest.is_absolute() else root / args.manifest
            require(path.resolve().is_relative_to(root), 'Manifest must be inside the reviewed root')
            result = check_manifest(root, path)
    except Exception as error:
        result = {'status': 'FAIL', 'failure': str(error)}
    print(json.dumps(result, indent=2))
    return 0 if result['status'] == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
