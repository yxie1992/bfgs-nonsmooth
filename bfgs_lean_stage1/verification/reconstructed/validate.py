#!/usr/bin/env python3
"""Validate delivered E19 evidence; never generate or trust a PASS by itself."""
import argparse,datetime,hashlib,json,re,sys
from pathlib import Path
PACKAGE=Path(__file__).resolve().parent
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def obj(p):return json.loads(p.read_text())
def artifact(root,name):
    p=(root/name).resolve()
    if not p.is_relative_to(root.resolve()):raise ValueError('artifact path escapes run directory')
    if not p.is_file():raise ValueError(f'missing artifact: {name}')
    return p
def require(condition,message):
    if not condition:raise ValueError(message)
def execution(run,e,recorded_cwd=None):
    if recorded_cwd is not None:require(e['cwd']==recorded_cwd,'inconsistent command working directory')
    require(e['exit_code']==0 and e['timed_out'] is False,'failed or incomplete command')
    require(isinstance(e['command'],list) and e['command'],'missing exact command')
    require(e['elapsed_seconds']>=0,'negative duration')
    start=datetime.datetime.fromisoformat(e['started_utc']);end=datetime.datetime.fromisoformat(e['ended_utc'])
    require(end>=start,'timestamps out of order')
    log=artifact(run,e['log']);require(sha(log)==e['log_sha256'],'execution log hash mismatch')
    return log

def validate_run(project,run):
    project=project.resolve();run=run.resolve()
    require(run.is_relative_to(project),'run must live in this project')
    conf=obj(PACKAGE/'jobs.json');frozen=obj(PACKAGE/'package_hashes.json')
    for path,expected in frozen['files'].items():require(sha(artifact(PACKAGE,path))==expected,f'package hash changed: {path}')
    for path,expected in frozen['main_inputs'].items():require(sha(artifact(project,path))==expected,f'library input changed: {path}')
    for path,provenance in frozen['import_only_provenance'].items():
        restored=artifact(PACKAGE,path).read_text()
        for norm in reversed(provenance['import_normalizations']):
            require(restored.count(norm['to'])==1,f'normalization is not unique: {path}')
            restored=restored.replace(norm['to'],norm['from'],1)
        require(hashlib.sha256(restored.encode()).hexdigest()==provenance['reviewed_original_sha256'],f'import-only provenance mismatch: {path}')
    require(len(conf['jobs'])==19 and len({j['job'] for j in conf['jobs']})==19,'nineteen distinct jobs required')
    summary=obj(run/'SUMMARY.json')
    require(summary['status']=='PASS','suite did not pass')
    require(summary['kind']=='fresh_reconstructed_theorem_suite','unexpected suite kind')
    require(summary['mode']=='delivered_main_facts','authoring run is not delivery evidence')
    require(summary['historical_evidence_status']=='superseded_unsupported_ai_generated_history','historical evidence status mismatch')
    require(summary['changed_inputs']==[],'source mutation during run')
    inp=artifact(run,summary['input_hashes']);require(sha(inp)==summary['input_hashes_sha256'],'input manifest hash mismatch')
    inputs=obj(inp)
    require(all(inputs.get(p)==h for p,h in frozen['main_inputs'].items()),'run does not bind frozen main inputs')
    for path,h in inputs.items():require(sha(artifact(project,path))==h,f'run input changed: {path}')
    envfile=artifact(run,summary['environment']);require(sha(envfile)==summary['environment_sha256'],'environment record hash mismatch')
    env=obj(envfile)
    require(env['lean_toolchain']==(project/'lean-toolchain').read_text().strip(),'toolchain pin mismatch')
    recorded_cwd=summary['build']['cwd']
    require(isinstance(recorded_cwd,str) and Path(recorded_cwd).is_absolute(),'missing absolute recorded project cwd')
    for key in ['lean','lake','git','mathlib','mathlib_status']:execution(run,env[key],recorded_cwd)
    require(re.fullmatch(r'Lean \(version 4\.19\.0, .*\)\s*',artifact(run,env['lean']['log']).read_text()) is not None,'not actual pinned Lean 4.19.0')
    pin=next(x['rev'] for x in obj(project/'lake-manifest.json')['packages'] if x['name']=='mathlib')
    require(env['mathlib_pinned_revision']==pin and artifact(run,env['mathlib']['log']).read_text().strip()==pin,'actual mathlib revision does not match pin')
    require(not artifact(run,env['mathlib_status']['log']).read_text().strip(),'tracked mathlib source changes')
    build=execution(run,summary['build'],recorded_cwd)
    require(summary['build']['command'][-3:]==['build','BfgsVerification','BfgsVerification.EReconstructionFacts'],'missing actual main build')
    jobs=summary['jobs'];require([j['job'] for j in jobs]==[j['job'] for j in conf['jobs']],'job list mismatch')
    total=0;distinct=set()
    for expected,actual in zip(conf['jobs'],jobs):
        label=actual['job'];require(actual['status']=='PASS',f'{label}: failed')
        require(actual['method']==expected['method']=='kernel_checked_theorem_counterpart',f'{label}: wrong method')
        for key in ['source_lines','mathematical_roles','authored_change','unsupported_historical_assertions']:
            require(actual[key]==expected[key],f'{label}: changed {key}')
        driver=artifact(PACKAGE,expected['driver'])
        require(actual['driver']==expected['driver'] and sha(driver)==actual['driver_sha256'],f'{label}: driver hash mismatch')
        source=driver.read_text()
        require('⋯' not in source and not re.search(r'\b(sorry|admit|native_decide)\b',source),f'{label}: omitted or unchecked proof')
        require(all(line.startswith('import BfgsVerification') for line in source.splitlines() if line.startswith('import ')),f'{label}: non-delivered import')
        log=execution(run,actual['execution'],recorded_cwd);text=log.read_text()
        expected_driver=str(Path(recorded_cwd)/PACKAGE.relative_to(project)/expected['driver'])
        require(actual['execution']['command']==[summary['build']['command'][0],'env','lean',expected_driver],f'{label}: wrong compiled driver or command')
        rows=[json.loads(s) for s in re.findall(r'E19_CHECK (\{[^\n]+\})',text)]
        pairs=[(r['theorem'],r['contract']) for r in rows]
        desired=[(c['theorem'],c['contract']) for c in expected['checks']]
        require(pairs==desired,f'{label}: missing, reordered or additional checks')
        require(re.findall(r'^E19_JOB_PASS (\d+)$',text,re.M)==[str(len(desired))],f'{label}: completion marker mismatch')
        require(not re.search(r'(^|\n).*error:',text),f'{label}: compiler error')
        for row in rows:
            require(row['strict_definitional_type_check'] is True and set(row['axioms'])<=ALLOWED,f'{label}: bad type or axiom')
            require(isinstance(row['signature'],str) and row['signature'],f'{label}: missing actual type')
            distinct.add(row['theorem'])
        checked=artifact(run,actual['checks'])
        require(sha(checked)==actual['checks_sha256'] and obj(checked)==rows,f'{label}: check record mismatch')
        require(obj(run/label/'RESULT.json')==actual,f'{label}: result/summary mismatch')
        require(actual['actual_check_count']==len(rows),f'{label}: count mismatch')
        total+=len(rows)
    require(summary['actual_check_occurrences']==total,'total check count mismatch')
    require(summary['distinct_theorems_checked']==len(distinct),'distinct theorem count mismatch')
    require(sum(j['job']=='R-interpretation' for j in jobs)==1,'missing R job')
    rjob=next(j for j in conf['jobs'] if j['job']=='R-interpretation')
    require({'BfgsVerification.reconstructedFourPieceFailure','BfgsVerification.reconstructedSupportingPlane'}<={c['theorem'] for c in rjob['checks']},'missing reconstructed R mathematical roles')
    print(f'PASS: 19 delivered jobs; {total} strict literal type/axiom checks; {len(distinct)} distinct theorems; all source/evidence hashes stable')
    return 0

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--validate-only',action='store_true');p.add_argument('--project',type=Path);p.add_argument('--run-dir',type=Path)
    a=p.parse_args();candidates=[a.project] if a.project else PACKAGE.parents
    project=next((x for x in candidates if x and (x/'lean-toolchain').exists() and (x/'lakefile.toml').exists()),None)
    if project is None:p.error('cannot locate project')
    return validate_run(project,a.run_dir or PACKAGE/'fresh')
if __name__=='__main__':
    try:raise SystemExit(main())
    except Exception as e:print('FAIL:',e,file=sys.stderr);raise SystemExit(1)
