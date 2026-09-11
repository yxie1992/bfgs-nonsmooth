#!/usr/bin/env python3
"""Reconstructed E19 theorem jobs. No historical numerical run is replayed."""
from __future__ import annotations
import argparse,concurrent.futures,datetime,hashlib,json,os,platform,re,subprocess,sys,time
from pathlib import Path

PACKAGE=Path(__file__).resolve().parent
RUN_ROOT=None
ALLOWED={'propext','Classical.choice','Quot.sound'}

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def write_json(path,obj):path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def run_command(cmd,cwd,env,out,timeout):
    out.parent.mkdir(parents=True,exist_ok=True)
    start=utc();mono=time.monotonic()
    with out.open('w') as f:
        try:
            p=subprocess.run(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=timeout)
            code=p.returncode;timed_out=False
        except subprocess.TimeoutExpired:
            code=None;timed_out=True
    return {'command':list(map(str,cmd)),'cwd':str(cwd),'started_utc':start,'ended_utc':utc(),
            'elapsed_seconds':time.monotonic()-mono,'exit_code':code,'timed_out':timed_out,
            'log':str(out.relative_to(RUN_ROOT)) if RUN_ROOT else str(out),'log_sha256':digest(out)}
def parse_job(log,job):
    text=log.read_text()
    rows=[json.loads(s) for s in re.findall(r'E19_CHECK (\{[^\n]+\})',text)]
    expected={(c['theorem'],c['contract']) for c in job['checks']}
    got=[(r['theorem'],r['contract']) for r in rows]
    if set(got)!=expected or len(got)!=len(expected):raise ValueError('missing, repeated, or unexpected exact check')
    if not all(r['strict_definitional_type_check'] is True and set(r['axioms'])<=ALLOWED for r in rows):
        raise ValueError('failed exact type/axiom check')
    markers=re.findall(r'^E19_JOB_PASS (\d+)$',text,re.M)
    if markers!=[str(len(expected))]:raise ValueError('missing or repeated completion marker')
    if re.search(r'(^|\n).*error:',text):raise ValueError('Lean error in log')
    return rows

def main():
    global RUN_ROOT
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path)
    parser.add_argument('--validate-only',action='store_true')
    parser.add_argument('--run-dir',type=Path)
    parser.add_argument('--workers',type=int,default=3)
    parser.add_argument('--timeout',type=int,default=1800)
    args=parser.parse_args()
    if args.workers<1 or args.workers>19:parser.error('workers must be between 1 and 19')
    candidates=[args.project] if args.project else list(PACKAGE.parents)
    project=next((p.resolve() for p in candidates if p and (p/'lean-toolchain').is_file() and (p/'lakefile.toml').is_file()),None)
    if project is None:parser.error('could not locate pinned Lean project')
    if args.validate_only:
        import validate
        return validate.validate_run(project, (args.run_dir or PACKAGE/'fresh').resolve())
    run=(args.run_dir or PACKAGE/'fresh').resolve()
    if not run.is_relative_to(project):parser.error('all run artifacts must live inside this repository project')
    if run.exists() and args.run_dir is None:
        archive=PACKAGE/'runs'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
        archive.parent.mkdir(exist_ok=True)
        run.rename(archive)
    run.mkdir(parents=True,exist_ok=False)
    RUN_ROOT=run
    conf=json.loads((PACKAGE/'jobs.json').read_text());jobs=conf['jobs']
    if len(jobs)!=19 or len({j['job'] for j in jobs})!=19:raise ValueError('expected nineteen distinct jobs')
    own=[PACKAGE/'jobs.json',Path(__file__).resolve()]+[PACKAGE/j['driver'] for j in jobs]
    # Capture the complete local Lean source/input snapshot, not only headline aliases.
    inputs={str(p.relative_to(project)):digest(p) for p in sorted((project/'BfgsVerification').glob('*.lean'))}
    for p in [project/'BfgsVerification.lean',project/'lean-toolchain',project/'lakefile.toml',project/'lake-manifest.json',*own]:inputs[str(p.relative_to(project))]=digest(p)
    manifest_path=PACKAGE/'package_hashes.json'
    if not manifest_path.exists():raise ValueError('missing frozen package manifest')
    if manifest_path.exists():
        frozen=json.loads(manifest_path.read_text())
        for name,expected in frozen['files'].items():
            if digest(PACKAGE/name)!=expected:raise ValueError(f'package hash mismatch: {name}')
            inputs[str((PACKAGE/name).relative_to(project))]=expected
        for name,expected in frozen['main_inputs'].items():
            if digest(project/name)!=expected:raise ValueError(f'library input hash mismatch: {name}')
    inputs[str(manifest_path.relative_to(project))]=digest(manifest_path)
    write_json(run/'INPUTS.json',inputs)
    env=os.environ.copy();env.pop('LEAN_PATH',None);elan=project/'.toolchain/elan'
    if (elan/'bin/lake').is_file():
        env['ELAN_HOME']=str(elan);env['PATH']=str(elan/'bin')+os.pathsep+env.get('PATH','')
    env['XDG_CACHE_HOME']=str(project/'.cache');env['MATHLIB_CACHE_DIR']=str(project/'.cache/mathlib')
    lake=str(elan/'bin/lake') if (elan/'bin/lake').is_file() else 'lake'
    environment={'python':sys.version,'platform':platform.platform(),'machine':platform.machine(),'processor':platform.processor(),
        'lean_toolchain':(project/'lean-toolchain').read_text().strip(),'workers':args.workers,'timeout_seconds':args.timeout}
    for name,cmd in [('lean',[lake,'env','lean','--version']),('lake',[lake,'--version']),('git',['git','rev-parse','HEAD']),('mathlib',['git','-C','.lake/packages/mathlib','rev-parse','HEAD']),('mathlib_status',['git','-C','.lake/packages/mathlib','status','--porcelain','--untracked-files=no'])]:
        result=run_command(cmd,project,env,run/'environment'/f'{name}.log',60);environment[name]=result
        if result['exit_code']!=0:raise RuntimeError(f'environment command failed: {name}')
    pin=next(x['rev'] for x in json.loads((project/'lake-manifest.json').read_text())['packages'] if x['name']=='mathlib')
    actual=(run/'environment/mathlib.log').read_text().strip()
    if actual!=pin:raise RuntimeError('actual mathlib revision differs from lake-manifest pin')
    if (run/'environment/mathlib_status.log').read_text().strip():raise RuntimeError('tracked mathlib sources differ from pinned revision')
    if not re.fullmatch(r'Lean \(version 4\.19\.0, .*\)\s*',(run/'environment/lean.log').read_text()):raise RuntimeError('actual Lean version differs from 4.19.0 pin')
    environment['mathlib_pinned_revision']=pin
    write_json(run/'ENVIRONMENT.json',environment)
    summary={'schema_version':1,'status':'RUNNING','kind':'fresh_reconstructed_theorem_suite','historical_evidence_status':'superseded_unsupported_ai_generated_history',
        'started_utc':utc(),'mode':'delivered_main_facts',
        'environment':'ENVIRONMENT.json','environment_sha256':digest(run/'ENVIRONMENT.json'),'input_hashes':'INPUTS.json','input_hashes_sha256':digest(run/'INPUTS.json'),'jobs':[]}
    write_json(run/'SUMMARY.json',summary)
    buildmods=['BfgsVerification','BfgsVerification.EReconstructionFacts']
    build=run_command([lake,'build',*buildmods],project,env,run/'build.log',args.timeout)
    summary['build']=build
    if build['exit_code']!=0:summary['status']='FAIL';write_json(run/'SUMMARY.json',summary);return 1
    def job_task(job):
        jd=run/job['job'];jd.mkdir()
        result=run_command([lake,'env','lean',str(PACKAGE/job['driver'])],project,env,jd/'stdout.log',args.timeout)
        record={'job':job['job'],'method':job['method'],'status':'FAIL','execution':result,
                'driver':job['driver'],'driver_sha256':digest(PACKAGE/job['driver']),
                'mathematical_roles':job['mathematical_roles'],'source_lines':job['source_lines'],
                'authored_change':job['authored_change'],'unsupported_historical_assertions':job['unsupported_historical_assertions']}
        try:
            if result['exit_code']!=0:raise ValueError('compiler did not finish successfully')
            rows=parse_job(jd/'stdout.log',job);write_json(jd/'CHECKS.json',rows)
            record.update(status='PASS',actual_check_count=len(rows),checks=str((jd/'CHECKS.json').relative_to(run)),checks_sha256=digest(jd/'CHECKS.json'))
        except Exception as e:record['failure']=str(e)
        write_json(jd/'RESULT.json',record)
        return record
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures=[pool.submit(job_task,j) for j in jobs]
        for future in concurrent.futures.as_completed(futures):
            record=future.result();summary['jobs'].append(record)
            write_json(run/'SUMMARY.json',summary);print(record['job'],record['status'],flush=True)
    summary['jobs'].sort(key=lambda j:next(i for i,x in enumerate(jobs) if x['job']==j['job']))
    changed=[p for p,h in inputs.items() if not (project/p).is_file() or digest(project/p)!=h]
    summary['changed_inputs']=changed;summary['ended_utc']=utc()
    summary['status']='PASS' if not changed and all(j['status']=='PASS' for j in summary['jobs']) else 'FAIL'
    summary['actual_check_occurrences']=sum(j.get('actual_check_count',0) for j in summary['jobs'])
    summary['distinct_theorems_checked']=len({c['theorem'] for j in jobs for c in j['checks']})
    write_json(run/'SUMMARY.json',summary)
    print('SUMMARY',run/'SUMMARY.json',summary['status'],flush=True)
    return 0 if summary['status']=='PASS' else 1
if __name__=='__main__':raise SystemExit(main())
