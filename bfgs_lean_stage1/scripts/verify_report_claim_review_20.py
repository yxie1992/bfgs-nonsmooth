#!/usr/bin/env python3
"""Reproduce or validate the bounded original-report claim audits.

Default: read-only validation of delivered fresh evidence.
--run: build the pinned main library and freshly compile each unchanged Lean
source. Mathematical checks are performed by Lean's ordinary axiom collector
and strict contracts in those sources, never by Python arithmetic.
"""
from __future__ import annotations
import argparse, collections, concurrent.futures, datetime, hashlib, json, os
import platform, re, subprocess, sys, time
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[1]
PACKAGE = PROJECT / 'audit/claim_review20'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
PRINT_REPORT = re.compile(r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", re.M)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def artifact(root, name):
    require(isinstance(name, str) and not Path(name).is_absolute(), 'absolute artifact label')
    p = (root / name).resolve()
    require(p.is_relative_to(root.resolve()) and p.is_file(), f'missing/escaping artifact: {name}')
    return p


def original(name):
    p = (PROJECT.parent / name).resolve()
    require(p.is_relative_to(PROJECT.parent / 'BFGS_MASTER_REPORT_LaTeX/report/chapters') and p.is_file(), 'bad original report path')
    return p


def parse_log(text, job):
    require(not re.search(r'\berror:|\bsorryAx\b|\bdeclaration uses .sorry.\b', text), f"{job['id']}: compiler error/unchecked proof")
    events = []
    for m in PRINT_REPORT.finditer(text):
        ax = sorted(s.strip() for s in (m.group(2) or '').split(',') if s.strip())
        events.append((m.start(), {'format': 'print_axioms', 'name': m.group(1), 'axioms': ax}))
    for spec in job.get('json_reports', []):
        regex = re.compile(r'^' + re.escape(spec['prefix']) + r'([^\n]+)$', re.M)
        for m in regex.finditer(text):
            data = json.loads(m.group(1))
            ax = data[spec['axioms_key']]
            require(isinstance(ax, list) and all(isinstance(a, str) for a in ax), 'invalid ordinary axiom list')
            ty = data[spec['type_key']]
            require(isinstance(ty, str) and ty.strip(), 'missing actual theorem/definition type')
            events.append((m.start(), {'format': spec['prefix'], 'name': data[spec['name_key']], 'axioms': sorted(ax), 'type': ty}))
    rows = [e for _, e in sorted(events, key=lambda e: e[0])]
    expected = job['ordinary_reports']
    require([(r['format'], r['name']) for r in rows] == [(r['format'], r['name']) for r in expected], f"{job['id']}: missing, reordered, or additional ordinary reports")
    for row, exp in zip(rows, expected):
        require(set(row['axioms']) <= ALLOWED, f"{job['id']}: nonstandard axioms for {row['name']}")
        require(row['axioms'] == exp['axioms'], f"{job['id']}: axiom set differs from reviewed report")
        if 'type_sha256' in exp:
            require(hashlib.sha256(row['type'].encode()).hexdigest() == exp['type_sha256'], f"{job['id']}: actual type changed")
    prefixes = tuple(job['marker_prefixes'])
    markers = [line for line in text.splitlines() if line.startswith(prefixes)]
    require(markers == job['markers'], f"{job['id']}: exact marker sequence/count mismatch")
    require(set(job['own_declarations']) <= {r['name'] for r in rows}, 'own declaration omitted')
    return rows, markers


def lean_code(text):
    """Mask nested Lean comments and quoted strings without changing newlines."""
    out=[];i=0;depth=0;quoted=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i): depth+=1;out.extend('  ');i+=2
            elif text.startswith('-/',i): depth-=1;out.extend('  ');i+=2
            else: out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif quoted:
            if text[i]=='\\' and i+1<len(text): out.extend('  ');i+=2
            elif text[i]=='"': quoted=False;out.append(' ');i+=1
            else: out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif text.startswith('/-',i): depth=1;out.extend('  ');i+=2
        elif text.startswith('--',i):
            end=text.find('\n',i)
            if end<0: end=len(text)
            out.extend(' '*(end-i));i=end
        elif text[i]=='"': quoted=True;out.append(' ');i+=1
        else: out.append(text[i]);i+=1
    require(depth==0 and not quoted,'unclosed Lean comment/string')
    return ''.join(out)


def configuration():
    conf = read(PACKAGE / 'jobs.json')
    require(conf['schema_version'] == 1 and conf['kind'] == 'original_report_claim_review', 'wrong job manifest')
    require(set(conf['allowed_axioms']) == ALLOWED, 'changed allowed axiom semantics')
    basepath = artifact(PACKAGE, conf['baseline']['path'])
    require(digest(basepath) == conf['baseline']['sha256'], 'baseline hash mismatch')
    baseline = read(basepath)
    require(baseline['lean_toolchain'] == 'leanprover/lean4:v4.19.0', 'unexpected toolchain')
    actual_sources = {str(p.relative_to(PROJECT)) for p in (PROJECT/'BfgsVerification').glob('*.lean')} | {'BfgsVerification.lean', 'Audit.lean'}
    require(actual_sources == set(baseline['main_sources']) and len(actual_sources) == 737, '737-source baseline file set changed')
    for f, h in {**baseline['main_sources'], **baseline['configuration']}.items():
        require(digest(artifact(PROJECT, f)) == h, f'main/configuration hash changed: {f}')
    for f, h in baseline['original_report_sources'].items():
        require(digest(original(f)) == h, f'original report source changed: {f}')
    require((PROJECT/'lean-toolchain').read_text().strip() == baseline['lean_toolchain'], 'Lean pin changed')
    lake_manifest = read(PROJECT/'lake-manifest.json')
    packages = [{'name': p['name'], 'rev': p['rev']} for p in lake_manifest['packages']]
    require(packages == baseline['dependencies'], 'package pin list changed')
    jobs = conf['jobs']
    require(jobs and len({j['id'] for j in jobs}) == len(jobs), 'empty or duplicate job IDs')
    require(all(re.fullmatch(r'[a-zA-Z0-9_-]+', j['id']) for j in jobs), 'unsafe job ID')
    for j in jobs:
        p = artifact(PACKAGE, j['source'])
        require(digest(p) == j['source_sha256'] == j['reviewed_source_sha256'], f"{j['id']}: source correspondence failed")
        if 'exact_source_prefix' in j:
            prefix=j['exact_source_prefix'];prefixpath=artifact(PACKAGE,prefix['source'])
            require(digest(prefixpath)==prefix['sha256'] and p.read_bytes().startswith(prefixpath.read_bytes()), 'peer source does not embed exact reviewed owner bytes')
            owner=next((k for k in jobs if k['source']==prefix['source']),None)
            require(owner is not None and j['repeated_own_declarations']==owner['own_declarations'], 'repeated declaration inventory mismatch')
        source = lean_code(p.read_text())
        require(not re.search(r'\b(?:sorry|admit|axiom|native_decide|sorryAx)\b', source), f"{j['id']}: unchecked source")
        imports = re.findall(r'^import\s+([^\n]+)', source, re.M)
        require(imports and all(all(m == 'BfgsVerification' or m.startswith('BfgsVerification.') or m == 'Lean' or m.startswith('Lean.') for m in line.split()) for line in imports), f"{j['id']}: non-main import")
        for n in j['own_declarations']:
            require(re.search(r'^#check\s+@?' + re.escape(n) + r'(?=\s|$)', source, re.M), f'missing own #check: {n}')
        oldlog = artifact(PACKAGE, j['reviewed_log'])
        require(digest(oldlog) == j['reviewed_log_sha256'], 'reviewed log changed')
        parse_log(oldlog.read_text(), j)
    for f, h in conf['review_artifacts'].items():
        require(digest(artifact(PACKAGE, f)) == h, f'review artifact changed: {f}')
    return conf, baseline


def input_hashes(conf, baseline):
    values = {**baseline['main_sources'], **baseline['configuration']}
    for f in ['jobs.json', conf['baseline']['path'], *conf['review_artifacts']]:
        values[str((PACKAGE/f).relative_to(PROJECT))] = digest(PACKAGE/f)
    for j in conf['jobs']:
        for f in [j['source'], j['reviewed_log']]:
            values[str((PACKAGE/f).relative_to(PROJECT))] = digest(PACKAGE/f)
    values[str(Path(__file__).resolve().relative_to(PROJECT))] = digest(Path(__file__).resolve())
    return values


def execution(run, record, command, cwd):
    require(record['command'] == command and record['cwd'] == cwd, 'wrong command or cwd')
    require(record['exit_code'] == 0 and record['timed_out'] is False, 'incomplete/failed command')
    require(isinstance(record['elapsed_seconds'], (int,float)) and record['elapsed_seconds'] >= 0, 'invalid duration')
    start = datetime.datetime.fromisoformat(record['started_utc']); end = datetime.datetime.fromisoformat(record['ended_utc'])
    require(start.tzinfo is not None and end.tzinfo is not None and end >= start, 'invalid execution timestamps')
    require(abs((end-start).total_seconds()-record['elapsed_seconds']) < 5, 'inconsistent duration/timestamps')
    log = artifact(run, record['log'])
    require(digest(log) == record['log_sha256'], 'command log changed')
    return log.read_text()


def validate_environment(run, env, baseline):
    cwd = env['project_cwd']; require(Path(cwd).is_absolute(), 'recorded cwd not absolute')
    lake = str(Path(cwd)/'.toolchain/elan/bin/lake')
    require(env['lake_executable'] == lake and env['inherited_LEAN_PATH_cleared'] is True, 'wrong pinned runtime')
    require(env['lean_toolchain'] == baseline['lean_toolchain'], 'environment toolchain differs')
    lean = execution(run, env['lean'], [lake,'env','lean','--version'], cwd)
    require(re.fullmatch(r'Lean \(version 4\.19\.0, .*\)\s*', lean) is not None, 'actual Lean version mismatch')
    execution(run, env['lake'], [lake,'--version'], cwd)
    git = execution(run, env['git'], ['git','rev-parse','HEAD'], cwd)
    require(re.fullmatch(r'[0-9a-f]{40}\s*',git) is not None, 'missing actual repository revision')
    validate_dependency_records(run, env['dependencies'], baseline, cwd)
    return cwd, lake


def validate_dependency_records(run, records, baseline, cwd):
    require([d['name'] for d in records] == [d['name'] for d in baseline['dependencies']], 'dependency environment incomplete')
    for d, pin in zip(records, baseline['dependencies']):
        require(d['revision'] == pin['rev'], 'recorded dependency revision mismatch')
        path = '.lake/packages/'+pin['name']
        rev = execution(run, d['head'], ['git','-C',path,'rev-parse','HEAD'], cwd)
        clean = execution(run, d['clean'], ['git','-C',path,'status','--porcelain','--untracked-files=all'], cwd)
        require(rev.strip() == pin['rev'] and not clean.strip(), f"dirty/wrong dependency: {pin['name']}")


def validate(run):
    conf, baseline = configuration()
    summary = read(run/'SUMMARY.json')
    require(summary['schema_version'] == 1 and summary['kind'] == conf['kind'] and summary['status'] == 'PASS', 'not a completed claim review')
    require(summary['changed_inputs'] == [], 'inputs changed during execution')
    require(summary['jobs_manifest_sha256'] == digest(PACKAGE/'jobs.json'), 'job manifest differs from executed snapshot')
    inputsfile = artifact(run, summary['inputs']['path'])
    require(digest(inputsfile) == summary['inputs']['sha256'], 'input record changed')
    require(read(inputsfile) == input_hashes(conf, baseline), 'executed input snapshot mismatch')
    envfile = artifact(run, summary['environment']['path'])
    require(digest(envfile) == summary['environment']['sha256'], 'environment record changed')
    cwd,lake = validate_environment(run, read(envfile), baseline)
    execution(run, summary['build'], [lake,'build','BfgsVerification'], cwd)
    validate_dependency_records(run, summary['post_dependencies'], baseline, cwd)
    require([r['id'] for r in summary['jobs']] == [j['id'] for j in conf['jobs']], 'executed job list changed')
    allrows=[]; allmarkers=[]
    before=read(envfile)
    before_records=[before[k] for k in ['lean','lake','git']]+[d[k] for d in before['dependencies'] for k in ['head','clean']]
    require(all(datetime.datetime.fromisoformat(r['ended_utc']) <= datetime.datetime.fromisoformat(summary['build']['started_utc']) for r in before_records), 'environment was not checked before the build')
    for actual,j in zip(summary['jobs'],conf['jobs']):
        require(actual['status'] == 'PASS' and actual['source'] == j['source'] and actual['source_sha256'] == j['source_sha256'], 'wrong executed source')
        source = str(Path(cwd)/PACKAGE.relative_to(PROJECT)/j['source'])
        text = execution(run, actual['execution'], [lake,'env','lean',source], cwd)
        rows,markers = parse_log(text,j)
        parsed=artifact(run,actual['reports']['path'])
        require(digest(parsed)==actual['reports']['sha256'] and read(parsed)==rows, 'parsed report differs from actual Lean output')
        require(actual['ordinary_report_count']==len(rows) and actual['marker_count']==len(markers), 'job counts incorrect')
        require(read(artifact(run,actual['result'])) == actual, 'individual result/summary mismatch')
        allrows.extend(rows);allmarkers.extend(markers)
    last_job=max(datetime.datetime.fromisoformat(j['execution']['ended_utc']) for j in summary['jobs'])
    for d in summary['post_dependencies']:
        for k in ['head','clean']:
            require(datetime.datetime.fromisoformat(d[k]['started_utc']) >= last_job, 'dependency post-check precedes job completion')
            require(datetime.datetime.fromisoformat(d[k]['ended_utc']) <= datetime.datetime.fromisoformat(summary['ended_utc']), 'dependency post-check ends after summary')
    require(summary['ordinary_report_occurrences']==len(allrows) and summary['unique_reported_declarations']==len({r['name'] for r in allrows}) and summary['marker_occurrences']==len(allmarkers), 'aggregate counts wrong')
    require(summary['own_declarations']==[n for j in conf['jobs'] for n in j['own_declarations']], 'own declaration inventory wrong')
    require(summary['unique_own_declarations']==len(set(summary['own_declarations'])), 'unique own declaration count wrong')
    require(datetime.datetime.fromisoformat(summary['ended_utc']) >= datetime.datetime.fromisoformat(summary['started_utc']), 'summary timestamps wrong')
    print(f"PASS: {len(conf['jobs'])} original-claim jobs; {len(allrows)} ordinary report occurrences; {len({r['name'] for r in allrows})} distinct declarations; {len(allmarkers)} exact markers; 737 main hashes and all nine dependency revisions bound")
    return 0


def command(cmd, env, run, logname, timeout):
    out = run/logname; out.parent.mkdir(parents=True, exist_ok=True)
    start=utc();begin=time.monotonic()
    with out.open('w') as f:
        try:
            process=subprocess.run(cmd,cwd=PROJECT,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=timeout)
            code=process.returncode;expired=False
        except subprocess.TimeoutExpired:
            code=None;expired=True
    return {'command':cmd,'cwd':str(PROJECT),'started_utc':start,'ended_utc':utc(),
        'elapsed_seconds':time.monotonic()-begin,'exit_code':code,'timed_out':expired,
        'log':logname,'log_sha256':digest(out)}


def run_jobs(run, workers, timeout):
    conf, baseline = configuration()
    require(not run.exists(), 'run directory exists; choose a new --run-dir or archive the previous evidence explicitly')
    run.mkdir(parents=True)
    values=input_hashes(conf,baseline);write(run/'INPUTS.json',values)
    summary={'schema_version':1,'kind':conf['kind'],'status':'RUNNING','started_utc':utc(),
        'jobs_manifest_sha256':digest(PACKAGE/'jobs.json'),'inputs':{'path':'INPUTS.json','sha256':digest(run/'INPUTS.json')},'jobs':[]}
    write(run/'SUMMARY.json',summary)
    env=os.environ.copy();env.pop('LEAN_PATH',None)
    elan=PROJECT/'.toolchain/elan';lake=str(elan/'bin/lake')
    require(Path(lake).is_file(), 'project-local pinned elan/lake unavailable; run bootstrap first')
    env.update(ELAN_HOME=str(elan),PATH=str(elan/'bin')+os.pathsep+env.get('PATH',''),XDG_CACHE_HOME=str(PROJECT/'.cache'),MATHLIB_CACHE_DIR=str(PROJECT/'.cache/mathlib'))
    try:
        er={'project_cwd':str(PROJECT),'lake_executable':lake,'inherited_LEAN_PATH_cleared':True,'lean_toolchain':baseline['lean_toolchain'],'python':sys.version,'platform':platform.platform(),'workers':workers,'timeout_seconds':timeout,'dependencies':[]}
        for name,cmd in [('lean',[lake,'env','lean','--version']),('lake',[lake,'--version']),('git',['git','rev-parse','HEAD'])]:
            er[name]=command(cmd,env,run,'environment/'+name+'.log',60)
        for p in baseline['dependencies']:
            prefix='environment/'+p['name']; path='.lake/packages/'+p['name']
            er['dependencies'].append({'name':p['name'],'revision':p['rev'],
                'head':command(['git','-C',path,'rev-parse','HEAD'],env,run,prefix+'_head.log',60),
                'clean':command(['git','-C',path,'status','--porcelain','--untracked-files=all'],env,run,prefix+'_clean.log',60)})
        write(run/'ENVIRONMENT.json',er)
        summary['environment']={'path':'ENVIRONMENT.json','sha256':digest(run/'ENVIRONMENT.json')}
        validate_environment(run,er,baseline)
        summary['build']=command([lake,'build','BfgsVerification'],env,run,'build.log',timeout)
        execution(run,summary['build'],[lake,'build','BfgsVerification'],str(PROJECT))
        write(run/'SUMMARY.json',summary)
        def one(j):
            result={'id':j['id'],'status':'FAIL','source':j['source'],'source_sha256':digest(PACKAGE/j['source'])}
            try:
                result['execution']=command([lake,'env','lean',str(PACKAGE/j['source'])],env,run,j['id']+'/compiler.log',timeout)
                text=execution(run,result['execution'],[lake,'env','lean',str(PACKAGE/j['source'])],str(PROJECT))
                rows,markers=parse_log(text,j);f=j['id']+'/REPORTS.json';write(run/f,rows)
                result.update(status='PASS',reports={'path':f,'sha256':digest(run/f)},ordinary_report_count=len(rows),marker_count=len(markers))
            except Exception as e:
                result['failure']=str(e)
            result['result']=j['id']+'/RESULT.json';write(run/result['result'],result)
            return result
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
            futures=[pool.submit(one,j) for j in conf['jobs']]
            for f in concurrent.futures.as_completed(futures):
                result=f.result();summary['jobs'].append(result);write(run/'SUMMARY.json',summary)
                print(result['id'],result['status'],flush=True)
        summary['jobs'].sort(key=lambda r:next(i for i,j in enumerate(conf['jobs']) if j['id']==r['id']))
        summary['post_dependencies']=[]
        for pin in baseline['dependencies']:
            path='.lake/packages/'+pin['name'];prefix='post_environment/'+pin['name']
            summary['post_dependencies'].append({'name':pin['name'],'revision':pin['rev'],
                'head':command(['git','-C',path,'rev-parse','HEAD'],env,run,prefix+'_head.log',60),
                'clean':command(['git','-C',path,'status','--porcelain','--untracked-files=all'],env,run,prefix+'_clean.log',60)})
        validate_dependency_records(run,summary['post_dependencies'],baseline,str(PROJECT))
        summary['changed_inputs']=[f for f,h in values.items() if not (PROJECT/f).is_file() or digest(PROJECT/f)!=h]
        # Recheck the original reports and all reviewed metadata at completion too.
        configuration()
        summary.update(ended_utc=utc(),ordinary_report_occurrences=sum(j.get('ordinary_report_count',0) for j in summary['jobs']),
            unique_reported_declarations=len({r['name'] for j in conf['jobs'] for r in j['ordinary_reports']}),
            marker_occurrences=sum(j.get('marker_count',0) for j in summary['jobs']),
            own_declarations=[n for j in conf['jobs'] for n in j['own_declarations']],
            unique_own_declarations=len({n for j in conf['jobs'] for n in j['own_declarations']}))
        summary['status']='PASS' if not summary['changed_inputs'] and all(j['status']=='PASS' for j in summary['jobs']) else 'FAIL'
        write(run/'SUMMARY.json',summary)
        return validate(run)
    except Exception as e:
        summary.update(status='FAIL',ended_utc=utc(),failure=str(e));write(run/'SUMMARY.json',summary)
        raise


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run',action='store_true',help='freshly execute the pinned Lean audits')
    p.add_argument('--run-dir',type=Path,help='new run directory within this public package')
    p.add_argument('--workers',type=int,default=2)
    p.add_argument('--timeout',type=int,default=1800)
    a=p.parse_args();require(1<=a.workers<=8 and a.timeout>0,'invalid worker count or timeout')
    target=(a.run_dir or PACKAGE/'fresh').resolve()
    if a.run and a.run_dir is None and target.exists():
        target=PACKAGE/'runs'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    if a.run:
        print('Fresh claim-review run:',target,flush=True)
        print('Validate it with: python3 scripts/verify_report_claim_review_20.py --run-dir '+str(target.relative_to(PROJECT)),flush=True)
    require(target.is_relative_to(PACKAGE) and target != PACKAGE, 'run directory must remain inside the public claim-review package')
    return run_jobs(target,a.workers,a.timeout) if a.run else validate(target)


if __name__=='__main__':
    try:
        raise SystemExit(main())
    except Exception as e:
        print('FAIL:',e,file=sys.stderr)
        raise SystemExit(1)
