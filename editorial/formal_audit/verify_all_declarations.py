#!/usr/bin/env python3
"""Fresh module-owned safe-declaration audit, without mutating the central gate.

The mathematical traversal is performed by the two Lean drivers. Python binds
inputs, records commands, and compares their exact outputs to released evidence.
The five supplemental modules are exact byte copies of public claim-review20
sources; the peer source already embeds the sixth (owner) source verbatim.
"""
from __future__ import annotations
import argparse, collections, concurrent.futures, datetime, hashlib, importlib.util
import json, os, re, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = next(q for p in [HERE, *HERE.parents] for q in [p,p/'bfgs_lean_stage1'] if (q/'lakefile.toml').is_file())
SPEC = importlib.util.spec_from_file_location('review20', PROJECT/'scripts/verify_report_claim_review_20.py')
REVIEW20 = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(REVIEW20)
MODULES = {'M':'Master21ScopeM','AC':'Master21ScopeGeometry',
           'DL':'Master21ScopeNegative','SEARCH':'Master21ScopeFuel',
           'ORIGINAL_PEER':'Master21ScopeOriginalPeer'}
OUTPUTS = ['all_safe_declarations.json','compiler_implementation_declarations.json',
           'all_declaration_stats.json','unified_safe_declarations.json',
           'unified_compiler_declarations.json','unified_declaration_stats.json']
ALLOWED = {'propext','Classical.choice','Quot.sound'}

def require(ok, message):
    if not ok: raise ValueError(message)
def read(p): return json.loads(p.read_text())
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,x): p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def utc(): return datetime.datetime.now(datetime.timezone.utc).isoformat()

def inputs():
    conf, base = REVIEW20.configuration()
    names = {**base['main_sources'], **base['configuration']}
    for p in [PROJECT/'audit/declarations.json', PROJECT/'scripts/verify_report_claim_review_20.py',
              PROJECT/'audit/claim_review20/jobs.json',PROJECT/'audit/claim_review20/baseline.json',
              ]:
        names[str(p.relative_to(PROJECT))] = digest(p)
    for filename in ['AllDeclarations.lean','UnifiedAllDeclarations.lean','verify_all_declarations.py','expected_inventory.json']:
        names['@audit/'+filename]=digest(HERE/filename)
    for j in conf['jobs']:
        p=REVIEW20.PACKAGE/j['source'];names[str(p.relative_to(PROJECT))]=digest(p)
        local=HERE/j['source'];require(local.read_bytes()==p.read_bytes(),'copied supplemental source changed')
        names['@audit/'+j['source']]=digest(local)
    prefix=(PROJECT/'Audit.lean').read_text().split('namespace BfgsAuditCache\n',1)[1].split('end BfgsAuditCache',1)[0]
    for f in ['AllDeclarations.lean','UnifiedAllDeclarations.lean']:
        actual=(HERE/f).read_text().split('namespace BfgsAuditCache\n',1)[1].split('end BfgsAuditCache',1)[0]
        require(actual==prefix,'collector differs from reviewed central CollectAxioms implementation')
    for f in base['main_sources']:
        code=REVIEW20.lean_code((PROJECT/f).read_text())
        require(not re.search(r'\b(?:axiom|sorry|admit|native_decide|unsafe|implemented_by)\b',code), 'authored unchecked source: '+f)
    return conf,base,names

def compare(run):
    conf,base,_=inputs()
    a=read(run/'all_safe_declarations.json'); u=read(run/'unified_safe_declarations.json')
    ad={x['name']:x for x in a};ud={x['name']:x for x in u}
    require(len(ad)==len(a) and len(ud)==len(u),'duplicate safe names')
    expected=read(HERE/'expected_inventory.json')
    require(sorted(ad)==expected['main_safe_names'] and sorted(ud)==expected['unified_safe_names'],'exact safe-name inventory differs')
    require(sorted(ud.keys()-ad.keys())==expected['additional_supplemental_names'],'exact supplemental name delta differs')
    for rows,statsfile in [(a,'all_declaration_stats.json'),(u,'unified_declaration_stats.json')]:
        stats=read(run/statsfile)
        require(stats['safe_roots']==len(rows),'wrong root count')
        require(stats['missing']==stats['unsafe_or_partial_reachable']==[], 'unsafe/missing proof dependency')
        require(set(stats['axiom_seeds'])<=ALLOWED, 'nonstandard axiom seed')
        for x in rows:
            require(not x['unsafe'] and not x['partial'] and isinstance(x['isProp'],bool),'non-safe mathematical root')
            require(set(x['axioms'])<=ALLOWED and x['signature'].strip(), 'axiom/signature failure')
            for key in ['type_project_dependencies','value_project_dependencies','structural_project_dependencies']:
                require(all(n in (ad if statsfile.startswith('all_') else ud) for n in x[key]), 'missing direct safe project dependency')
    fields=['kind','unsafe','partial','signature','level_params','isProp','axioms',
            'type_project_dependencies','value_project_dependencies','structural_project_dependencies']
    for n,x in ad.items():
        require(n in ud and all(x[k]==ud[n][k] for k in fields), 'main constant changed in supplemental environment: '+n)
    old=read(PROJECT/'audit/declarations.json')
    for x in old:
        require(x['theorem'] in ad,'legacy theorem missing')
        y=ad[x['theorem']]
        require(x['signature']==y['signature'] and set(x['axioms'])==set(y['axioms']), 'legacy type/axioms changed')
    ordinary=[]
    for j in conf['jobs']:
        ordinary.extend(j['ordinary_reports'])
        for x in j['ordinary_reports']:
            require(x['name'] in ud and set(x['axioms'])==set(ud[x['name']]['axioms']), 'ordinary20 comparison failed: '+x['name'])
    for j in conf['jobs']:
        if j['id'] not in MODULES: continue
        REVIEW20.parse_log((run/'logs'/('scope_'+j['id']+'.log')).read_text(),j)
    expected_modules={Path(f).with_suffix('').as_posix().replace('/','.') for f in base['main_sources'] if f!='Audit.lean'}
    require(set(read(run/'all_declaration_stats.json')['module_names'])==expected_modules,'main module closure incomplete')
    excluded=read(run/'compiler_implementation_declarations.json')
    require(len(excluded)==1960 and all(x['unsafe'] or x['partial'] for x in excluded),'excluded inventory changed')
    ax=[x for x in excluded if x['kind']=='axiom']
    require(len(ax)==219 and all(x['unsafe'] for x in ax),'compiler axiom classification changed')
    require(all('._spec_' in x['name'] or '._elambda_' in x['name'] for x in ax),'unexpected compiler axiom name class')
    require(len(old)==7813 and len(a)==9672 and len(u)==9781,'baseline counts changed')
    extra_theorems=sorted(x['name'] for x in a if x['kind']=='theorem' and x['name'] not in {t['theorem'] for t in old})
    require(extra_theorems==expected['additional_main_theorems'] and len(extra_theorems)==61,'exact generated theorem delta changed')
    return {'status':'PASS','main_safe_constants':len(a),'unified_safe_constants':len(u),
      'main_kind_counts':dict(collections.Counter(x['kind'] for x in a)),
      'unified_kind_counts':dict(collections.Counter(x['kind'] for x in u)),
      'legacy_exact_types_and_axiom_sets':len(old),'new_theorem_names_outside_legacy_namespace':extra_theorems,'additional_private_theorem_count':sum(n.startswith('_private.') for n in extra_theorems),
      'supplemental_unique_added_constants':len(ud.keys()-ad.keys()),
      'supplemental_ordinary_occurrences':len(ordinary),'supplemental_ordinary_unique':len({x['name'] for x in ordinary}),
      'module_attribution_changes':[{ 'name':n,'main_module':x['module'],'unified_module':ud[n]['module']} for n,x in ad.items() if x['module']!=ud[n]['module']],
      'compiler_axiom_name_patterns':dict(collections.Counter('specialization' if '._spec_' in x['name'] else 'erased_lambda' for x in ax)),
      'unsafe_or_partial_reachable':[],'missing':[]}

def validate(run):
    conf,base,current=inputs();s=read(run/'SUMMARY.json')
    require(s['status']=='PASS' and read(run/'INPUTS.json')==current,'not a completed unchanged-input run')
    require(s['input_sha256']==digest(run/'INPUTS.json'),'input record changed')
    require(s['inherited_LEAN_PATH_cleared'] is True,'inherited import path not cleared')
    cwd=s['project_cwd']; recorded_run=Path(s['run_directory']); audit=Path(s['audit_directory'])
    require(all(Path(p).is_absolute() for p in [cwd,str(recorded_run),str(audit)]),'relative recorded execution roots')
    lake=str(Path(cwd)/'.toolchain/elan/bin/lake')
    expected=[]
    def depcommands(phase):
        for d in base['dependencies']:
            path='.lake/packages/'+d['name']
            expected.extend([(phase+'_'+d['name']+'_head',['git','-C',path,'rev-parse','HEAD']),
              (phase+'_'+d['name']+'_clean',['git','-C',path,'status','--porcelain','--untracked-files=all'])])
    depcommands('before')
    expected.extend([('lean_version',[lake,'env','lean','--version']),
      ('main_build',[lake,'build','BfgsVerification']),
      ('main_audit',[lake,'env','lean',str(audit/'AllDeclarations.lean')])])
    for j in conf['jobs']:
        if j['id'] not in MODULES:continue
        n=MODULES[j['id']]
        expected.append(('scope_'+j['id'],[lake,'env','lean','--root='+str(recorded_run/'scope_sources'),
          '-o',str(recorded_run/'scope_objects'/(n+'.olean')),str(recorded_run/'scope_sources'/(n+'.lean'))]))
    expected.extend([('lake_lean_path',[lake,'env','printenv','LEAN_PATH']),
      ('unified_audit',[lake,'env','lean',str(audit/'UnifiedAllDeclarations.lean')])])
    depcommands('after')
    require([(x['id'],x['command']) for x in s['commands']]==expected,'executed commands/order differ')
    for x in s['commands']:
        require(x['exit_code']==0 and x['cwd']==cwd,'failed/wrong-directory command')
        a=datetime.datetime.fromisoformat(x['started_utc']);b=datetime.datetime.fromisoformat(x['ended_utc'])
        require(a.tzinfo is not None and b>=a and abs((b-a).total_seconds()-x['elapsed_seconds'])<5,'invalid command timing')
        require(digest(run/x['log'])==x['log_sha256'],'command log changed')
        text=(run/x['log']).read_text();require(not re.search(r'\berror:|\bsorryAx\b',text),'Lean error/unchecked proof')
    commands={x['id']:x for x in s['commands']}
    def logtext(name): return (run/commands[name]['log']).read_text()
    require(re.fullmatch(r'Lean \(version 4\.19\.0, .*\)\s*',logtext('lean_version')) is not None,'actual Lean version differs')
    for phase in ['before','after']:
        for d in base['dependencies']:
            require(logtext(phase+'_'+d['name']+'_head').strip()==d['rev'] and not logtext(phase+'_'+d['name']+'_clean').strip(),'actual dependency evidence differs')
    require(s['unified_explicit_lean_path']==str(recorded_run/'scope_objects')+os.pathsep+logtext('lake_lean_path').strip(),'private import path differs')
    for name,statsfile in [('main_audit','all_declaration_stats.json'),('unified_audit','unified_declaration_stats.json')]:
        lines=[line for line in logtext(name).splitlines() if line.startswith('MASTER21_ALL_DECLARATIONS_PASS ')]
        require(len(lines)==1 and json.loads(lines[0].split(' ',1)[1])==read(run/statsfile),'actual audit marker/statistics differ')
    expected_outputs=set(OUTPUTS)|{'scope_sources/'+n+'.lean' for n in MODULES.values()}
    require(set(s['outputs'])==expected_outputs,'output inventory changed')
    for p,h in s['outputs'].items(): require(digest(run/p)==h,'output changed: '+p)
    require(s['comparison']==compare(run),'comparison changed')
    for phase in ['before_dependencies','after_dependencies']:
        require(s[phase]==s['expected_dependencies'],'pinned dependency dirty/changed')
    require(s['changed_inputs']==[],'input mutation during run')
    print('PASS: all 9672 main and 9781 unified safe constants; 7813 exact prior types/sets; 182 ordinary supplemental occurrences; no unsafe/partial/missing dependency')

def execute(run):
    conf,base,original_inputs=inputs(); require(not run.exists(),'choose a new run directory')
    run.mkdir(parents=True);(run/'logs').mkdir();(run/'scope_sources').mkdir();(run/'scope_objects').mkdir()
    write(run/'INPUTS.json',original_inputs)
    s={'status':'RUNNING','started_utc':utc(),'input_sha256':digest(run/'INPUTS.json'),'commands':[],
       'project_cwd':str(PROJECT),'audit_directory':str(HERE),'run_directory':str(run),'inherited_LEAN_PATH_cleared':True}
    env=os.environ.copy();env.pop('LEAN_PATH',None)
    elan=PROJECT/'.toolchain/elan';lake=str(elan/'bin/lake')
    env.update(ELAN_HOME=str(elan),PATH=str(elan/'bin')+os.pathsep+env.get('PATH',''),XDG_CACHE_HOME=str(PROJECT/'.cache'),MATHLIB_CACHE_DIR=str(PROJECT/'.cache/mathlib'))
    env['BFGS_MASTER21_AUDIT_OUT']=str(run)+os.sep
    def command(name,args,e=env):
        start=utc(); t=time.monotonic();log=run/'logs'/(name+'.log')
        with log.open('w') as f:p=subprocess.run(args,cwd=PROJECT,env=e,stdout=f,stderr=subprocess.STDOUT,timeout=7200)
        record={'id':name,'command':args,'cwd':str(PROJECT),'started_utc':start,'ended_utc':utc(),'elapsed_seconds':time.monotonic()-t,'exit_code':p.returncode,'log':str(log.relative_to(run)),'log_sha256':digest(log)}
        s['commands'].append(record);write(run/'SUMMARY.json',s)
        require(p.returncode==0,'command failed: '+name)
        return log.read_text()
    def dependencies(phase):
        vals=[]
        for d in base['dependencies']:
            prefix='.lake/packages/'+d['name']
            rev=command(phase+'_'+d['name']+'_head',['git','-C',prefix,'rev-parse','HEAD']).strip()
            dirty=command(phase+'_'+d['name']+'_clean',['git','-C',prefix,'status','--porcelain','--untracked-files=all']).strip()
            vals.append({'name':d['name'],'rev':rev,'dirty':dirty})
        return vals
    try:
        s['expected_dependencies']=[dict(d,dirty='') for d in base['dependencies']]
        s['before_dependencies']=dependencies('before')
        require(s['before_dependencies']==s['expected_dependencies'],'wrong/dirty pinned dependencies')
        version=command('lean_version',[lake,'env','lean','--version'])
        require(re.fullmatch(r'Lean \(version 4\.19\.0, .*\)\s*',version) is not None,'wrong Lean version')
        command('main_build',[lake,'build','BfgsVerification'])
        command('main_audit',[lake,'env','lean',str(HERE/'AllDeclarations.lean')])
        for j in conf['jobs']:
            if j['id'] not in MODULES:continue
            name=MODULES[j['id']];source=run/'scope_sources'/(name+'.lean');source.write_bytes((HERE/j['source']).read_bytes())
            require(digest(source)==j['source_sha256'],'supplement source byte mismatch')
            command('scope_'+j['id'],[lake,'env','lean','--root='+str(run/'scope_sources'),'-o',str(run/'scope_objects'/(name+'.olean')),str(source)])
        basepath=command('lake_lean_path',[lake,'env','printenv','LEAN_PATH']).strip()
        unified_env=env.copy();unified_env['LEAN_PATH']=str(run/'scope_objects')+os.pathsep+basepath
        s['unified_explicit_lean_path']=unified_env['LEAN_PATH']
        command('unified_audit',[lake,'env','lean',str(HERE/'UnifiedAllDeclarations.lean')],unified_env)
        s['after_dependencies']=dependencies('after')
        require(s['after_dependencies']==s['expected_dependencies'],'dependency changed during run')
        _,_,final_inputs=inputs();s['changed_inputs']=[p for p,h in original_inputs.items() if final_inputs.get(p)!=h]
        require(s['changed_inputs']==[],'inputs changed')
        s['comparison']=compare(run)
        s['outputs']={p:digest(run/p) for p in OUTPUTS}
        for p in (run/'scope_sources').glob('*.lean'):s['outputs'][str(p.relative_to(run))]=digest(p)
        s.update(status='PASS',ended_utc=utc());write(run/'SUMMARY.json',s)
        validate(run)
    except Exception as e:
        s.update(status='FAIL',ended_utc=utc(),failure=str(e));write(run/'SUMMARY.json',s);raise

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run',action='store_true');ap.add_argument('--run-dir',type=Path)
    args=ap.parse_args(); target=(args.run_dir or HERE/'fresh').resolve()
    if args.run:execute(target)
    else:validate(target)
