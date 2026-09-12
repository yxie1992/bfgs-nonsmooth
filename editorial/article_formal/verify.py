#!/usr/bin/env python3
"""Compile article-only geometry wrappers and audit every module-owned helper."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, subprocess, sys

ROOT=Path(__file__).resolve().parents[2]
PROJECT=ROOT/'bfgs_lean_stage1'
HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--run-id',default=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
args=parser.parse_args()
if not args.run_id or any(c not in 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-' for c in args.run_id):
    raise SystemExit('run-id must use letters, numbers, underscore or hyphen')
run=HERE/'runs'/args.run_id
run.mkdir(parents=True,exist_ok=False)
build=run/'build';build.mkdir()
env=os.environ.copy()
elan=PROJECT/'.toolchain/elan'
if (elan/'bin/lake').is_file():
    env['ELAN_HOME']=str(elan)
    env['PATH']=str(elan/'bin')+os.pathsep+env['PATH']
env['XDG_CACHE_HOME']=str(PROJECT/'.cache')
env['MATHLIB_CACHE_DIR']=str(PROJECT/'.cache/mathlib')
commands=[]
def invoke(command,tag,runenv=env):
    start=datetime.datetime.now(datetime.timezone.utc).isoformat()
    result=subprocess.run(command,cwd=PROJECT,env=runenv,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (run/(tag+'.log')).write_text(result.stdout)
    commands.append({'command':command,'cwd':str(PROJECT),'started_utc':start,'exit_code':result.returncode,'log':str((run/(tag+'.log')).relative_to(ROOT))})
    (run/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    return result.stdout
baseline=json.loads((ROOT/'editorial/BASELINE.json').read_text())
source_names=['ArticleGeometry.lean','ConvexBalance.lean','DependencyAudit.lean','verify.py']
source_hashes={str((HERE/x).relative_to(ROOT)):hashlib.sha256((HERE/x).read_bytes()).hexdigest() for x in source_names}
for x in ['lean-toolchain','lakefile.toml','lake-manifest.json','master_report/DECLARATION_INDEX.json']:
    path=PROJECT/x
    if hashlib.sha256(path.read_bytes()).hexdigest()!=baseline['files'][str(path.relative_to(ROOT))]:
        raise SystemExit('Pinned project input differs from baseline: '+x)
version=invoke(['lake','env','lean','--version'],'00_version').strip()
expected_version=(PROJECT/'lean-toolchain').read_text().strip().rsplit(':v',1)[-1]
if not version.startswith('Lean (version '+expected_version+','):
    raise SystemExit('Actual Lean version does not match the pinned toolchain: '+version)
search=invoke(['lake','env','printenv','LEAN_PATH'],'01_search_path').strip()
for i,name in enumerate(['ArticleGeometry','ConvexBalance'],2):
    invoke(['lake','env','lean','-R',str(HERE),'-o',str(build/(name+'.olean')),str(HERE/(name+'.lean'))],f'{i:02d}_{name}')
audit_env=env.copy();audit_env['LEAN_PATH']=str(build)+os.pathsep+search
audit_env['BFGS_ARTICLE_AUDIT_OUT']=str(run)
invoke(['lean','-R',str(HERE),str(HERE/'DependencyAudit.lean')],'04_dependency_audit',audit_env)
summary=json.loads((run/'audit_summary.json').read_text())
if summary['status']!='PASS':raise SystemExit('Audit did not pass')
summary.update({'lean_version':version,'source_commit':baseline['source_commit'],'source_sha256':source_hashes,
                'scope':'Fresh supplemental article-only audit; original sealed sources and audit policy unchanged.',
                'run_directory':str(run.relative_to(ROOT))})
(run/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
