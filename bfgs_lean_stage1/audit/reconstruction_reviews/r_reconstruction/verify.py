#!/usr/bin/env python3
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess
P=Path(__file__).resolve().parent
ROOT=P.parents[2]
os.chdir(ROOT)
m=json.loads((P/'declarations.json').read_text())
def check_sources():
 for row in m['sources']:
  f=P/row['path'];raw=f.read_bytes();assert hashlib.sha256(raw).hexdigest()==row['sha256']
  assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',raw.decode()),row['path']
 for filename in ['main_dependency_hashes.json','scratch_dependency_hashes.json']:
  for f,h in json.loads((P/filename).read_text()).items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,f
check_sources()
objects=P/'objects';objects.mkdir(exist_ok=True)
env=os.environ.copy();env['LEAN_PATH']=str(objects)+os.pathsep+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip()
with (P/'build.log').open('w') as log:
 commands=[['lake','env','lean','--version'],['lake','build','BfgsVerification.CoerciveSeedIntercept','BfgsVerification.AffineWhiteningRun']]
 helper=ROOT/'audit/scratch/objective_value_scale19/ObjectiveValueScaling.lean'
 commands.append(['lean','-o',str(objects/'ObjectiveValueScaling.olean'),str(helper)])
 commands += [['lean','-o',str(objects/(Path(row['path']).stem+'.olean')),str(P/row['path'])] for row in m['sources']]
 for cmd in commands:
  log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush()
  subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
  log.write('COMPLETED '+cmd[-1]+'\n');log.flush()
with (P/'axioms_contracts.log').open('w') as log:
 subprocess.run(['lean',str(P/'Audit.lean')],env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
check_sources()
text=(P/'axioms_contracts.log').read_text();assert 'error:' not in text
reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)
assert [n for n,a in reports]==m['declarations']
for n,a in reports:assert set(a.replace(',',' ').split())<={'propext','Classical.choice','Quot.sound'},n
assert re.findall(r'^EXACT_TARGET_OK (\S+)$',text,re.M)==[n for n,t in m['targets']]
assert len(m['declarations'])==len(set(m['declarations']))==53
assert len(m['sources'])==5 and len(m['targets'])==2
out=datetime.datetime.now(datetime.timezone.utc).isoformat()+'\nPASS:5 frozen R reconstruction sources;53 actual complete type/standard transitive axiom reports;2 strict full targets;100 frozen main source dependencies;positive-scaling helper freshly rebuilt.\n'
(P/'validation.log').write_text(out);print(out)
