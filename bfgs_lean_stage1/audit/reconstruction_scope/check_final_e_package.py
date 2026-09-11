"""Independent public-only E package and adverse-evidence checks, after actual fresh PASS."""
from pathlib import Path
import json,hashlib,shutil,subprocess,sys,datetime,re
HERE=Path(__file__).resolve().parent; PROJECT=HERE.parents[2]; PACKAGE=PROJECT/'verification/reconstructed'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
m=read(PACKAGE/'package_hashes.json'); original=read(PACKAGE/'fresh/SUMMARY.json')
assert original['status']=='PASS' and original['mode']=='delivered_main_facts'
assert original['actual_check_occurrences']==107 and original['distinct_theorems_checked']==93
for f,h in m['files'].items():assert sha(PACKAGE/f)==h,f
for f,h in m['main_inputs'].items():assert sha(PROJECT/f)==h,f
fixture=HERE/'E19_peer_fixture';assert not fixture.exists(); fp=fixture/'project'; fpackage=fp/'verification/reconstructed'
fpackage.mkdir(parents=True)
for f in list(m['files'])+['package_hashes.json']:
 dest=fpackage/f;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(PACKAGE/f,dest)
for f in m['main_inputs']:
 dest=fp/f;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(PROJECT/f,dest)
shutil.copytree(PACKAGE/'fresh',fpackage/'fresh')
# Relocation keeps the exact original commands as historical data, never follows those paths.
program='''import pathlib,runpy,sys
root=pathlib.Path.cwd().resolve()
def guard(event,args):
 if event=="open" and isinstance(args[0],(str,bytes)):
  p=pathlib.Path(args[0]).resolve()
  if p.is_relative_to(root/"audit/scratch") or p.is_relative_to(root/".scratch"):
   raise RuntimeError("excluded scratch input:"+str(p))
sys.addaudithook(guard)
sys.argv=["verification/reconstructed/validate.py","--validate-only"]
runpy.run_path(sys.argv[0],run_name="__main__")
'''
logs=[]
def validate(label,ok=True):
 r=subprocess.run([sys.executable,'-c',program],cwd=fp,text=True,capture_output=True)
 assert (r.returncode==0)==ok,(label,r.stdout,r.stderr)
 logs.append(f'{label}: '+ ('PASS\n'+r.stdout if ok else 'PASS (correct rejection)\n'+r.stderr))
def write(p,o):p.write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
validate('relocated public-only baseline')
summary=fpackage/'fresh/SUMMARY.json'; baseline=summary.read_bytes()
def change_job(label,change):
 s=read(summary);j=s['jobs'][0];result=fpackage/'fresh'/j['job']/'RESULT.json';old=result.read_bytes()
 change(j);write(result,j);write(summary,s);validate(label,False);result.write_bytes(old);summary.write_bytes(baseline)
change_job('wrong recorded cwd',lambda j:j['execution'].__setitem__('cwd','/different/project'))
change_job('wrong absolute driver',lambda j:j['execution']['command'].__setitem__(-1,'/different/jobs/Job01.lean'))
change_job('incorrect check total',lambda j:j.__setitem__('actual_check_count',999))
s=read(summary);s['mode']='authoring_local_facts';write(summary,s);validate('authoring evidence excluded',False);summary.write_bytes(baseline)
log=fpackage/'fresh'/original['jobs'][0]['execution']['log'];old=log.read_bytes();log.write_bytes(old+b'corruption\n');validate('altered ordinary compiler log',False);log.write_bytes(old)
# Mutate fully rehashed environment evidence; pin validation must still reject it.
envp=fpackage/'fresh/ENVIRONMENT.json';eold=envp.read_bytes();env=read(envp);mp=fpackage/'fresh'/env['mathlib']['log'];mold=mp.read_bytes();mp.write_text('0'*40+'\n');env['mathlib']['log_sha256']=sha(mp);env['mathlib_pinned_revision']='0'*40;write(envp,env);s=read(summary);s['environment_sha256']=sha(envp);write(summary,s);validate('wrong actual mathlib pin after rehash',False);mp.write_bytes(mold);envp.write_bytes(eold);summary.write_bytes(baseline)
# Actual contract bodies cannot be changed even when the rest of the old evidence survives.
driver=fpackage/'jobs/Job01.lean';dold=driver.read_bytes();driver.write_bytes(dold+b'\n');validate('altered frozen contract source',False);driver.write_bytes(dold)
validate('restored public-only evidence')
allrows=[]
for j in original['jobs']:
 rows=read(PACKAGE/'fresh'/j['checks']);assert len(rows)==j['actual_check_count'];allrows+=rows
 assert all(row['strict_definitional_type_check'] and set(row['axioms'])<= {'propext','Classical.choice','Quot.sound'} for row in rows)
assert len(allrows)==107 and len({r['theorem'] for r in allrows})==93
binding={'package_manifest_sha256':sha(PACKAGE/'package_hashes.json'),'summary_sha256':sha(PACKAGE/'fresh/SUMMARY.json'),'actual_check_occurrences':107,'distinct_theorems':93,'package_files':m['files'],'main_inputs':m['main_inputs'],'run_evidence':{str(p.relative_to(PACKAGE/'fresh')):sha(p) for p in sorted((PACKAGE/'fresh').rglob('*')) if p.is_file()}}
(HERE/'E19_PACKAGE_PEER_HASHES.json').write_text(json.dumps(binding,indent=2)+'\n')
(HERE/'E19_PACKAGE_PEER_VALIDATION.log').write_text(datetime.datetime.now(datetime.timezone.utc).isoformat()+'\n'+''.join(logs)+'PASS: all19 actual fresh jobs/107 strict ordinary reports/93 unique theorems; immutable public sources, relocated evidence and adverse-case rejection verified.\n')
print('Independent E19 public-only fixture PASS')
