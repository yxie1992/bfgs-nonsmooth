#!/usr/bin/env python3
"""Fresh normalized preview build and private public-tooling fixture checks."""
from pathlib import Path
import ast,hashlib,json,os,re,shutil,subprocess,sys,datetime
P=Path(__file__).resolve().parent;ROOT=P.parents[2];os.chdir(ROOT)
preview=P/'preview';m=json.loads((preview/'audit/reconstruction_completion_declarations.json').read_text())
objects=P/'objects';(objects/'BfgsVerification').mkdir(parents=True,exist_ok=True)
owned={Path(s['path']).stem for scope in m['scopes'] for s in scope['sources']}
for f in (ROOT/'.lake/build/lib/lean/BfgsVerification').rglob('*'):
    if f.is_file() and f.stem not in owned:
        dest=objects/'BfgsVerification'/f.relative_to(ROOT/'.lake/build/lib/lean/BfgsVerification');dest.parent.mkdir(parents=True,exist_ok=True)
        if not dest.exists():dest.symlink_to(f.resolve())
env=os.environ.copy();env['LEAN_PATH']=str(objects)+os.pathsep+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip()
with (P/'preview_build.log').open('w') as log:
    for scope in m['scopes']:
        for source in scope['sources']:
            stem=Path(source['path']).stem
            cmd=['lean','-o',str(objects/'BfgsVerification'/(stem+'.olean')),str(preview/source['path'])]
            log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush()
            subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
            log.write('COMPILED '+source['path']+'\n');log.flush()
with (P/'preview_axioms_contracts.log').open('w') as log:
    subprocess.run(['lean',str(preview/m['audit_driver'])],env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
log=(P/'preview_axioms_contracts.log').read_text();assert 'error:' not in log
rows=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log)
assert [n for n,a in rows]==m['declarations'] and len(rows)==85
for n,a in rows:assert set(a.replace(',',' ').split())<={'propext','Classical.choice','Quot.sound'}
assert re.findall(r'^EXACT_TARGET_OK (\S+)$',log,re.M)==[n for n,t in m['targets']]
fixture=P/'private_fixture';assert not fixture.exists(),'Use a new fixture instead of overwriting a prior test'
shutil.copytree(preview,fixture)
prior=json.loads((ROOT/'audit/report_literal_foundation_source_hashes.json').read_text())
for rel in list(prior)+['lakefile.toml','scripts/check.py','scripts/verify_report_sign_query_scoped.py',
        'audit/STATUS.json','audit/report_literal_foundation_source_hashes.json']:
    dest=fixture/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/rel,dest)
for source,dest in [('preview_build.log','audit/reconstruction_completion_build.log'),
        ('preview_axioms_contracts.log','audit/reconstruction_completion_axioms_contracts.log')]:
    shutil.copyfile(P/source,fixture/dest)
PROGRAM='''import pathlib,runpy,sys
root=pathlib.Path.cwd()
def guard(event,args):
 if event=="open" and isinstance(args[0],(str,bytes)):
  p=pathlib.Path(args[0]).resolve()
  if p.is_relative_to(root/"audit/scratch") or p.is_relative_to(root/".scratch"):
   raise RuntimeError("Excluded input read:"+str(p))
sys.addaudithook(guard)
sys.argv=sys.argv[1:]
runpy.run_path(sys.argv[0],run_name="__main__")
'''
with (P/'fixture_validation.log').open('w') as out:
    def call(args,success=True,guard=False):
        cmd=[sys.executable,'-c',PROGRAM,*args] if guard else [sys.executable,*args]
        result=subprocess.run(cmd,cwd=fixture,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        if success:assert result.returncode==0,result.stdout;out.write(result.stdout)
        else:assert result.returncode!=0,'Corruption unexpectedly accepted';out.write('PASS: expected corruption rejection\n')
        out.flush()
    call(['audit/validate_reconstruction_completion_provenance.py'],guard=True)
    call(['scripts/verify_report_sign_query_scoped.py','--validate-only','--manifest','audit/reconstruction_completion_declarations.json'],guard=True)
    victim=fixture/m['scopes'][0]['sources'][0]['path'];original=victim.read_bytes();victim.write_bytes(original+b'\n')
    call(['audit/validate_reconstruction_completion_provenance.py'],success=False,guard=True);victim.write_bytes(original)
    oldaudit=(fixture/'Audit.lean').read_bytes();oldcheck=(fixture/'scripts/check.py').read_text()
    call(['scripts/register_report_reconstruction_19.py'])
    audit=(fixture/'Audit.lean').read_bytes();assert audit.startswith(oldaudit)
    def registry(code):
        d={}
        for node in ast.parse(code).body:
            if isinstance(node,ast.Assign) and isinstance(node.value,ast.Dict) and any(isinstance(t,ast.Name) and (t.id=='TARGETS' or t.id.endswith('_TARGETS')) for t in node.targets):
                dd=ast.literal_eval(node.value);assert not d.keys()&dd.keys();d.update(dd)
        return d
    oldtargets=registry(oldcheck);newtargets=registry((fixture/'scripts/check.py').read_text())
    assert len(oldtargets)==251 and len(newtargets)==255 and all(newtargets[k]==v for k,v in oldtargets.items())
    (fixture/'Audit.lean').write_bytes(b'\n'+audit);call(['scripts/freeze_report_reconstruction_19.py'],success=False);(fixture/'Audit.lean').write_bytes(audit)
    call(['scripts/freeze_report_reconstruction_19.py'])
    freeze=json.loads((fixture/'audit/report_reconstruction_source_hashes.json').read_text());assert len(freeze)==737
    for rel,h in prior.items():
        if rel not in ['Audit.lean','BfgsVerification.lean']:assert hashlib.sha256((fixture/rel).read_bytes()).hexdigest()==h
    out.write('PASS: private255-target/737-source registration and freeze;all727 old library proofs/251 pairs and complete cached Audit unchanged;main untouched.\n')
for rel,h in prior.items():assert hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==h,rel
for f,h in json.loads((P/'frozen_registration_inputs.json').read_text()).items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,f
result=datetime.datetime.now(datetime.timezone.utc).isoformat()+'\nPASS:8 import-normalized sources freshly compiled;85 actual type/ordinary-axiom reports;4 strict targets;public-only fixture/provenance/corruption/registration/freeze checks;main unchanged.\n'
(P/'preview_gate_validation.log').write_text(result);print(result)
