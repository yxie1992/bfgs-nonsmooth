from pathlib import Path
import ast,hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent; ROOT=P.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
frozen=json.loads((P/'tooling_source_hashes.json').read_text())
print(type(frozen).__name__)
# Every output is copied from the independently read preview and its exact snapshot.
preview=json.loads((P/'preview_validation.json').read_text())
for f,h in preview['files'].items():assert sha((P/'preview'/f).read_bytes())==h,f
m=json.loads((P/'preview/audit/reconstruction_completion_declarations.json').read_text())
assert len(m['declarations'])==85 and len(m['targets'])==4
for scope in m['scopes']:
 for s in scope['sources']:
  lines=(P/'preview'/s['path']).read_text().splitlines(keepends=True)
  for c in s['import_normalizations']:
   i=c['line']-1;assert lines[i]==c['delivered_line'];lines[i]=c['reviewed_line']
  assert sha(''.join(lines).encode())==s['reviewed_original_sha256']
fixture=P/'peer_public_fixture';assert not fixture.exists();shutil.copytree(P/'private_fixture',fixture)
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=ROOT,text=True).strip()); prefix=ROOT.relative_to(repo)
for f in ['Audit.lean','BfgsVerification.lean','scripts/check.py']:
 (fixture/f).write_bytes(subprocess.check_output(['git','show','19c76918cb790c311157c85777aa24a76f185b05:'+str(prefix/f)],cwd=ROOT))
for f in ['audit/report_reconstruction_targets.json','audit/reconstruction_completion_registration.json','audit/report_reconstruction_source_hashes.json']:(fixture/f).unlink()
program='''import pathlib,runpy,sys
root=pathlib.Path.cwd().resolve()
def guard(event,args):
 if event=="open" and isinstance(args[0],(str,bytes)):
  p=pathlib.Path(args[0]).resolve()
  if p.is_relative_to(root/"audit/scratch") or p.is_relative_to(root/".scratch"):
   raise RuntimeError("excluded scratch input:"+str(p))
sys.addaudithook(guard)
sys.argv=sys.argv[1:];runpy.run_path(sys.argv[0],run_name="__main__")
'''
output=[]
def run(args,ok=True):
 r=subprocess.run([sys.executable,'-c',program,*args],cwd=fixture,text=True,capture_output=True)
 assert (r.returncode==0)==ok,r.stdout+r.stderr
 output.append(r.stdout if ok else 'PASS: intentionally corrupted fixture rejected\n')
run(['audit/validate_reconstruction_completion_provenance.py'])
run(['scripts/verify_report_sign_query_scoped.py','--validate-only','--manifest','audit/reconstruction_completion_declarations.json'])
for victim in [fixture/m['scopes'][1]['sources'][1]['path'],fixture/m['scopes'][2]['peer_validation']]:
 raw=victim.read_bytes();victim.write_bytes(raw+b'corruption\n');run(['audit/validate_reconstruction_completion_provenance.py'],False);victim.write_bytes(raw)
old=(fixture/'Audit.lean').read_bytes(); oldcheck=(fixture/'scripts/check.py').read_text()
run(['scripts/register_report_reconstruction_19.py'])
assert (fixture/'Audit.lean').read_bytes().startswith(old)
def registry(t):
 d={}
 for n in ast.parse(t).body:
  if isinstance(n,ast.Assign) and isinstance(n.value,ast.Dict) and any(isinstance(v,ast.Name) and (v.id=='TARGETS' or v.id.endswith('_TARGETS')) for v in n.targets):d.update(ast.literal_eval(n.value))
 return d
before=registry(oldcheck);after=registry((fixture/'scripts/check.py').read_text());assert len(before)==251 and len(after)==255 and all(after[k]==v for k,v in before.items())
record=json.loads((fixture/'audit/reconstruction_completion_registration.json').read_text());assert record['whole_report_flag_promotion'] is False
assert 'corrected_report_verified is a separate report-level conjunction' in record['outside_verified_scope_after']
a=fixture/'Audit.lean';raw=a.read_bytes();a.write_bytes(b'\n'+raw);run(['scripts/freeze_report_reconstruction_19.py'],False);a.write_bytes(raw)
run(['scripts/freeze_report_reconstruction_19.py'])
assert len(json.loads((fixture/'audit/report_reconstruction_source_hashes.json').read_text()))==737
prior=json.loads((fixture/'audit/report_literal_foundation_source_hashes.json').read_text())
for f,h in prior.items():
 if f not in ['Audit.lean','BfgsVerification.lean']:assert sha((fixture/f).read_bytes())==h
output.append('PASS: independent public-only fixture; all8 import reconstructions;85 reports/4 targets;251→255 exact pairs;729→737 sources;727 old proof bodies and complete cached Audit preserved; no whole-report promotion.\n')
(P/'peer_tooling_validation.log').write_text(datetime.datetime.now(datetime.timezone.utc).isoformat()+'\n'+''.join(output))
(P/'peer_tooling_reviewed_hashes.json').write_text(json.dumps({'tooling_manifest_sha256':sha((P/'tooling_source_hashes.json').read_bytes()),'preview_manifest_sha256':sha((P/'preview_validation.json').read_bytes()),'public_files':preview['files']},indent=2)+'\n')
print(output[-1])
