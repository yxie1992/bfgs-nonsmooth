#!/usr/bin/env python3
"""Independently exercise public validation while forbidding excluded input reads."""
from pathlib import Path
import ast,datetime,hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'audit'
program='''import pathlib,runpy,sys
root=pathlib.Path.cwd()
def guard(event,args):
 if event=="open" and isinstance(args[0],(str,bytes)):
  path=pathlib.Path(args[0]).resolve()
  if path.is_relative_to(root/"audit/scratch") or path.is_relative_to(root/".scratch"):
   raise RuntimeError("EXCLUDED_INPUT_READ: "+str(path))
sys.addaudithook(guard)
sys.argv=sys.argv[1:]
runpy.run_path(sys.argv[0],run_name="__main__")
'''
commands=[]
for prefix in ['sign_query','positive_index','d_source_supplement','semialgebraic_projection','tame_geometry','d_literal_closure','boundary_sign','general_smooth_cover','critical_geometry']:
 commands.append(['scripts/verify_report_sign_query_scoped.py','--validate-only','--manifest',f'audit/{prefix}_declarations.json'])
commands += [[v] for v in ['audit/validate_smooth_components.py','audit/validate_semialgebraic_smooth_components.py','scripts/validate_d_literal_closure.py']]
commands += [[g,'--check'] for g in ['audit/generate_d_displays.py','audit/generate_d_auxiliary.py']]
with (OUT/'report_tame_geometry_delivered_only_validation.log').open('w') as log:
 log.write(datetime.datetime.now(datetime.timezone.utc).isoformat()+'\n')
 for cmd in commands:
  log.write('PUBLIC_COMMAND '+json.dumps(cmd)+'\n');log.flush()
  out=subprocess.check_output(['python3','-c',program,*cmd],cwd=ROOT,text=True,stderr=subprocess.STDOUT)
  assert 'PASS' in out,cmd
  log.write(out);log.flush()
 log.write('PASS all14 public validator/regeneration invocations with audit/scratch and .scratch input reads forbidden.\n')
print('PASS all14 public validators/regenerators with excluded-input audit hook active.')
