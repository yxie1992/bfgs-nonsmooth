#!/usr/bin/env python3
"""Independent, read-only production validation plus isolated evidence corruption tests."""
import builtins, contextlib, copy, hashlib, importlib.util, io, json, pathlib, shutil, tempfile
ROOT=next(p for p in pathlib.Path(__file__).resolve().parents if (p/'lakefile.toml').is_file() and (p/'scripts/check.py').is_file())
RUNNER=ROOT/'scripts/verify_report_claim_review_20.py'
SPEC=importlib.util.spec_from_file_location('claim20_public_runner',RUNNER)
v=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(v)
HERE=pathlib.Path(__file__).resolve().parent
assert ROOT==v.PROJECT
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before={str(p.relative_to(ROOT)):h(p) for p in [RUNNER,v.PACKAGE/'jobs.json',v.PACKAGE/'fresh/SUMMARY.json']}
checks=[]
def ok(label):
 checks.append(label);print('PASS',label)
# Reject any attempted scratch input read during actual production validation.
old_open=builtins.open;old_io=io.open

def guarded(orig):
 def f(path,*args,**kwargs):
  if isinstance(path,(str,pathlib.Path)):
   mode=args[0] if args else kwargs.get('mode','r')
   if 'r' in mode and 'audit/scratch/' in str(pathlib.Path(path).resolve()):
    raise AssertionError('Production validator attempted excluded scratch read: '+str(path))
  return orig(path,*args,**kwargs)
 return f
builtins.open=guarded(old_open);io.open=guarded(old_io)
try:
 assert v.validate(v.PACKAGE/'fresh')==0
finally:
 builtins.open=old_open;io.open=old_io
ok('actual completed public evidence validates with all scratch input reads blocked')
conf,base=v.configuration()
assert len(conf['jobs'])==6
assert sum(len(j['ordinary_reports']) for j in conf['jobs'])==182
assert len({r['name'] for j in conf['jobs'] for r in j['ordinary_reports']})==141
assert sum(len(j['markers']) for j in conf['jobs'])==35
assert sum(len(j['own_declarations']) for j in conf['jobs'])==87
assert len({n for j in conf['jobs'] for n in j['own_declarations']})==70
ok('six-job exact counts182/141/35 and repeated own87/70 derived independently')
owner=next(j for j in conf['jobs'] if j['id']=='ORIGINAL')
peer=next(j for j in conf['jobs'] if j['id']=='ORIGINAL_PEER')
assert (v.PACKAGE/peer['source']).read_bytes().startswith((v.PACKAGE/owner['source']).read_bytes())
assert len(owner['own_declarations'])==17 and peer['repeated_own_declarations']==owner['own_declarations']
ok('peer driver exact owner prefix and all17 intentional repeated declarations')
# Independent source-token scanner checks: comments/strings ignored, live proofs not ignored.
text='/- admit /- axiom -/ sorry -/\n-- native_decide\n#eval "sorryAx \\\" admit"\nexample : True := by trivial\n'
code=v.lean_code(text)
assert not __import__('re').search(r'\b(?:sorry|admit|axiom|native_decide|sorryAx)\b',code)
for token in ['sorry','admit','axiom','native_decide','sorryAx']:
 assert __import__('re').search(r'\b'+token+r'\b',v.lean_code('/- harmless -/\n'+token))
for bad in ['/- missing end','"missing end']:
 try:v.lean_code(bad)
 except ValueError:pass
 else:raise AssertionError('malformed scanner input accepted')
ok('nested comment/string masking preserves rejection of live unchecked tokens')
# Direct ordered-output corruption tests exercise Lean evidence parsing.
def rejected(label,f):
 try:f()
 except (ValueError,KeyError,IndexError) as e:
  ok(label+' rejected: '+str(e)[:140]);return
 raise AssertionError('accepted corruption: '+label)
ac=next(j for j in conf['jobs'] if j['id']=='AC')
log=(v.PACKAGE/ac['reviewed_log']).read_text()
rejected('compiler error appended',lambda:v.parse_log(log+'\nerror: injected\n',ac))
rejected('sorryAx appended',lambda:v.parse_log(log+'\nsorryAx\n',ac))
first=next(v.PRINT_REPORT.finditer(log),None)
assert first is not None
rejected('one ordinary report removed',lambda:v.parse_log(log[:first.start()]+log[first.end():],ac))
rejected('ordinary report duplicated',lambda:v.parse_log(log+'\n'+first.group(0)+'\n',ac))
rejected('strict marker removed',lambda:v.parse_log(log.replace(ac['markers'][0],'',1),ac))
rejected('strict marker duplicated',lambda:v.parse_log(log+'\n'+ac['markers'][0]+'\n',ac))
badjob=copy.deepcopy(ac);badjob['ordinary_reports'][0]['axioms']=['inventedAxiom']
rejected('reviewed axiom expectation changed',lambda:v.parse_log(log,badjob))
js=next(j for j in conf['jobs'] if any('type_sha256' in x for x in j['ordinary_reports']))
badjob=copy.deepcopy(js)
next(x for x in badjob['ordinary_reports'] if 'type_sha256' in x)['type_sha256']='0'*64
rejected('actual type digest changed',lambda:v.parse_log((v.PACKAGE/js['reviewed_log']).read_text(),badjob))
# Full validation on private evidence-only copies; main sources and public evidence stay untouched.
def mutate_case(label,change):
 with tempfile.TemporaryDirectory(prefix='evidence_case_',dir=HERE) as d:
  case=pathlib.Path(d)/'fresh';shutil.copytree(v.PACKAGE/'fresh',case)
  s=v.read(case/'SUMMARY.json');change(case,s);v.write(case/'SUMMARY.json',s)
  rejected(label,lambda:v.validate(case))
mutate_case('incomplete summary status',lambda p,s:s.update(status='RUNNING'))
mutate_case('changed executed inputs',lambda p,s:s.update(changed_inputs=['BfgsVerification.lean']))
mutate_case('wrong manifest snapshot',lambda p,s:s.update(jobs_manifest_sha256='0'*64))
mutate_case('wrong aggregate count',lambda p,s:s.update(ordinary_report_occurrences=181))
mutate_case('wrong unique declaration count',lambda p,s:s.update(unique_reported_declarations=140))
mutate_case('wrong marker count',lambda p,s:s.update(marker_occurrences=34))
mutate_case('wrong job command',lambda p,s:s['jobs'][0]['execution'].update(command=['true']))
mutate_case('failed compiler exit code',lambda p,s:s['jobs'][0]['execution'].update(exit_code=1))
mutate_case('timed-out compiler',lambda p,s:s['jobs'][0]['execution'].update(timed_out=True))
mutate_case('missing job',lambda p,s:s['jobs'].pop())
mutate_case('reordered jobs',lambda p,s:s['jobs'].reverse())
mutate_case('changed output log bytes',lambda p,s:(p/s['jobs'][0]['execution']['log']).write_text('forged PASS\n'))
mutate_case('wrong source digest',lambda p,s:s['jobs'][0].update(source_sha256='0'*64))
mutate_case('incomplete ordinary report count',lambda p,s:s['jobs'][0].update(ordinary_report_count=1))
def input_bad(p,s):
 f=p/s['inputs']['path'];data=v.read(f);data['BfgsVerification.lean']='0'*64;v.write(f,data);s['inputs']['sha256']=h(f)
mutate_case('self-consistent changed input record',input_bad)
def env_bad(p,s):
 f=p/s['environment']['path'];data=v.read(f);data['inherited_LEAN_PATH_cleared']=False;v.write(f,data);s['environment']['sha256']=h(f)
mutate_case('self-consistent inherited Lean search path',env_bad)
def dep_bad(p,s):
 d=s['post_dependencies'][0];f=p/d['clean']['log'];f.write_text(' M source.lean\n');d['clean']['log_sha256']=h(f)
mutate_case('self-consistent dirty dependency log',dep_bad)
def rev_bad(p,s):
 d=s['post_dependencies'][0];f=p/d['head']['log'];f.write_text('0'*40+'\n');d['head']['log_sha256']=h(f)
mutate_case('self-consistent wrong dependency revision',rev_bad)
def parse_bad(p,s):
 f=p/s['jobs'][0]['reports']['path'];data=v.read(f);data.pop();v.write(f,data);s['jobs'][0]['reports']['sha256']=h(f)
mutate_case('self-consistent omitted parsed report',parse_bad)
for f,d in before.items():assert h(ROOT/f)==d
ok('public runner, manifest and completed evidence hashes remain unchanged')
print('TOTAL',len(checks),'independent checks PASS')
(HERE/'RUNNER_TEST_BINDINGS.json').write_text(json.dumps({'status':'PASS','checks':checks,'public_input_sha256':before},indent=2)+'\n')
