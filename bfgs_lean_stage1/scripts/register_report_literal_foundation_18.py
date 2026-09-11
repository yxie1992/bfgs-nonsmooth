#!/usr/bin/env python3
"""Register two delivered targets; leave the final source freeze to freeze_sources.py.

The ordinary path requires the unchanged seventeenth Audit.lean. Root can then
replace only its reviewed enumeration prefix before freezing. This script does
not adopt any cached audit implementation or update release documentation.
"""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parent
ROOT=next(parent for parent in HERE.parents
          if (parent/'lakefile.toml').is_file() and (parent/'scripts/check.py').is_file())
BLOCK='REPORT_LITERAL_FOUNDATION_TARGETS'
TAIL='#print axioms BfgsVerification.CompressionAlgebra.gram_numerator_identity\n'

def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def registry(code):
    result={}
    for node in ast.parse(code).body:
        if isinstance(node,ast.Assign) and isinstance(node.value,ast.Dict):
            if any(isinstance(t,ast.Name) and (t.id=='TARGETS' or t.id.endswith('_TARGETS')) for t in node.targets):
                d=ast.literal_eval(node.value);assert not(result.keys()&d.keys());result.update(d)
    return result

def main():
    status=read(ROOT/'audit/STATUS.json')
    assert status['status']=='MODULE_M_AND_REPORT_SEMIALGEBRAIC_PATH_TARGETS_VERIFIED'
    assert not status['remaining_target_obligations'] and not status['unexpected_axioms'] and not status['missing_axiom_reports']
    prior=read(ROOT/'audit/report_semialgebraic_path_source_hashes.json');assert len(prior)==726
    for path,h in prior.items():assert sha((ROOT/path).read_bytes())==h,path
    baseline=read(ROOT/'audit/module_m_literal_registration_input_hashes.json')
    assert sha((ROOT/'scripts/check.py').read_bytes())==baseline['scripts/check.py']
    manifest='audit/module_m_literal_completion_declarations.json'
    m=read(ROOT/manifest);pairs=m['targets']
    assert len(m['declarations'])==18 and len(pairs)==2
    for command in [[sys.executable,m['provenance_validator']],
                    [sys.executable,'scripts/verify_report_sign_query_scoped.py','--validate-only','--manifest',manifest]]:
        output=subprocess.check_output(command,cwd=ROOT,text=True);assert 'PASS' in output;print(output,end='')
    log=(ROOT/'audit/module_m_literal_completion_axioms_contracts.log').read_text()
    assert re.findall(r'^EXACT_TARGET_OK (\S+)$',log,re.M)==[a for a,b in pairs]
    check=ROOT/'scripts/check.py';old=check.read_text();assert BLOCK not in old
    previous=registry(old);assert len(previous)==249
    code=BLOCK+' = {\n'
    for a,b in pairs:
        flag=a.removeprefix('BfgsVerification.').replace('.','_')+'_verified'
        assert flag not in previous and a not in {x for x,y in previous.values()}
        code+=f'    "{flag}":\n        ("{a}", "{b}"),\n'
    code+='}\n'
    assert old.count('ALL_TARGETS = ')==1
    new=old.replace('ALL_TARGETS = ',code+'ALL_TARGETS = ',1)
    anchor='| REPORT_SEMIALGEBRAIC_PATH_TARGETS\n';assert new.count(anchor)==1
    new=new.replace(anchor,'| REPORT_SEMIALGEBRAIC_PATH_TARGETS | '+BLOCK+'\n',1)
    before='MODULE_M_AND_REPORT_SEMIALGEBRAIC_PATH_TARGETS_VERIFIED'
    after='MODULE_M_AND_REPORT_LITERAL_FOUNDATION_TARGETS_VERIFIED'
    assert new.count(before)==1;new=new.replace(before,after,1)
    updated=registry(new);assert len(updated)==251
    assert all(updated[k]==v for k,v in previous.items())
    assert set(updated.values())-set(previous.values())==set(map(tuple,pairs))
    literal='status[flag] = name in inventory and inventory[name]["signature"] == signature'
    assert literal in old and literal in new
    modules=sorted((ROOT/'BfgsVerification').glob('*.lean'));assert len(modules)==727
    own={r['path'] for scope in m['scopes'] for r in scope['sources']}
    assert {str(p.relative_to(ROOT)) for p in modules}-set(prior)==own
    rp=ROOT/'BfgsVerification.lean';r=rp.read_text();assert '/-!' in r
    imports=''.join('import BfgsVerification.'+p.stem+'\n' for p in modules)+'\n'+r[r.index('/-!'):]
    ap=ROOT/'Audit.lean';audit=ap.read_text()
    marker='/- Eighteenth milestone: literal principal Gram sum and sharp finite-potential degree/root limit. -/'
    assert marker not in audit and TAIL in audit
    audit+='\n'+marker+'\n'
    for a,b in pairs:audit+=f'#print {b}\nexample : {b} := {a}\n#print axioms {a}\n'
    record=dict(target_count=251,source_count=729,check_sha256=sha(new.encode()),root_sha256=sha(imports.encode()),
                registered_audit_sha256=sha(audit.encode()),audit_tail_sha256=sha(audit[audit.index(TAIL):].encode()),
                cache_adoption='Not performed. Root may separately replace only the enumeration prefix before freeze.')
    paths=[ROOT/'audit/report_literal_foundation_targets.json',ROOT/'audit/module_m_literal_completion_registration.json']
    assert not any(p.exists() for p in paths)
    check.write_text(new);rp.write_text(imports);ap.write_text(audit)
    paths[0].write_text(json.dumps(pairs,indent=2)+'\n');paths[1].write_text(json.dumps(record,indent=2)+'\n')
    print('Registered2 new targets;251 total;729 source paths. Audit tail preserved;final source freeze and central gate still pending.')

if __name__=='__main__':main()
