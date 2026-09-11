#!/usr/bin/env python3
"""Register the four audited reconstruction targets; preserve the full cached Audit."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'lakefile.toml').is_file() and (p/'scripts/check.py').is_file())
BLOCK='REPORT_RECONSTRUCTION_TARGETS'
TAIL='#print axioms BfgsVerification.CompressionAlgebra.gram_numerator_identity\n'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(rel):return json.loads((ROOT/rel).read_text())
def registry(code):
    result={}
    for node in ast.parse(code).body:
        if isinstance(node,ast.Assign) and isinstance(node.value,ast.Dict) and any(isinstance(t,ast.Name) and (t.id=='TARGETS' or t.id.endswith('_TARGETS')) for t in node.targets):
            d=ast.literal_eval(node.value);assert not result.keys()&d.keys();result.update(d)
    return result

def main():
    s=read('audit/STATUS.json');assert s['status']=='MODULE_M_AND_REPORT_LITERAL_FOUNDATION_TARGETS_VERIFIED'
    assert not s['remaining_target_obligations'] and not s['unexpected_axioms'] and not s['missing_axiom_reports']
    prior=read('audit/report_literal_foundation_source_hashes.json');assert len(prior)==729
    for path,h in prior.items():assert sha((ROOT/path).read_bytes())==h,path
    for path,h in read('audit/reconstruction_registration_input_hashes.json').items():assert sha((ROOT/path).read_bytes())==h,path
    manifest='audit/reconstruction_completion_declarations.json';m=read(manifest);pairs=m['targets']
    assert len(m['declarations'])==85 and len(pairs)==4
    for cmd in [[sys.executable,m['provenance_validator']],[sys.executable,'scripts/verify_report_sign_query_scoped.py','--validate-only','--manifest',manifest]]:
        out=subprocess.check_output(cmd,cwd=ROOT,text=True);assert 'PASS' in out;print(out,end='')
    log=(ROOT/'audit/reconstruction_completion_axioms_contracts.log').read_text()
    assert re.findall(r'^EXACT_TARGET_OK (\S+)$',log,re.M)==[n for n,t in pairs]
    check=ROOT/'scripts/check.py';old=check.read_text();assert BLOCK not in old
    previous=registry(old);assert len(previous)==251
    block=BLOCK+' = {\n'
    for name,target in pairs:
        flag=name.removeprefix('BfgsVerification.').replace('.','_')+'_verified'
        assert flag not in previous and name not in {a for a,b in previous.values()}
        block+=f'    "{flag}":\n        ("{name}", "{target}"),\n'
    block+='}\n';assert old.count('ALL_TARGETS = ')==1
    new=old.replace('ALL_TARGETS = ',block+'ALL_TARGETS = ',1)
    anchor='| REPORT_LITERAL_FOUNDATION_TARGETS\n';assert new.count(anchor)==1
    new=new.replace(anchor,'| REPORT_LITERAL_FOUNDATION_TARGETS | '+BLOCK+'\n',1)
    scope_before = "The literal A geometric ingredients are now proved: actual semialgebraic witness paths, finite actual continuous-semialgebraic path components, and continuous objective composition smooth outside finitely many interior parameters. Historical E jobs/counts/timings/environment/archive identities remain unverified without the original inputs. R182–187's numerical attribution to an unidentified older four-piece objective remains a mathematical source-attribution obligation; the verified current D objective does not identify that older objective. See REPORT_STATUS.json"
    scope_after = "The literal A geometric ingredients and an explicit R182–187 reconstruction are proved, including actual transformed full-BFGS failure and supporting errors. New E mathematical facts and reconstructed verification evidence are separate from unsupported attribution to original historical jobs, counts, timings, environments or archive identities. The original historical attribution is not recovered by these new proofs or runs. The core entire_report_verified flag remains false; corrected_report_verified is a separate report-level conjunction with its own evidence checks. See REPORT_STATUS.json"
    assert new.count(scope_before)==1
    new=new.replace(scope_before,scope_after,1)
    before='MODULE_M_AND_REPORT_LITERAL_FOUNDATION_TARGETS_VERIFIED';assert new.count(before)==1
    new=new.replace(before,'MODULE_M_AND_REPORT_RECONSTRUCTION_TARGETS_VERIFIED',1)
    updated=registry(new);assert len(updated)==255 and all(updated[k]==v for k,v in previous.items())
    assert set(updated.values())-set(previous.values())==set(map(tuple,pairs))
    literal='status[flag] = name in inventory and inventory[name]["signature"] == signature'
    assert literal in old and literal in new
    modules=sorted((ROOT/'BfgsVerification').glob('*.lean'));assert len(modules)==735
    own={row['path'] for scope in m['scopes'] for row in scope['sources']}
    assert {str(p.relative_to(ROOT)) for p in modules}-set(prior)==own
    root=ROOT/'BfgsVerification.lean';oldroot=root.read_text();assert '/-!' in oldroot
    imports=''.join('import BfgsVerification.'+p.stem+'\n' for p in modules)+'\n'+oldroot[oldroot.index('/-!'):]
    ap=ROOT/'Audit.lean';oldaudit=ap.read_text();assert oldaudit.count(TAIL)==1
    marker='/- Nineteenth milestone: explicit R reconstruction and new E mathematical facts. -/'
    assert marker not in oldaudit
    audit=oldaudit+'\n'+marker+'\n'+''.join(f'#print {target}\nexample : {target} := {name}\n#print axioms {name}\n' for name,target in pairs)
    assert audit.startswith(oldaudit)
    record=dict(target_count=255,source_count=737,check_sha256=sha(new.encode()),root_sha256=sha(imports.encode()),
        registered_audit_sha256=sha(audit.encode()),prior_audit_sha256=sha(oldaudit.encode()),
        cached_prefix_sha256=sha(oldaudit[:oldaudit.index(TAIL)].encode()),
        audit_tail_sha256=sha(audit[audit.index(TAIL):].encode()),
        outside_verified_scope_before=scope_before,outside_verified_scope_after=scope_after,
        whole_report_flag_promotion=False)
    pairpath=ROOT/'audit/report_reconstruction_targets.json';recordpath=ROOT/'audit/reconstruction_completion_registration.json'
    assert not pairpath.exists() and not recordpath.exists()
    check.write_text(new);root.write_text(imports);ap.write_text(audit)
    pairpath.write_text(json.dumps(pairs,indent=2)+'\n');recordpath.write_text(json.dumps(record,indent=2)+'\n')
    print('Registered4 new targets;255 total;737 source paths. Entire cached Audit and old tail preserved. Final freeze/full gate/status promotion remain pending.')
if __name__=='__main__':main()
