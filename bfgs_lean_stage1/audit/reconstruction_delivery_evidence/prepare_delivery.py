#!/usr/bin/env python3
"""Prepare eight import-only proof sources and public evidence; preview by default.

--apply is reserved for root after independent review. It requires the pushed
release18 baseline and never edits root imports, Audit, checker or status.
"""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
PREFIX='reconstruction_completion'
BASE='19c76918cb790c311157c85777aa24a76f185b05'
STANDARD={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
def report_check(text,names):
    assert 'error:' not in text
    rows=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)
    json_rows=[json.loads(line.split(' ',1)[1]) for line in text.splitlines() if line.startswith(('E_FACT_AUDIT ','E_FACT_PEER '))]
    assert not (rows and json_rows)
    if json_rows:
        assert all(isinstance(row['signature'],str) and row['signature'] for row in json_rows)
        rows=[(row['declaration'],','.join(row['axioms'])) for row in json_rows]
    assert len(rows)==len(names) and {n for n,_ in rows}==set(names)
    for n,a in rows:assert set(a.replace(',',' ').split())<=STANDARD,n

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--apply',action='store_true');args=parser.parse_args()
    assert git('rev-parse','HEAD')==BASE,'Prepared against the exact pushed release18 baseline'
    if args.apply:
        status=read(ROOT/'audit/STATUS.json')
        assert status['status']=='MODULE_M_AND_REPORT_LITERAL_FOUNDATION_TARGETS_VERIFIED'
        assert not status['unexpected_axioms'] and not status['missing_axiom_reports'] and not status['remaining_target_obligations']
        repo=Path(git('rev-parse','--show-toplevel'));rel=str((ROOT/'audit/STATUS.json').relative_to(repo))
        assert subprocess.check_output(['git','show','HEAD:'+rel],cwd=ROOT)==(ROOT/'audit/STATUS.json').read_bytes()
        assert git('rev-parse','@{upstream}')==BASE,'Previous release must be pushed'
    freeze=read(HERE/'frozen_inputs.json')
    owned={Path(row['path']).stem for scope in freeze['scopes'] for row in read(ROOT/scope['metadata'])['sources']}
    assert len(owned)==8
    payload={};scopes=[];names=[];pairs=[]
    for scope in freeze['scopes']:
        for rel,h in scope['hashes'].items():assert sha((ROOT/rel).read_bytes())==h,rel
        m=read(ROOT/scope['metadata']);ns=m['declarations']
        assert len(ns)==scope['declaration_count']
        for role in ['owner_validation','peer_validation']:
            t=(ROOT/scope[role]).read_text();assert re.search(r'^PASS(?:\s*:|\s+\d{4}-)',t,re.M) and 'FAIL' not in t
        for role in ['owner_axioms','peer_axioms']:report_check((ROOT/scope[role]).read_text(),ns)
        rows=[]
        for source in m['sources']:
            path=ROOT/scope['source_directory']/source['path'];raw=path.read_bytes()
            assert sha(raw)==source['sha256'];lines=raw.decode().splitlines(keepends=True);normal=[]
            for i,line in enumerate(lines):
                match=re.fullmatch(r'import ([A-Za-z0-9_.]+)\n',line)
                if match and match[1] in owned:
                    new='BfgsVerification.'+match[1]
                    normal.append(dict(line=i+1,reviewed_line=line,delivered_line='import '+new+'\n',**{'from':match[1],'to':new}))
                    lines[i]='import '+new+'\n'
            body=''.join(lines).encode();assert not re.search(rb'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',body)
            dest='BfgsVerification/'+Path(source['path']).name;assert dest not in payload
            payload[dest]=body
            rows.append(dict(path=dest,module='BfgsVerification.'+Path(source['path']).stem,
                sha256=sha(body),reviewed_original_sha256=sha(raw),reviewed_source=str(path.relative_to(ROOT)),
                import_normalizations=normal,declarations=source['declarations']))
        assert [n for row in rows for n in row['declarations']]==ns
        evidence=[];eh={};translation={}
        for src in scope['evidence']:
            assert not Path(src).is_absolute()
            rel='audit/reconstruction_reviews/'+scope['id']+'/'+str(Path(src).relative_to(scope['evidence_root']))
            assert '..' not in Path(rel).parts and rel not in payload
            raw=(ROOT/src).read_bytes();payload[rel]=raw;evidence.append(rel);eh[rel]=sha(raw);translation[src]=rel
        scopes.append(dict(id=scope['id'],sources=rows,declarations=ns,targets=m['targets'],
            review_evidence=evidence,review_evidence_hashes=eh,
            owner_validation=translation[scope['owner_validation']],peer_validation=translation[scope['peer_validation']]))
        names+=ns;pairs+=m['targets']
    assert len(names)==len(set(names))==85 and len(pairs)==4 and sum(len(s['sources']) for s in scopes)==8
    dependencies=freeze['main_dependency_hashes']
    for rel,h in dependencies.items():assert sha((ROOT/rel).read_bytes())==h,rel
    driver='audit/ReconstructionCompletionAudit.lean'
    m=dict(schema_version=1,log_prefix=PREFIX,audit_driver=driver,base_release=BASE,scopes=scopes,
        declarations=names,targets=pairs,main_dependency_hashes=dependencies,
        provenance_validator='audit/validate_reconstruction_completion_provenance.py',historical_paths_are_provenance_only=True)
    payload['audit/'+PREFIX+'_declarations.json']=(json.dumps(m,indent=2)+'\n').encode()
    audit=''.join('import '+row['module']+'\n' for scope in scopes for row in scope['sources'])+'import Lean\n\n'
    audit+=''.join('#check '+n+'\n#print axioms '+n+'\n' for n in names)
    for wrapper,target in pairs:
        audit+=f'\n#print {target}\nexample : {target} := {wrapper}\nopen Lean Elab Command in\nrun_cmd do\n  let info ← getConstInfo `{wrapper}\n  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `{target})\n  unless ok do throwError "Exact target type mismatch"\n  logInfo "EXACT_TARGET_OK {wrapper}"\n'
    payload[driver]=audit.encode()
    for source,dest in [('provenance_template.py','audit/validate_reconstruction_completion_provenance.py'),
        ('register_targets.py','scripts/register_report_reconstruction_19.py'),
        ('freeze_sources.py','scripts/freeze_report_reconstruction_19.py'),
        ('frozen_registration_inputs.json','audit/reconstruction_registration_input_hashes.json')]:
        payload[dest]=(HERE/source).read_bytes()
    destination=ROOT if args.apply else HERE/'preview'
    for rel,raw in payload.items():
        out=destination/rel
        if args.apply and out.exists():assert out.read_bytes()==raw,'Conflicting existing delivery:'+rel
    for rel,raw in payload.items():
        out=destination/rel;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(raw)
    result=dict(mode='applied' if args.apply else 'preview',sources=8,declarations=85,targets=4,
        files={rel:sha(raw) for rel,raw in payload.items()})
    (HERE/('apply_validation.json' if args.apply else 'preview_validation.json')).write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: '+result['mode']+';8 import-only sources/85 reports/4 targets;three frozen owner/peer scopes;central files untouched.')
if __name__=='__main__':main()
