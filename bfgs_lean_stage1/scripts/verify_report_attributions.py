#!/usr/bin/env python3
"""Check citation revision preservation and attribution/Lean status separation.

Read-only. This validates reviewed editorial changes, not external paper proofs.
The exact prior Git commit is required for the preservation comparison.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent
HERE=ROOT/'master_report'
AUTH=HERE/'authoring/citation_revision'

def read(p):return json.loads(p.read_text())
def sha(data):return hashlib.sha256(data).hexdigest()
def historical(commit,name):
    assert re.fullmatch(r'[0-9a-f]{40}',commit)
    p=Path(name);assert not p.is_absolute() and '..' not in p.parts
    result=subprocess.run(['git','show',commit+':'+name],cwd=REPO,capture_output=True)
    assert result.returncode==0, 'Recorded prior report Git history is required: '+commit
    return result.stdout

def main():
    if not __debug__:raise RuntimeError('Run without -O.')
    baseline=read(AUTH/'BASELINE.json');commit=baseline['source_commit']
    prior={name:historical(commit,name) for name in baseline['files']}
    assert all(sha(prior[name])==h for name,h in baseline['files'].items())
    notes=[n for p in sorted(AUTH.glob('*_notes.json')) for n in read(p)]
    replacements=read(AUTH/'editorial_replacements.json')
    assert len(notes)==41 and len({n['id'] for n in notes})==41 and len(replacements)==5
    note_index={n['id']:n for n in notes}
    assert read(HERE/'BIBLIOGRAPHIC_NOTES.json')['notes']==notes
    claims=read(HERE/'CLAIMS.json')['claims']
    oldclaims=json.loads(prior['bfgs_lean_stage1/master_report/CLAIMS.json'])['claims']
    assert len(claims)==len(oldclaims)==172
    modules={c['module']:c['corrected_source'] for c in claims}
    for module,path in modules.items():
        content=(HERE/path).read_text();stripped=content
        for n in notes:
            if n['module']!=module:continue
            assert stripped.count(n['text'])==1,n['id']
            before=content[:content.index(n['text'])];stack=[]
            for kind,env in re.findall(r'\\(begin|end)\{([^}]+)\}',before):
                if kind=='begin':stack.append(env)
                else:
                    assert stack and stack.pop()==env,(module,env)
            assert not set(stack)&{'theorem','lemma','proposition','corollary','proof'},(n['id'],stack)
            stripped=stripped.replace(n['text'],'',1)
        for r in replacements:
            if r['module']==module:
                assert stripped.count(r['new'])==1,r['id'];stripped=stripped.replace(r['new'],r['old'],1)
        assert stripped.encode()==prior['bfgs_lean_stage1/master_report/'+path],('Changed mathematical chapter',module)
    note_occurrences=[]
    for new,old in zip(claims,oldclaims):
        for field in ['id','module','original_source','original_lines','original_sha256','classification','exports','review_note','inherited_review']:
            assert new[field]==old[field],('Changed formal correspondence',new['id'],field)
        ids=re.findall(r'% BEGIN ATTRIBUTION ([A-Za-z0-9_.]+)',new['corrected_excerpt'])
        assert ids==[n['id'] for n in new['bibliographic_notes']]
        for n in new['bibliographic_notes']:
            assert n['kind']=='bibliographic_attribution' and n['formal_status']=='Editorial source comparison; not a Lean-certified assertion'
            assert n['source_ids']==note_index[n['id']]['source_ids']
            note_occurrences.append(n['id'])
    assert set(note_occurrences)==set(note_index)
    assert (HERE/'DECLARATION_INDEX.json').read_bytes()==prior['bfgs_lean_stage1/master_report/DECLARATION_INDEX.json']
    changed=subprocess.check_output(['git','diff','--name-only',commit,'--','*.lean','*lean-toolchain','*lakefile.toml','*lake-manifest.json'],cwd=REPO,text=True).splitlines()
    assert not changed, ('Changed Lean proof or toolchain inputs',changed)
    sources={s['id'] for s in read(ROOT/'literature_audit/SOURCES.json')['sources']}
    assert all(set(n['source_ids'])<=sources for n in notes)
    bib=(HERE/'authoring/bibliography.tex').read_text()
    keys=re.findall(r'\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}',bib)
    assert len(keys)==len(set(keys))==53
    body='\n'.join(p.read_text() for p in (HERE/'latex').rglob('*.tex'))
    used={k.strip() for group in re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}',body) for k in group.split(',')}
    assert used<=set(keys),('Unresolved citation keys',used-set(keys))
    marker=r'\item[]\textbf{Internal source labels.}'
    oldbib=prior['bfgs_lean_stage1/master_report/authoring/bibliography.tex'].decode()
    assert bib.split(marker)[1]==oldbib.split(marker)[1]
    fields=read(HERE/'STATUS.json')['bibliographic_revision']
    assert fields['attribution_notes']==41 and fields['external_bibliography_entries']==38
    assert fields['external_source_comparisons_lean_verified'] is False
    print(json.dumps({'status':'PASS','baseline_commit':commit,'historical_hashes_verified':len(prior),
        'mathematical_chapters_recovered_exactly':len(modules),'attribution_notes':len(notes),
        'novelty_wording_edits':len(replacements),'unchanged_formal_export_lists':len(claims),
        'formal_declaration_index_byte_identical':True,'lean_and_toolchain_changes':changed,
        'notes_outside_theorem_and_proof_environments':True,
        'attribution_status_separate_from_lean':True,'bibliography_keys':len(keys),
        'external_works':38,'used_citation_keys':len(used),'internal_label_block_byte_identical':True,
        'scope':'Citation attribution and exact preservation; external-source claims are editorial scholarship, not Lean proofs.'},indent=2))

if __name__=='__main__':main()
