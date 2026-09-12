#!/usr/bin/env python3
"""Apply reviewed citation-only insertions to the guarded original-source edit ledger.

Historical report sources and all Lean proofs are untouched. Each insertion has
an exact current-text anchor and labelled boundaries, so deleting inserted notes
must recover the prior corrected chapter byte for byte.
"""
from pathlib import Path
import importlib.util
import json
import subprocess

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent
HERE=ROOT/'master_report'
AUTH=HERE/'authoring/citation_revision'
spec=importlib.util.spec_from_file_location('report_builder',ROOT/'scripts/build_rigorous_master_report.py')
builder=importlib.util.module_from_spec(spec);spec.loader.exec_module(builder)

def read(p):return json.loads(p.read_text())
def old_text(commit,path):return subprocess.check_output(['git','show',commit+':'+str(path.relative_to(REPO))],cwd=REPO).decode()

def main():
    if not __debug__:raise RuntimeError('Run without -O.')
    baseline=read(AUTH/'BASELINE.json');commit=baseline['source_commit']
    ledger_files=sorted((HERE/'edits').glob('*.json'))
    ledgers={p:read(p) for p in ledger_files}
    addition_path=HERE/'edits/60_attributions.json'
    assert addition_path not in ledgers, 'Already applied; review/revert the citation revision before reapplying.'
    ledgers[addition_path]=[]
    mods=read(ROOT/'audit/REPORT_STATUS.json')['modules']
    source_by_module={m['module']:m['source'] for m in mods}
    notes=[n for p in sorted(AUTH.glob('*_notes.json')) for n in read(p)]
    assert len({n['id'] for n in notes})==len(notes)
    changes=[]
    for note in notes:
        source_path=REPO/source_by_module[note['module']]
        raw=source_path.read_text()
        own=[e for es in ledgers.values() for e in es if e['source']==source_by_module[note['module']]]
        corrected,mapping=builder.edited_source(raw,own)
        anchor=note['anchor'];assert corrected.count(anchor)==1, ('Nonunique note anchor',note['id'])
        assert '% BEGIN ATTRIBUTION '+note['id'] not in corrected
        position=corrected.index(anchor)+(len(anchor) if note['position']=='after' else 0)
        # Prefer an existing edit containing this insertion; otherwise map to an
        # unchanged original-source interval and make a new nonoverlapping edit.
        segment=next((m for m in mapping if m['edit'] and m['new'][0]<=position<=m['new'][1]),None)
        if segment:
            e=next(e for e in own if e['id']==segment['edit'])
            offset=position-segment['new'][0]
            e['new']=e['new'][:offset]+note['text']+e['new'][offset:]
            e.setdefault('attribution_insertions',[]).append(note['id'])
            edit_id=e['id']
        else:
            segment=next(m for m in mapping if m['edit'] is None and m['new'][0]<=position<=m['new'][1])
            original_position=segment['old'][0]+position-segment['new'][0]
            # Use the surrounding source line(s) as a short unique anchor.
            start=raw.rfind('\n',segment['old'][0],max(segment['old'][0],original_position-1))+1
            start=max(start,segment['old'][0])
            end=raw.find('\n',original_position,segment['old'][1])
            end=segment['old'][1] if end<0 else end+1
            while raw.count(raw[start:end])!=1:
                if start>segment['old'][0]:start=max(segment['old'][0],raw.rfind('\n',segment['old'][0],start-1)+1)
                elif end<segment['old'][1]:
                    nxt=raw.find('\n',end,segment['old'][1]);end=segment['old'][1] if nxt<0 else nxt+1
                else:raise RuntimeError('Could not create unique original anchor: '+note['id'])
            old=raw[start:end];offset=original_position-start
            edit_id='citation.'+note['id']
            ledgers[addition_path].append(dict(id=edit_id,source=source_by_module[note['module']],
                start_line=raw[:start].count('\n')+1,
                end_line=raw[:end].count('\n')+(not old.endswith('\n')),
                old=old,new=old[:offset]+note['text']+old[offset:],lean_exports=[],
                reason='Bibliographic attribution/comparison only; mathematical text and proof exports unchanged.',
                kind='bibliographic_attribution',attribution_insertions=[note['id']]))
        changes.append(dict(id=note['id'],module=note['module'],edit_id=edit_id,source_ids=note['source_ids']))
    replacements=read(AUTH/'editorial_replacements.json')
    for change in replacements:
        path=REPO/source_by_module[change['module']];raw=path.read_text()
        own=[e for es in ledgers.values() for e in es if e['source']==source_by_module[change['module']]]
        corrected,mapping=builder.edited_source(raw,own)
        assert corrected.count(change['old'])==1,change['id']
        a=corrected.index(change['old']);b=a+len(change['old'])
        segment=next(m for m in mapping if m['new'][0]<=a and b<=m['new'][1])
        if segment['edit']:
            e=next(e for e in own if e['id']==segment['edit'])
            assert e['new'].count(change['old'])==1
            e['new']=e['new'].replace(change['old'],change['new'],1)
            e.setdefault('attribution_wording_revisions',[]).append(change['id'])
        else:
            start=segment['old'][0]+a-segment['new'][0];end=start+len(change['old'])
            old=raw[start:end];assert old==change['old'] and raw.count(old)==1
            ledgers[addition_path].append(dict(id='citation.'+change['id'],source=source_by_module[change['module']],
                start_line=raw[:start].count('\n')+1,end_line=raw[:end].count('\n')+(not old.endswith('\n')),
                old=old,new=change['new'],lean_exports=[],reason=change['reason'],kind='bibliographic_wording',
                attribution_wording_revisions=[change['id']]))
    for m in mods:
        path=REPO/m['source'];own=[e for es in ledgers.values() for e in es if e['source']==m['source']]
        corrected,_=builder.edited_source(path.read_text(),own)
        stripped=corrected
        for note in notes:
            if note['module']==m['module']:
                assert stripped.count(note['text'])==1,note['id'];stripped=stripped.replace(note['text'],'',1)
        for change in replacements:
            if change['module']==m['module']:
                assert stripped.count(change['new'])==1,change['id']
                stripped=stripped.replace(change['new'],change['old'],1)
        previous=old_text(commit,HERE/'latex/chapters'/path.name)
        assert stripped==previous,('Mathematical text changed',m['module'])
    for p,rows in ledgers.items():
        text=json.dumps(rows,indent=2,ensure_ascii=False)+'\n'
        if not p.exists() or p.read_text()!=text:p.write_text(text)
    (AUTH/'APPLIED.json').write_text(json.dumps(dict(baseline_commit=commit,notes=changes,
        editorial_wording_replacements=replacements,
        chapter_text_unchanged_after_reverting_attribution_revision=True),indent=2)+'\n')
    print('Applied',len(notes),'citation notes; reverting notes and five novelty-wording edits recovers all 14 prior chapters exactly.')

if __name__=='__main__':main()
