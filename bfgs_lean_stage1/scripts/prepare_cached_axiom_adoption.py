#!/usr/bin/env python3
"""Prepare a candidate only. Root separately adopts it after reviewing provenance."""
from pathlib import Path
import json,runpy
from validate_cached_axiom_audit import ROOT,BASE,MARKER,sha,checked_scope18,check_static
check_static()
scope=checked_scope18()
original=(BASE/'OriginalAudit17.lean.txt').read_bytes()
reviewed=(BASE/'ReviewedProposedAudit17.lean.txt').read_bytes()
current=(ROOT/'Audit.lean').read_bytes()
old_prefix=original[:original.index(MARKER)]
assert current.startswith(old_prefix),'ordinary first loop changed;do not overwrite'
tail=current[current.index(MARKER):]
assert tail.startswith(original[original.index(MARKER):]),'original tail was changed'
for declaration,target in scope['targets']:
 for line in [f'#print {target}',f'example : {target} := {declaration}',f'#print axioms {declaration}']:
  assert ('\n'+line+'\n').encode() in tail,line
config=runpy.run_path(str(ROOT/'scripts/check.py'))
assert len(config['ALL_TARGETS'])==251,'register the18 targets before preparing prefix adoption'
prefix=reviewed[:reviewed.index(MARKER)]
candidate=prefix+tail
record={'before_sha256':sha(current),'candidate_sha256':sha(candidate),
 'preserved_tail_sha256':sha(tail),'preserved_tail_bytes':len(tail),
 'reviewed_cached_prefix_sha256':sha(prefix),'registered_targets':251,
 'main_audit_modified_by_preparation':False}
for filename,data in [('OriginalAuditBeforeCache.lean.txt',current),('ProposedCurrentAudit.lean',candidate),('adoption_provenance.json',(json.dumps(record,indent=2)+'\n').encode())]:
 path=BASE/filename
 assert not path.exists() or path.read_bytes()==data,('conflicting preparation evidence',filename)
 path.write_bytes(data)
print('PASS:candidate prepared with reviewed cached prefix and whole current251-target tail byte-preserved;main Audit unchanged.')
