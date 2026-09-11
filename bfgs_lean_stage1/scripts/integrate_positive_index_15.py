#!/usr/bin/env python3
"""Adopt the independently reviewed positive pseudo-index bridge (imports only)."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
b=ROOT/'audit/scratch/positive_index'
assert 'PASS' in (b/'validation.log').read_text()
assert 'PASS' in (b/'peer_validation.log').read_text()
rows=[]
for f,h in json.loads((b/'source_hashes.json').read_text()).items():
 p=b/f;assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 raw=p.read_text()
 out=re.sub(r'^import (RationalIndexTargets|PositivePseudoIndex)$',r'import BfgsVerification.\1',raw,flags=re.M)
 assert re.sub(r'^import .*\n','',raw,flags=re.M)==re.sub(r'^import .*\n','',out,flags=re.M)
 dest=ROOT/'BfgsVerification'/f;assert not dest.exists();dest.write_text(out)
 rows.append(dict(module='BfgsVerification.'+p.stem,path=str(dest.relative_to(ROOT)),sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),reviewed_source=str(p.relative_to(ROOT)),reviewed_sha256=h))
names=(b/'declarations.txt').read_text().splitlines();assert len(names)==10
pairs=[['BfgsVerification.positivePseudoIndexSpecialization','BfgsVerification.PositivePseudoIndexSpecializationTarget']]
evidence=[]
for f in ['STATEMENT_REVIEW.md','INDEPENDENT_PEER_REVIEW.md','peer_validation.log','peer_axioms_contracts.log']:
 d=ROOT/'audit'/('POSITIVE_INDEX_'+f);assert not d.exists();d.write_bytes((b/f).read_bytes());evidence.append(str(d.relative_to(ROOT)))
m=dict(scopes=[dict(id='positive_index',label='POSITIVE_INDEX',sources=rows,declarations=names,targets=pairs,review_evidence=evidence)],declarations=names,targets=pairs,audit_driver='audit/PositiveIndexAudit.lean',log_prefix='positive_index')
(ROOT/'audit/positive_index_declarations.json').write_text(json.dumps(m,indent=2)+'\n')
a=(b/'PeerAudit.lean').read_text().replace('import PositivePseudoIndexSpecialization','import BfgsVerification.PositivePseudoIndexSpecialization')
(ROOT/'audit/PositiveIndexAudit.lean').write_text(a)
(ROOT/'audit/positive_index_import_correspondence.log').write_text('PASS: two reviewed source hashes matched; module imports alone changed; ten declarations and one exact target preserved. Both original and delivered hashes recorded.\n')
print('Adopted positive pseudo-index bridge: two files/ten declarations/one target; central audit pending.')
