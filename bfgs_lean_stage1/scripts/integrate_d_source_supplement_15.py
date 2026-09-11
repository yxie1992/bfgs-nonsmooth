#!/usr/bin/env python3
"""Adopt the reviewed six-file D source supplement, preserving proof bodies."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1];b=ROOT/'audit/scratch/d_source_closure'
assert 'PASS' in (b/'validation.log').read_text()
assert 'PASS' in (b/'peer_validation.log').read_text()
hashes=json.loads((b/'source_hashes.json').read_text());modules={Path(f).stem for f in hashes}
def normalize(s):
 return re.sub(r'^import ([A-Za-z0-9_]+)$',lambda m:'import BfgsVerification.'+m[1] if m[1] in modules else m[0],s,flags=re.M)
rows=[]
for f,h in hashes.items():
 p=b/f;assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 raw=p.read_text();out=normalize(raw)
 assert re.sub(r'^import .*\n','',raw,flags=re.M)==re.sub(r'^import .*\n','',out,flags=re.M)
 d=ROOT/'BfgsVerification'/f;assert not d.exists();d.write_text(out)
 rows.append(dict(module='BfgsVerification.'+p.stem,path=str(d.relative_to(ROOT)),sha256=hashlib.sha256(d.read_bytes()).hexdigest(),reviewed_source=str(p.relative_to(ROOT)),reviewed_sha256=h))
names=json.loads((b/'declarations.json').read_text());assert len(names)==97
pairs=[['BfgsVerification.'+ns+'.'+th,'BfgsVerification.'+ns+'.'+ta] for ns,th,ta in json.loads((b/'targets.json').read_text())]
assert len(pairs)==3
evidence=[]
for f in ['STATEMENT_REVIEW.md','INDEPENDENT_PEER_REVIEW.md','peer_validation.log','peer_axioms_contracts.log','peer_regeneration.log']:
 d=ROOT/'audit'/('D_SOURCE_SUPPLEMENT_'+f);assert not d.exists();d.write_bytes((b/f).read_bytes());evidence.append(str(d.relative_to(ROOT)))
m=dict(scopes=[dict(id='d_source_closure',label='D_SOURCE_SUPPLEMENT',sources=rows,declarations=names,targets=pairs,review_evidence=evidence)],declarations=names,targets=pairs,audit_driver='audit/DSourceSupplementAudit.lean',log_prefix='d_source_supplement')
(ROOT/'audit/d_source_supplement_declarations.json').write_text(json.dumps(m,indent=2)+'\n')
(ROOT/'audit/DSourceSupplementAudit.lean').write_text(normalize((b/'PeerAudit.lean').read_text()))
# Candidate reproduction writes/checks delivered paths and qualifies imports only.
gen=(b/'generate_d_displays.py').read_text().replace('import json,sys','import json,sys,re')
gen=gen.replace('def write_or_check(path,content):\n', '''def write_or_check(path,content):
 if path.suffix=='.lean':
  path=HERE.parent/'BfgsVerification'/path.name
  content=re.sub(r'^import (DDisplayRaw)$',r'import BfgsVerification.\\1',content,flags=re.M)
 if path.name=='display_candidates.json':path=HERE/'d_display_candidates.json'
''')
(ROOT/'audit/generate_d_displays.py').write_text(gen)
(ROOT/'audit/generate_d_auxiliary.py').write_bytes((b/'generate_auxiliary.py').read_bytes())
(ROOT/'audit/d_display_candidates.json').write_bytes((b/'display_candidates.json').read_bytes())
gen=(b/'generate_source_map.py').read_text()
gen=gen.replace('P=Path(__file__).resolve().parent; PROJECT=P.parents[2]','P=Path(__file__).resolve().parent; PROJECT=P.parent')
gen=gen.replace("(P/'source_map.json')","(P/'d_source_map.json')").replace("(P/'SOURCE_MAP.md')","(P/'D_SOURCE_MAP.md')")
gen=gen.replace('Module D complete source reconciliation (scratch)','Module D complete source reconciliation')
gen=gen.replace('STATEMENT_REVIEW.md','D_SOURCE_SUPPLEMENT_STATEMENT_REVIEW.md')
(ROOT/'audit/generate_d_source_map.py').write_text(gen)
(ROOT/'audit/d_source_supplement_import_correspondence.log').write_text('PASS: six reviewed source hashes match; only module imports changed; 97 declarations and three targets preserved. Candidate generators changed output paths/import qualification only; main regeneration is checked separately.\n')
print('Adopted D supplement: six files/97 declarations/three targets; central audit pending.')
