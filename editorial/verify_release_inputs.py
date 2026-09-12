#!/usr/bin/env python3
"""Read-only final source, contract, build and audit integrity gate."""
from pathlib import Path
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[1]
def read(p):return json.loads((ROOT/p).read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
results=[]
def record(name,condition,details=None):
 results.append({'check':name,'status':'PASS' if condition else 'FAIL','details':details})
base=read('editorial/BASELINE.json')
changed=[p for p,h in base['files'].items() if sha(ROOT/p)!=h]
record('Original research, corrected edition and dependencies unchanged',not changed,changed)
inputs=read('editorial/formal_audit/runs/20260912_authoring/INPUTS.json')
changed=[]
for p,h in inputs.items():
 path=ROOT/'editorial/formal_audit'/p[7:] if p.startswith('@audit/') else ROOT/'bfgs_lean_stage1'/p
 if sha(path)!=h:changed.append(p)
record('Every input to the fresh main audit retains its hash',not changed,{'inputs':len(inputs),'changed':changed})
main=read('editorial/formal_audit/runs/20260912_authoring/SUMMARY.json')
record('Fresh pinned main and correction audit',main['status']=='PASS' and not main['changed_inputs'])
root=read('editorial/root_contract_review.json');supp=root['supplemental_audit']
changed=[p for p,h in supp['source_sha256'].items() if sha(ROOT/p)!=h]
record('Fresh article-only audit and its exact mathematical inputs',supp['status']=='PASS' and not changed and not supp['unchecked_missing_unsafe_partial'],{'module_owned_declarations':supp['module_owned_declarations'],'transitive_dependencies':supp['transitive_checked_declarations'],'changed':changed})
allowed={'propext','Classical.choice','Quot.sound'}
record('Article-only transitive axiom policy',set(supp['axioms'])<=allowed,supp['axioms'])
for file,key in [('positive_contract_review.json','article_sha256'),('negative_contract_review.json','article_file_sha256'),('root_contract_review.json','article_file_sha256')]:
 d=read('editorial/'+file);changed=[p for p,h in d[key].items() if sha(ROOT/p)!=h]
 record('Reviewed source contracts: '+file,not changed,changed)
ledger=read('editorial/CLAIM_LEDGER.json')
record('All named article statements mapped',not ledger['unmapped_named_article_statements'])
record('Complete companion source and export preservation',len(ledger['companion_source_span_records'])==172 and len({n for r in ledger['companion_source_span_records'] for n in r['full_formal_exports']})==3087)
record('Root mathematical deductions have no remaining obligations',not root['remaining_math_obligations'])
for d in read('editorial/logs/document_checks.json')['documents']:
 record(d['document']+' PDF matches successful resolved, overflow-free build',sha(ROOT/d['pdf'])==d['sha256'] and not d['errors'] and not d['overfull_warnings'],{'pages':d['pages'],'sha256':d['sha256']})
for p in [ROOT/'paper/sections',ROOT/'paper/appendices',ROOT/'paper/statements']:
 todo=[]
 for f in p.glob('*.tex'):
  if re.search(r'\b(TODO|TBD|FIXME|placeholder)\b',f.read_text()):todo.append(str(f.relative_to(ROOT)))
 record('No substantive authoring placeholders in '+p.name,not todo,todo)
out={'status':'PASS' if all(r['status']=='PASS' for r in results) else 'FAIL','scope':'Read-only release inputs; fresh compilation is evidenced by separate hashed logs. Page-level visual approval is recorded separately.','checks':results}
(ROOT/'editorial/logs/release_integrity.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2));assert out['status']=='PASS'
