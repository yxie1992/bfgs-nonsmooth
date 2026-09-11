#!/usr/bin/env python3
"""Generate ordinary Lean CollectAxioms audit from its frozen prefix and current tail.

--run invokes the slower ordinary collector without modifying main Audit/checker.
Source scripts/env.sh before requesting execution,or invoke through lake's shell.
"""
from pathlib import Path
import argparse,json,subprocess
from validate_cached_axiom_audit import ROOT,BASE,MARKER,sha,check_static,index,same_items
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--run',action='store_true')
args=parser.parse_args()
check_static()
original=(BASE/'OriginalAudit17.lean.txt').read_bytes()
actual=(ROOT/'Audit.lean').read_bytes()
tail=actual[actual.index(MARKER):]
ordinary=original[:original.index(MARKER)]+tail
output=BASE/'OrdinaryCurrentAudit.lean'
output.write_bytes(ordinary)
(BASE/'ordinary_current_provenance.json').write_text(json.dumps({
 'ordinary_prefix_source_sha256':sha(original),'current_main_audit_sha256':sha(actual),
 'preserved_current_tail_sha256':sha(tail),'ordinary_current_sha256':sha(ordinary),
 'main_audit_modified':False},indent=2)+'\n')
print('Prepared ordinary Lean4.19 collector with every current audit-tail check unchanged.')
if args.run:
 with (BASE/'ordinary_current_audit.log').open('w') as log:
  subprocess.run(['lake','env','lean',str(output.relative_to(ROOT))],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
 text=(BASE/'ordinary_current_audit.log').read_text()
 assert 'error:' not in text
 items=[json.loads(l[len('BFGS_AUDIT '):]) for l in text.splitlines() if l.startswith('BFGS_AUDIT ')]
 ordinary_items=index(items)
 cached={n:x for n,x in index(json.loads((BASE/'current_cached_reports.json').read_text())).items() if x['isTheorem']}
 assert set(ordinary_items)==set(cached)
 same_items(ordinary_items,cached)
 (BASE/'ordinary_current_declarations.json').write_text(json.dumps(items,indent=2)+'\n')
 (BASE/'ordinary_current_validation.log').write_text(f'PASS:all{len(items)} actual ordinary-current theorem types and axiom sets match cached-current;current audit tail preserved;main Audit unchanged.\n')
 print((BASE/'ordinary_current_validation.log').read_text(),end='')
