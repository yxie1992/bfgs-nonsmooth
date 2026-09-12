#!/usr/bin/env python3
"""Reject failed or unresolved document builds; retain warning details for review."""
from pathlib import Path
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[1]
results=[]
for name in ['paper','companion']:
 pdf=ROOT/name/'build/master.pdf';log=ROOT/name/'build/master.log'
 assert pdf.is_file() and log.is_file(),name
 text=log.read_text(errors='replace')
 errors=[line for line in text.splitlines() if re.search(r'undefined|multiply defined|^! |Fatal error|Emergency stop',line,re.I)]
 info=subprocess.check_output(['pdfinfo',str(pdf)],text=True)
 pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1])
 overfull=re.findall(r'Overfull \\[hv]box.*',text)
 results.append({'document':name,'pdf':str(pdf.relative_to(ROOT)),'pages':pages,'sha256':hashlib.sha256(pdf.read_bytes()).hexdigest(),'errors':errors,'overfull_warnings':overfull})
out={'status':'PASS' if all(not x['errors'] for x in results) else 'FAIL','scope':'Compilation, references and PDF metadata; visual and mathematical reviews are separate','documents':results}
(ROOT/'editorial/logs/document_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
assert out['status']=='PASS'
