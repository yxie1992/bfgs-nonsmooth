#!/usr/bin/env python3
"""Inventory literal source evidence paths; do not claim historical executions."""
import datetime,hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];REPO=ROOT.parent;PACKAGE=REPO/'BFGS_MASTER_REPORT_LaTeX';SOURCE=PACKAGE/'report'
rows=[]
for f in sorted(SOURCE.rglob('*.tex')):
 for line,text in enumerate(f.read_text().splitlines(),1):
  for ref in re.findall(r'\\path\{([^}]+)\}',text):
   if not any(w in ref for w in ['verification','provenance','report/tools','report/EDIT']):continue
   candidates=[REPO/ref,PACKAGE/ref,SOURCE/ref]
   rows.append(dict(source=str(f.relative_to(REPO)),line=line,reference=ref,
    candidate_paths=[str(p.relative_to(REPO)) for p in candidates],
    existing_candidates=[str(p.relative_to(REPO)) for p in candidates if p.exists()]))
files=[x for x in subprocess.check_output(['git','ls-tree','-r','--name-only','2c8bb60'],cwd=REPO).decode().splitlines() if not x.startswith('bfgs_lean_stage1/')]
original={f:hashlib.sha256((REPO/f).read_bytes()).hexdigest() for f in files}
assert len(files)==22
for f in files:assert (REPO/f).read_bytes()==subprocess.check_output(['git','show','2c8bb60:'+f],cwd=REPO),f
out=dict(date_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),original_research_artifacts=original,
 references=rows,historical_execution_reproduced=False,
 warning='File presence audit only. Missing original inputs/logs prevent checking the claimed September10 historical commands, timings, counts and PASS outcomes. No reconstructed job is represented as that historical execution.')
(ROOT/'audit/historical_evidence_presence.json').write_text(json.dumps(out,indent=2)+'\n')
print(f'PASS:22 original research artifacts preserved; inventoried{len(rows)} literal archival/evidence references.')
print(f'{sum(bool(r["existing_candidates"]) for r in rows)} references have an existing candidate; historical executions were not rerun or verified.')
