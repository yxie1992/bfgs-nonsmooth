#!/usr/bin/env python3
"""Read actual final public documents; preserve all files and mutable run logs."""
from pathlib import Path
import ast,datetime,hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;ROOT=P.parents[2];REPO=ROOT.parent
BASE='19c76918cb790c311157c85777aa24a76f185b05'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
r=read(ROOT/'audit/REPORT_STATUS.json');s=read(ROOT/'audit/STATUS.json');rows=read(ROOT/'audit/declarations.json');inventory={x['theorem']:x for x in rows}
assert s['status']=='MODULE_M_AND_REPORT_RECONSTRUCTION_TARGETS_VERIFIED'
assert len(s['verified_declarations'])==s['explicit_theorem_declarations']==5195
assert len(rows)==len(inventory)==s['audited_declaration_count']==7813
assert not s['unexpected_axioms'] and not s['remaining_target_obligations'] and not s['missing_axiom_reports']
assert r['schema_version']==2
assert not r['entire_report_verified'] and not r['original_snapshot_all_assertions_verified']
for key in ['corrected_report_mathematics_verified','reconstructed_execution_evidence_verified','corrected_source_reconciliation_verified','corrected_report_verified']:assert r[key] is True
old=json.loads(subprocess.check_output(['git','show',BASE+':bfgs_lean_stage1/audit/REPORT_STATUS.json'],cwd=REPO))
assert len(r['modules'])==len(old['modules'])==14
nspans=nlines=0
for a,b in zip(old['modules'],r['modules']):
 assert a['module']==b['module'] and a['source_sha256']==b['source_sha256']
 assert b['previous_snapshot_status']==a['status'] and b['previous_snapshot_remaining_claims']==a['remaining_claims']
 assert not b['remaining_claims'] and b['corrected_retained_mathematics_verified'] is True
 source=REPO/b['source'];assert sha(source)==b['source_sha256']
 n=len(source.read_text().splitlines());nlines+=n;spans=b['coverage_spans'];nspans+=len(spans)
 assert [i for row in spans for i in range(row['start_line'],row['end_line']+1)]==list(range(1,n+1))
 assert len(a['coverage_spans'])==len(spans)
 for x,y in zip(a['coverage_spans'],spans):
  for key in ['id','start_line','end_line','anchor','labels']:assert x[key]==y[key]
  assert set(x.get('verified_exports',[]))<=set(y.get('verified_exports',[]))<=inventory.keys()
  assert y['claim_review']!='pending'
assert (nspans,nlines)==(172,4323)
corrections={x['id']:x for x in r['mathematical_corrections']};assert len(corrections)==11 and len(old['mathematical_corrections'])==9
for x in old['mathematical_corrections']:
 assert (corrections[x['id']]['previous_record'] if x['id']=='R.historical_four_piece_attribution' else corrections[x['id']])==x
assert corrections['R.historical_four_piece_attribution']['reconstruction_exports']==['BfgsVerification.reconstructedFourPieceFailure','BfgsVerification.reconstructedSupportingPlane']
E=next(m for m in r['modules'] if m['module']=='E');jobs=read(ROOT/'verification/reconstructed/jobs.json')['jobs']
mapped=[]
for row in E['coverage_spans']:
 for label in row.get('reconstructed_jobs',[]):
  j=next(j for j in jobs if j['job']==label);assert row['start_line']<=j['source_lines'][0]<=j['source_lines'][1]<=row['end_line'];mapped.append(label)
assert len(mapped)==len(set(mapped))==len(jobs)==19
assert sum(len(j['checks']) for j in jobs)==107
assert len({c['theorem'] for j in jobs for c in j['checks']})==93
assert all(c['theorem'] in inventory for j in jobs for c in j['checks'])
summary=read(ROOT/'verification/reconstructed/fresh/SUMMARY.json')
assert summary['status']=='PASS' and summary['actual_check_occurrences']==107 and summary['distinct_theorems_checked']==93
companion=ROOT/'CORRECTED_REPORT.md';assert sha(companion)==r['verification_scope']['companion_sha256']
text=companion.read_text();assert 'Draft release status' not in text
for exact in ['5,195 explicit theorems','7,813 total theorem declarations','all 255','737 frozen','107 strict literal','93 distinct','0<c1≤1/3','c1<c2<1','\\delta=c-16d-1>0','0,0,25/4','C-planar-numerical','U-multidimensional-numerical','G-oscillatory-numerical']:
 assert exact in text,exact
assert 'do not verify those original historical assertions' in text
for rel,h in read(ROOT/'audit/report_reconstruction_source_hashes.json').items():assert sha(ROOT/rel)==h,rel
main_docs=['CORRECTED_REPORT.md','README.md','MATHEMATICAL_REVIEW.md','PROOF_OBLIGATIONS.md','ENTIRE_REPORT_PLAN.md','audit/REPORT_VERIFICATION_OVERVIEW.md','audit/REPORT_RECONSTRUCTION_STATEMENT_REVIEW.md']
# Closing review/log links are completed by root after copying the reviewed files.
pending={'audit/REPORT_RECONSTRUCTION_FINAL_INDEPENDENT_REVIEW.md','audit/report_reconstruction_documentation_validation.log'}
checked=0
for rel in main_docs:
 doc=ROOT/rel
 for link in re.findall(r'\[[^\]]*\]\(([^)]+)\)',doc.read_text()):
  if '://' in link or link.startswith('#'):continue
  target=(doc.parent/link.split('#')[0]).resolve()
  if not target.exists():assert str(target.relative_to(ROOT)) in pending,(rel,link)
  checked+=1
for rel in ['MATHEMATICAL_REVIEW.md','PROOF_OBLIGATIONS.md','ENTIRE_REPORT_PLAN.md']:
 assert 'milestones 1–18 below are historical snapshots' in (ROOT/rel).read_text()
assert "Q's calibrated transport and full convergence theorem were subsequently proved." in (ROOT/'README.md').read_text()
assert 'new explicit R objective now has its' in (ROOT/'README.md').read_text()
msg=datetime.datetime.now(datetime.timezone.utc).isoformat()+f'\nPASS:actual5195/7813/255/737 status;14modules172spans4323lines;9inheritedcorrections+2explicitnewentries;allprevioussourceexports retained;19jobs107checks93theorems;correctedtrue/originalfalse;companion hypotheses and currentdocfreshness;{checked} navigation links checked with only two closing-evidence links pending root finalization.\n'
(P/'actual_document_validation.log').write_text(msg);print(msg)
