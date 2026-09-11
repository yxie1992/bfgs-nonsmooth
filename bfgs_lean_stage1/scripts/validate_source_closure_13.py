#!/usr/bin/env python3
"""Validate the frozen thirteenth release and its actual reviewed evidence."""
import datetime as dt
import hashlib
import json
import subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent
def command(args,cwd=ROOT):
    return subprocess.check_output(args,cwd=cwd).decode().strip()
s=json.loads((ROOT/'audit/STATUS.json').read_text())
assert s['status']=='MODULE_M_AND_REPORT_SOURCE_CLOSURE_TARGETS_VERIFIED'
assert len(s['verified_declarations'])==4291 and s['audited_declaration_count']==6264
assert not s['unexpected_axioms'] and not s['missing_axiom_reports'] and not s['remaining_target_obligations']
hashes=json.loads((ROOT/'audit/report_source_closure_source_hashes.json').read_text())
assert len(hashes)==543
for f,h in hashes.items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,f
packages=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
assert len(packages)==9
for p in packages:
    at=ROOT/'.lake/packages'/p['name']
    assert command(['git','rev-parse','HEAD'],at)==p['rev'],p['name']
    assert not command(['git','status','--porcelain'],at),p['name']
original=command(['git','ls-tree','-r','--name-only','2c8bb60'],REPO).splitlines()
original=[f for f in original if not f.startswith('bfgs_lean_stage1/')]
assert len(original)==22
for f in original:
    old=subprocess.check_output(['git','show','2c8bb60:'+f],cwd=REPO)
    assert (REPO/f).read_bytes()==old,f
for name in ['l_identity','tf_source_details','c_all_endpoints','l_stable_manifold',
             'a_univariate_cells','a_polynomial_simple_root']:
    output=command(['python3','audit/validate_'+name+'.py'])
    assert 'PASS' in output,name
for file in ['L_IDENTITY_PEER_REVIEW.md','WHITENING_PEER_REVIEW.md',
             'TF_SOURCE_DETAILS_INDEPENDENT_REVIEW.md','C_ALL_ENDPOINTS_INDEPENDENT_PEER_REVIEW.md',
             'L_STABLE_MANIFOLD_PEER_REVIEW.md','UNIVARIATE_CELLS_PEER_REVIEW.md',
             'POLYNOMIAL_SIMPLE_ROOT_PEER_REVIEW.md','REPORT_SOURCE_CLOSURE_STATEMENT_REVIEW.md']:
    assert (ROOT/'audit'/file).is_file(),file
r=json.loads((ROOT/'audit/REPORT_STATUS.json').read_text())
assert not r['entire_report_verified']
assert next(m for m in r['milestones'] if m['id']=='report_source_closure_13')['exact_targets']==162
print(dt.datetime.now(dt.timezone.utc).isoformat())
print('PASS: full pinned audit,4291 explicit/6264 total/162 exact targets; all543 frozen Lean hashes unchanged;9 exact clean dependencies;22 original research artifacts unchanged versus2c8bb60.')
print('PASS: all six delivered scoped compiler/type/axiom validators and all independent reviews present; no missing or unexpected axioms/targets. General A geometry, higher-dimensional C and final source reconciliation remain explicit; entire_report_verified=false.')
