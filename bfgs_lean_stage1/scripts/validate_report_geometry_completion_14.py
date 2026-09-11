#!/usr/bin/env python3
"""Validate the frozen fourteenth central release and all scoped evidence."""
import datetime as dt,hashlib,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];REPO=ROOT.parent
def command(args,cwd=ROOT):return subprocess.check_output(args,cwd=cwd).decode().strip()
s=json.loads((ROOT/'audit/STATUS.json').read_text())
assert s['status']=='MODULE_M_AND_REPORT_GEOMETRY_COMPLETION_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports'] and not s['remaining_target_obligations']
hashes=json.loads((ROOT/'audit/report_geometry_completion_source_hashes.json').read_text());assert len(hashes)==582
for f,h in hashes.items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,f
packages=json.loads((ROOT/'lake-manifest.json').read_text())['packages'];assert len(packages)==9
for p in packages:
 at=ROOT/'.lake/packages'/p['name'];assert command(['git','rev-parse','HEAD'],at)==p['rev'],p['name'];assert not command(['git','status','--porcelain'],at),p['name']
original=[f for f in command(['git','ls-tree','-r','--name-only','2c8bb60'],REPO).splitlines() if not f.startswith('bfgs_lean_stage1/')];assert len(original)==22
for f in original:assert (REPO/f).read_bytes()==subprocess.check_output(['git','show','2c8bb60:'+f],cwd=REPO),f
for name in ['two_piece','c_constant_rank','l_shape_precision','a_polynomial_multiplicity','a_quadratic_projection','a_polynomial_pseudodivision']:
 assert 'PASS' in command(['python3','audit/validate_'+name+'.py']),name
for f in ['TWO_PIECE_TERMINATION_INDEPENDENT_REVIEW.md','C_CONSTANT_RANK_INDEPENDENT_PEER_REVIEW.md','L_SHAPE_PRECISION_PEER_REVIEW.md','A_POLYNOMIAL_MULTIPLICITY_PEER_REVIEW.md','A_QUADRATIC_PROJECTION_PEER_REVIEW.md','A_POLYNOMIAL_PSEUDODIVISION_PEER_REVIEW.md','REPORT_GEOMETRY_COMPLETION_STATEMENT_REVIEW.md']:
 assert (ROOT/'audit'/f).is_file(),f
r=json.loads((ROOT/'audit/REPORT_STATUS.json').read_text());assert not r['entire_report_verified']
m=next(m for m in r['milestones'] if m['id']=='report_geometry_completion_14');assert m['exact_targets']==178
print(dt.datetime.now(dt.timezone.utc).isoformat())
print(f'PASS: full pinned central audit,{len(s["verified_declarations"])} explicit/{s["audited_declaration_count"]} total/178 exact targets;582 frozen Lean hashes;9 exact clean dependencies;22 original research artifacts unchanged against2c8bb60.')
print('PASS: six delivered-only scoped type/axiom/contract/source validators and all independent reviews; entire_report_verified=false; general semialgebraic elimination/path/application and final source closure remain explicit.')
