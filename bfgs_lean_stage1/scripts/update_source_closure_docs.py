#!/usr/bin/env python3
"""Update current documentation after the thirteenth full pinned audit gate."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
s=json.loads((ROOT/'audit/STATUS.json').read_text())
assert s['status']=='MODULE_M_AND_REPORT_SOURCE_CLOSURE_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports'] and not s['remaining_target_obligations']
e=len(s['verified_declarations']);a=s['audited_declaration_count']
marker='## Thirteenth milestone: identity initialization and invariant stable manifold'
text=f'''\n\n{marker}\n\nThe frozen pinned build and full transitive axiom audit passed {e:,} explicit\ntheorems, {a:,} total theorem declarations including generated auxiliaries, and\n162 registered exact targets in 543 Lean files. Only propext, Classical.choice\nand Quot.sound occur. Evidence: audit/report_source_closure_check.log,\naudit/build.log, audit/axioms.log, audit/STATUS.json and the frozen source hashes.\n\nBoth actual L local failure families now use identity initialization for one\nfixed objective each, with all exact search histories, actual query derivatives,\nstrict Armijo/weak Wolfe, positive nonstationary limits and uniform query\nlocality. Actual transformed strong-convexity/Lipschitz/Hessian constants are\nderived from the fixed SPD square root. The actual L return map now has a\nsmooth embedded two-dimensional locally invariant stable manifold, with actual\nstable tangent space and positive physical scales. These are conclusions, not\nassumed orbit or spectral data.\n\nC's same constructed field satisfies all three uniform estimates for every\nsufficiently close eligible endpoint pair. A's literal rank-loss Hessian spectrum,\ngenuine univariate cells and actual arbitrary-degree simple-root local charts\nare checked. T/F source details are closed; G is covered with its explicitly\ndocumented accessible/active-span correction and actual objective counterexample.\nSee audit/REPORT_SOURCE_CLOSURE_STATEMENT_REVIEW.md and its linked independent\nreviews and delivered-only reproduction scripts.\n\nThe entire report remains incomplete. A still needs general nonlinear\nsemialgebraic projection and finite smooth-path decomposition/application; C\nstill needs its arbitrary-dimensional constant-rank field/secant partial\nconstruction and A-dependent alternative. Final numerical-display, historical\nsource, synthesis and evidence reconciliation remain active. Original sources\nare preserved, including every disputed claim and documented correction.\n'''
for name in ['ENTIRE_REPORT_PLAN.md','MATHEMATICAL_REVIEW.md','PROOF_OBLIGATIONS.md']:
    p=ROOT/name;old=p.read_text();assert marker not in old,name;p.write_text(old+text)
p=ROOT/'README.md';old=p.read_text()
old=old.replace('all 4,039 explicit\ntheorems and 5,852 theorem declarations including generated auxiliaries. All 145',
                f'all {e:,} explicit\ntheorems and {a:,} theorem declarations including generated auxiliaries. All 162')
old=old.replace('audit/report_l_failure_check.log','audit/report_source_closure_check.log',1)
old=old.replace("L's fixed identity initialization and smooth-manifold/tangency, A's general\nsemialgebraic closure, C's remaining uniform/higher-dimensional assertions, and\nfinal source reconciliation remain open.",
'''The thirteenth tranche verifies both actual identity-initialized local failure\nfamilies, the actual smooth locally invariant stable manifold, C's uniform\nsame-field endpoint estimates, A's rank-loss spectrum and local semialgebraic\ninfrastructure, and T/F source details. See\n[audit/REPORT_SOURCE_CLOSURE_STATEMENT_REVIEW.md](audit/REPORT_SOURCE_CLOSURE_STATEMENT_REVIEW.md).\nA's general semialgebraic closure, C's higher-dimensional partial field/secant\nassertion and A-dependent alternative, and final source/evidence reconciliation\nremain open.''')
p.write_text(old)
for tag,review,state in [('T','TF_SOURCE_DETAILS_STATEMENT_REVIEW.md','verified'),
                         ('F','TF_SOURCE_DETAILS_STATEMENT_REVIEW.md','verified with the documented line-search proof replacement'),
                         ('G','G_SOURCE_CLOSURE_REVIEW.md','verified with the documented accessible/active-span correction')]:
    p=ROOT/f'audit/module_{tag}_inventory.md';old=p.read_text()
    current=f'''Current source reconciliation at milestone13: **{state}**.\nSee [{review}]({review}) and REPORT_STATUS.json for the authoritative\nline-by-line coverage. The chronological entries below preserve earlier\nobligations and must not be read as current pending status.\n\n'''
    assert not old.startswith('Current source reconciliation'),tag
    p.write_text(current+old)
print(f'Thirteenth documentation updated: {e} explicit/{a} total/162 exact targets.')
