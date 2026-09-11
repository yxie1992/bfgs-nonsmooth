#!/usr/bin/env python3
"""Update the source register only after the frozen sixteenth full gate passes."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
s=json.loads((ROOT/'audit/STATUS.json').read_text())
assert s['status']=='MODULE_M_AND_REPORT_TAME_GEOMETRY_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports'] and not s['remaining_target_obligations']
hashes=json.loads((ROOT/'audit/report_tame_geometry_source_hashes.json').read_text())
assert len(hashes)==693
for f,h in hashes.items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,f
p=ROOT/'audit/REPORT_STATUS.json';r=json.loads(p.read_text())
assert not any(m['id']=='report_tame_geometry_16' for m in r['milestones'])
mods={m['module']:m for m in r['modules']}
review='audit/REPORT_TAME_GEOMETRY_STATEMENT_REVIEW.md'
def exports(files):
 out=[]
 for f in files:
  found=[d['theorem'] for d in s['verified_declarations'] if d['source'].endswith('/'+f+'.lean')]
  assert found,f
  out+=found
 return sorted(set(out))
def span(tag,i,state,files,note):
 row=next(x for x in mods[tag]['coverage_spans'] if x['id']==f'{tag}.span.{i}')
 row.update(claim_review=state,review_note=note)
 row.pop('verification_note',None)
 row['verified_exports']=sorted(set(row.get('verified_exports',[])+exports(files)))
mods['A'].update(status='actual_finite_components_critical_values_and_low_gap_verified_literal_semialgebraic_paths_pending',
 statement_review=review+'; audit/CRITICAL_GEOMETRY_ACTUAL_CRITICAL_INDEPENDENT_PEER_REVIEW.md',
 remaining_claims="Only A69-75's literal assertions about semialgebraic witnessing path graphs and general continuous-semialgebraic composition piecewise-C1 regularity remain. Actual ordinary components, finite critical values and the original low-gap proposition are proved with no geometric closure premises.")
span('A',4,'reviewed_actual_finite_components_values_and_original_low_gap_audited_literal_path_graph_ingredient_pending',
 ['SemialgebraicCriticalGeometry','SemialgebraicCriticalTargets','SemialgebraicSmoothCover','SemialgebraicSmoothComponents'],
 'Actual root analysis, finite boundary-sign refinements and dimension induction construct the required finite smooth cover of genuine semialgebraic sets. Applied to the actual lifted critical graph this proves actual finite values, ordinary-component finiteness/semialgebraicity/constancy and the original low gap in all finite dimensions. No finite-cover/value/projection assumption remains. The stronger literal path-graph and general composition-regularity ingredients are tracked separately, not silently claimed.')
mods['C'].update(status='all_principal_and_tame_basin_conclusions_verified_literal_geometric_proof_refinement_tracked_in_A',
 statement_review=review+'; audit/CRITICAL_GEOMETRY_ACTUAL_CRITICAL_INDEPENDENT_PEER_REVIEW.md',
 remaining_claims='All stated BFGS convergence/basin conclusions, including the semialgebraic alternative, are proved with their original hypotheses. The source general path/composition proof ingredient is tracked in A; actual finite smooth-path classes are proved. The C2-to-C1 constant-rank qualification remains documented; higher-dimensional rotating-normal convergence remains explicitly unclaimed.')
span('C',12,'reviewed_actual_semialgebraic_finite_values_smooth_components_and_uniform_basin_conclusions_audited',
 ['SemialgebraicCriticalGeometry','SemialgebraicCriticalTargets','SemialgebraicSmoothComponents'],
 'Actual semialgebraic critical values give affine correctness below a positive threshold and the actual planar low/local basins. One threshold precedes every admissible run; strict contours and actual regular two-branch structure remain. No positive optimal multiplier, finite-value or assumed convergence premise is introduced. The literal general composition proof ingredient remains tracked in A.')
# Remove stale pre-calibration Q notes; their actual exports were audited earlier.
span('Q',3,'reviewed_claims_audited',[],
 'Actual original-family calibration, interface identity, uniform scale bounds and continuity are proved. Literal ordered pruning, strictly ordered breakpoints and adjacent calibration are also audited; see MODULE_Q_SOURCE_MAP and Q_FRESHNESS_REVIEW.')
next(x for x in mods['Q']['coverage_spans'] if x['id']=='Q.span.3')['scope_note']='Both the direct original-family construction and literal ordered-pruning specification are verified.'
span('Q',4,'reviewed_claims_audited',[],
 'Actual pair algebra and uniform visibility/secant bounds, including the calibrated theta scaling and complete actual BandCertificate, are audited.')
next(x for x in mods['Q']['coverage_spans'] if x['id']=='Q.span.7')['scope_note']='Literal printed field continuity/identification and its exact BandCertificate are verified. The stronger all-rho pair extension remains distinguished from the source printed c1<=2/3 range.'
mods['D'].update(status='all_retained_mathematical_claims_verified_with_documented_display_rounding_corrections',
 statement_review=review+'; audit/D_SOURCE_MAP.md; audit/D_LITERAL_CLOSURE_INDEPENDENT_PEER_REVIEW.md',remaining_claims=[])
for i,files,note in [
 (2,['DNonStrictObjectives','DLiteralTargets'],'Actual non-strict interpreter has the same full attempted-length lists and accepted lengths as the strict interpreter on every actual source run.'),
 (3,['DLiteralIdentities','DLiteralTargets'],'Literal polynomial equivalence holds both ways throughout the original closed box; actual three-gradient convex hull excludes zero. Exact seed and five nearest-rounding corrections retained.'),
 (4,['DLiteralIdentities'],'Actual update identities and whole-box positivity support the exact scalar-length iff.'),
 (5,['DNonStrictSearch','DNonStrictObjectives','DLiteralTargets'],'All actual strict and non-strict decisions are proved for every original allowed constant pair; no assigned oracle remains.'),
 (6,['DLiteralIdentities','DNonStrictObjectives'],'The literal positive weights 8/17,8/17,1/17 sum to one and give the actual constant affine branch combination. The coercive run also has identical non-strict search.'),
 (7,['DDisplayPrecision'],'The complete actual scalar construction and its derivative/asymptotic claims are audited, including the documented nearest-rounding corrections. All separately listed D literal wrappers are now closed.'),
 (9,['DNonStrictObjectives','DLiteralTargets'],'The actual embedded run has identical complete non-strict histories at every index and every source copy; all earlier Euclidean locality and infinite-tail bounds remain proved.')]:
 span('D',i,'reviewed_all_retained_literal_mathematical_claims_audited',files,note)
mods['I'].update(status='all_retained_current_mathematical_synthesis_verified_historical_source_exceptions_retained',
 remaining_claims='Historical execution/archive assertions remain unverified. All current mathematical synthesis implications, including A ordinary-component/finite-critical-value/low-gap assertions, are proved. The unidentified older R numerical attribution remains separately unresolved and is not silently retired.')
span('I',21,'reviewed_all_actual_geometric_synthesis_claims_audited',
 ['SemialgebraicCriticalGeometry','SemialgebraicCriticalTargets'],
 'Actual affine-critical set has finitely many ordinary connected components, each semialgebraic with constant actual objective. Actual finite critical values and the original low gap now follow with no geometric closure premise. Equal-rate, compact-gap and incoming-jump claims remain proved; no blanket BFGS result is inferred.')
mods['E']['remaining_claims']='Historical19-job outcomes, exact counts/timings/environment and original script/archive identities lack the referenced inputs. These particular facts remain unverified. Current actual mathematical proofs include general elimination, finite smooth covers, critical values, low gaps and C basins; the literal A semialgebraic-path proof ingredient remains separately active.'
span('E',24,'reviewed_current_analytic_audits_distinguished_from_historical_evidence',[],
 'The actual current compiled proofs supersede old draft status only for corresponding declarations. General elimination, actual finite smooth geometry/critical values/low gaps and C basins are now proved. Literal semialgebraic path-graph/composition assertions remain under separate audit. Rotating normals, positive-measure/floating-point robustness, rounded stable-manifold points and blanket convergence remain unclaimed.')
pairs=json.loads((ROOT/'audit/report_tame_geometry_targets.json').read_text());assert len(pairs)==28
e=len(s['verified_declarations']);a=s['audited_declaration_count']
r['milestones'].append(dict(id='report_tame_geometry_16',status='verified',targets=[t for _,t in pairs],
 audit='audit/STATUS.json',statement_review=review,explicit_theorems=e,audited_theorems=a,exact_targets=233,
 conditional_infrastructure=['Reusable finite graph-cover and finite-value bridges retain their explicit premises; actual semialgebraic applications discharge them.',
 'Literal semialgebraic path-graph/general composition assertions remain active.',
 'Historical execution records and the unidentified older R numerical objective remain unverified.']))
r['entire_report_verified']=False
p.write_text(json.dumps(r,indent=2)+'\n')
marker='## Sixteenth milestone: actual finite geometry, critical values and planar tame basins'
text=f'''\n\n{marker}

The frozen pinned build and transitive audit passed {e:,} explicit theorems,
{a:,} total theorem declarations, 233 exact targets and 693 frozen Lean files.
Only propext, Classical.choice and Quot.sound occur. Actual logs and frozen
hashes are report_tame_geometry_check.log, STATUS.json and their companions.

The actual arbitrary-dimensional semialgebraic finite smooth cover is proved
from polynomial root analysis and finite sign refinements. It yields actual
finite ordinary/smooth-path components, finite affine-critical values, the
original low gap and the planar tame convergence basins, without any assumed
geometric decomposition or convergence. D's literal non-strict search and
remaining finite-algebra identities also pass; all453 D lines are reconciled.

The stronger literal A assertions about semialgebraic path graphs and general
piecewise-C1 composition remain in a separate active proof scope. Historical E
jobs/counts/timings/archive identities and R's unidentified older four-piece
numerical claim remain unresolved. The latter is a mathematical attribution
exception, not merely execution history. No original claim is silently retired.
All original research sources are unchanged; the entire report flag is false.
'''
for name in ['ENTIRE_REPORT_PLAN.md','MATHEMATICAL_REVIEW.md','PROOF_OBLIGATIONS.md']:
 p=ROOT/name;old=p.read_text();assert marker not in old;p.write_text(old+text)
p=ROOT/'README.md';old=p.read_text()
old=old.replace('all 4,768 explicit\ntheorems and 7,134 theorem declarations including generated auxiliaries. All 205',
 f'all {e:,} explicit\ntheorems and {a:,} theorem declarations including generated auxiliaries. All 233')
old=old.replace('audit/report_algebra_completion_check.log','audit/report_tame_geometry_check.log',1)
old=old.replace("A's finite smooth-path/component/critical-value closure and dependent C alternative,\nD's last literal wrappers, and final source/evidence reconciliation remain open.",'''The sixteenth tranche proves actual finite smooth covers in arbitrary dimension,
finite ordinary and smooth-path components, finite critical values, the original
low gap, C's tame basins and D's last literal consequences. See
[audit/REPORT_TAME_GEOMETRY_STATEMENT_REVIEW.md](audit/REPORT_TAME_GEOMETRY_STATEMENT_REVIEW.md).
A's stronger literal semialgebraic-path/general-composition ingredient remains
active; historical execution/source-attribution exceptions remain unverified.''')
old=old.replace('remaining A/C path/value,\nD literal-export and historical-evidence obligations.','remaining literal A path/composition\nand historical/source-attribution obligations.')
p.write_text(old)
p=ROOT/'audit/I_SOURCE_RECONCILIATION.md';old=p.read_text()
old=old.replace('General semialgebraic support/critical definability is now proved, but finite components/constant values/low gap still require the active finite-path closure. This span remains mathematically partial.','Actual semialgebraic supporting/critical definability, finite ordinary components, constant critical values and the original low gap are now proved from the actual finite smooth cover. This mathematical synthesis span is complete; stronger literal path-graph facts in A remain separately tracked.')
old=old.replace('General A finite-value claims are not inferred\nfrom the now completed projection theorem alone.','General A finite-value claims now follow from the independently proved finite\nsmooth cover of the actual lifted critical graph, in addition to projection.')
p.write_text(old)
p=ROOT/'audit/HISTORICAL_EVIDENCE_RECONCILIATION.md';old=p.read_text()
old=old.replace('General semialgebraic elimination/path/application remains explicitly open in the current register.','General semialgebraic elimination, actual finite smooth covers, finite critical values, low gaps and C tame basins are now proved. The stronger literal A semialgebraic-path-graph/general composition ingredient remains separately active.')
p.write_text(old)
p=ROOT/'audit/R_FAMILY_COVERAGE_MAP.md';old=p.read_text()
old=old.replace('General-dimensional nuclear norm identification remains open.','The later six-file rectangular-nuclear tranche proves the actual arbitrary rectangular singular-value sum, variational identity, norm and centered/mixed convergence; see RECTANGULAR_NUCLEAR_STATEMENT_REVIEW.md.')
old=old.replace('A separately named first-difference matrix and literal centered/noncentered local scalar decomposition remain descriptive exports rather than missing basin premises.','The later rectangular-nuclear tranche also exports the named first-difference matrix and its literal fused/generalized-l1 local basin; the centered/noncentered scalar decomposition is explicit.')
old=old.replace('a general-dimensional nuclear norm remains distinct.','the later RectangularNuclear tranche also proves the distinct actual arbitrary rectangular nuclear norm and its centered/mixed convergence applications.')
p.write_text(old)
print(f'Sixteenth register/docs updated: {e} explicit/{a} total/233 targets; literal A and historical/source-attribution exceptions remain.')
