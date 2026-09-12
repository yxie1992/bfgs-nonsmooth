#!/usr/bin/env python3
"""Regenerate the positive narrative's exact source/formal correspondence record."""
from pathlib import Path
import copy, datetime, hashlib, json, re
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'editorial/narrative_rebuild/positive_contract_review.json'
PROJECT=ROOT/'bfgs_lean_stage1'
claims={x['id']:x for x in json.loads((PROJECT/'master_report/CLAIMS.json').read_text())['claims']}
index=json.loads((PROJECT/'master_report/DECLARATION_INDEX.json').read_text())
prior=json.loads((ROOT/'editorial/positive_contract_review.json').read_text())
run=ROOT/'editorial/narrative_rebuild/positive_formal/runs/20260912_mixed_benchmark_02'
supplement={x['name']:x for x in json.loads((run/'declarations.json').read_text())}
files=['paper/sections/global.tex','paper/sections/local.tex','paper/appendices/planar_geometry.tex','paper/statements/positive_partition.tex']
texts={f:(ROOT/f).read_text() for f in files}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
locs={}
for f,s in texts.items():
 for m in re.finditer(r'\\label\{([^}]+)\}',s):
  if m[1] in locs: raise ValueError('Duplicate label '+m[1])
  locs[m[1]]={'path':f,'line':s[:m.start()].count('\n')+1}

def exports(spans):return sorted({e for span in spans for e in claims[span]['exports']})
def exact(n):
 if n in supplement:
  d=supplement[n]
  return {'name':n,'signature':d['signature'],'source_path':'editorial/narrative_rebuild/positive_formal/MixedBenchmark.lean',
   'source_range':d['source_range'],'axioms':d['axioms'],'unsafe':d['unsafe'],'partial':d['partial'],
   'evidence':'editorial/narrative_rebuild/positive_formal/runs/20260912_mixed_benchmark_02/declarations.json'}
 d=index[n]
 return {k:d[k] for k in ['name','signature','source_path','source_range','axioms','unsafe','partial']}

specs=[
('art:radial-equivalence',['R.span.3','R.span.4','R.span.5'],[
 'BfgsVerification.RadialCertificate.radial_of_inward_on_compact',
 'BfgsVerification.RadialCertificate.inward_probe_quadratic_bound',
 'BfgsVerification.RadialCertificate.radialNumerator_swap'],
 'Article now proves only IR⇒RS, with actual differentiable endpoints and no inward-sample derivative. Full equivalence remains in companion Chapter4. Compact sublevel/attained minimum specialize the stronger compact-domain forward declaration. Nonnegative constants are a harmless normalization.'),
('art:radial-convergence',['R.span.4','T.span.7'],[
 'BfgsVerification.AdmissibleBFGSRun.radial_certificate_convergence_on_sublevel',
 'BfgsVerification.inwardCertificateConvergence'],
 'Either RS or the proved sufficient inward model on the compact original sublevel gives actual-run values and solution-set distance; uniqueness is used only for whole-iterate convergence.'),
('art:centered',['F.span.1','R.span.10'],[
 'BfgsVerification.AdmissibleBFGSRun.centered_values',
 'BfgsVerification.AdmissibleBFGSRun.centered_iterates',
 'BfgsVerification.AdmissibleBFGSRun.distance_to_argmin_of_values'],
 'Finite convex F, minimizer star, convex locally C1,1 psi on open convex U, finite convex degree-one gamma, exact centered representation on U, compact entire initial sublevel contained in U. Article open-convex U is a specialization of the formal open-set contract. No separate summand minima. Distance follows the recorded compact-value theorem; uniqueness only for iterates. Article uses its complete inward-Taylor proof, whereas the old principal implementation uses the proved cocoercivity correction bound.'),
('art:mixed-benchmark',['F.span.1','F.span.6','R.span.7','R.span.10'],[
 'ArticlePositive.mixed_benchmark_global','ArticlePositive.mixed_inward_error',
 'ArticlePositive.mixed_inward_on_sublevel',
 'BfgsVerification.UnexcitedMetric.objective_convex','BfgsVerification.UnexcitedMetric.unique_minimum'],
 'Literal F(u,v)=u²+|v|, all arbitrary actual AdmissibleBFGSRun2 F, no run convergence premise or vertical-start restriction. New end-to-end wrapper discharges compactness and inward bounds from the literal objective and concludes values0 and whole iterates0. Exact inward identity retains0≤tau≤1. The old UnexcitedMetric.run_limits vertical family is not used as the general conclusion.'),
('art:homogeneous',['H.span.3','H.span.9','H.span.12'],[
 'BfgsVerification.AdmissibleBFGSRun.homogeneous_coercive_iterates_zero',
 'BfgsVerification.AdmissibleBFGSRun.homogeneous_bounded_below_convergence',
 'BfgsVerification.Homogeneous.positive_of_bounded_zero_sublevel',
 'BfgsVerification.Homogeneous.bounded_zero_sublevel_of_coercive'],
 'Finite convex degree-one homogeneous objective in positive finite dimension; genuine coercivity, arbitrary actual run. Origin uniqueness and all compact sublevels are derived, not assumed on the run. Article proves this compact specialization using exact inward homogeneity; full noncompact dichotomy is explicitly companion-only.'),
('art:homogeneous-examples',['H.span.9','H.span.12','H.span.20'],[
 'BfgsVerification.AdmissibleBFGSRun.homogeneous_iterates_zero_of_bounded_zero_sublevel',
 'BfgsVerification.Homogeneous.positive_of_bounded_zero_sublevel',
 'BfgsVerification.Homogeneous.finiteMaxLinear_convex',
 'BfgsVerification.Homogeneous.finiteMaxLinear_homogeneous'],
 'Explicit specializations to a norm, a finite convex degree-one gauge with bounded unit sublevel, or a finite linear maximum with bounded zero sublevel. The article proves the ray/sphere positivity deduction, and bounded unit sublevel implies bounded zero sublevel by inclusion. No affine intercepts, no noncoercive all-iterate claim, no symmetry needed for gauges. Standard norm axioms supply continuity/positive homogeneity/convexity; no new algorithmic theorem assumed.'),
('art:localization',['M.span.1'],[
 'BfgsVerification.Localization.sphere_gap','BfgsVerification.Localization.neighborhood_basin',
 'BfgsVerification.Localization.sublevel_compact'],
 'Finite convex original objective with unique minimizer; compactness of all sublevels and low-sublevel containment derived by sphere gap and convex radial lower bound. Basin depends only on F and neighborhood, before arbitrary SPD/run/constants.'),
('art:polyhedral',['R.span.8'],[
 'BfgsVerification.ConvexCellRadial.finite_polyhedral_basin',
 'BfgsVerification.ConvexCellRadial.radial_derivative_eq',
 'BfgsVerification.ConvexCellRadial.local_cells_inward'],
 'Canonical existing statement is input once in local.tex. Finite closed full-dimensional polyhedral cover of local U; separate open extension domains containing U∩Pi, extensions only locally C1,1 and need not convex. Discard nonincident cells then shrink before using radial derivative equality. Unique minimizer and whole original-objective convexity retained.'),
('art:plq',['R.span.8','R.span.11','R.span.12'],[
 'BfgsVerification.ConvexCellRadial.piecewise_quadratic_basin',
 'BfgsVerification.ConvexCellRadial.smooth_plus_piecewise_quadratic_basin'],
 'PLQ explicitly means quadratic formulas on a finite cover by closed full-dimensional polyhedral cells. Locally C1,1 convex loss may be added; unique minimizer required. Finite polyhedral/absolute/hinge penalties are piecewise affine specializations. Arbitrary finite maxima of quadratics are not claimed polyhedrally partitioned.'),
('art:local-centered',['F.span.1','R.span.10','R.span.12'],[
 'BfgsVerification.CenteredSmoothSublinear.local_centered_basin'],
 'Local exact centered representation around unique minimizer, all theorem smoothness/convexity/homogeneity assumptions retained. Objective-only epsilon with non-strict start threshold, containment of all accepted iterates, value and whole-iterate convergence.'),
('art:planar-cluster',['C.span.2','C.span.3','C.span.4','C.span.6','C.span.7','C.span.8','C.span.9','C.span.10'],[
 'BfgsVerification.AdmissibleBFGSRun.planar_affineCritical_cluster_on_sublevel',
 'BfgsVerification.planarAffineCriticalCluster',
 'BfgsVerification.AdmissibleBFGSRun.steps_tendsto_zero_of_strict_contour',
 'BfgsVerification.AdmissibleBFGSRun.scalar_frame_energy',
 'BfgsVerification.AdmissibleBFGSRun.scalar_frame_reciprocal_sum_bound'],
 'Dimension exactly2; finite convex F with attained min and compact K={F≤b}, b>Fstar, start≤b. Every positive sublevel up to b has no nontrivial frontier segment. Regular smooth/convex-two-branch structure only away from actual affine-critical set; pair gradients linearly independent. Cluster existence, gradient bounds, summability, positive limiting level under contradiction and vanishing steps are derived. The appendix field is length-local; the whole tail is proved short before using it. No singleton-cluster or matrix-asymptotic assumption.'),
('art:planar-convergence',['C.span.2','C.span.3','C.span.10','C.span.11'],[
 'BfgsVerification.AdmissibleBFGSRun.planar_convergence_on_sublevel',
 'BfgsVerification.AdmissibleBFGSRun.convergence_of_affineCritical_cluster'],
 'Adds actual affine correctness on K: affine-critical points there are minimizers. Value and solution-set distance converge; uniqueness only for whole sequence. Does not conflate affine criticality and stationarity without the added premise.'),
('art:planar-max',['A.span.3','C.span.2','C.span.11'],[
 'BfgsVerification.PlanarMaxRegular.finite_max_local_basin',
 'BfgsVerification.PlanarMaxRegular.finite_max_hessian_local_basin',
 'BfgsVerification.ConvexSubdifferential.local_affine_critical_correctness',
 'BfgsVerification.PlanarMaxRegular.regular_of_finite_max_independent'],
 'Finite convex F:R²→R with unique minimizer; exact local finite maximum of convex C² branches; only original-active gradients affinely independent and strictly positive optimal weights. Sufficiently low global sublevel frontier strictness retained, or common positive branch Hessian bound as proved sufficient alternative. Objective-only epsilon precedes run/SPD/valid constants, strict initial threshold. Local subgradient formula proved via finite directional max, separation and extension of supporting inequalities by convexity.'),
('art:nonradial-example',['C.span.13','C.span.14'],[
 'BfgsVerification.planarQuadraticModel','BfgsVerification.planarQuadraticCoefficients',
 'BfgsVerification.planarQuadraticBasin','BfgsVerification.planarQuadraticCurve',
 'BfgsVerification.planarQuadraticSeparation',
 'BfgsVerification.PlanarQuadraticExample.fullBFGS_explicit_basin',
 'BfgsVerification.PlanarQuadraticExample.not_radial_secant_on_neighborhood'],
 'Literal three quadratics, Hessians I..3I, branch average=u²+v², exact denominator3(1+v−uv), all three numerator formulas and four box lower bounds, unique positive coefficients. F(x0)<1/100 actual-run basin arbitrarySPD/all valid constants. Separate radial obstruction uses c1=1/4,c2=1/2 with one fixed eta for each neighborhood before arbitrarily small eligible crossing pairs and unbounded quotient. Full polynomial and square-root formulas are covered by the complete C13/C14 export unions; no external computation is a proof premise.'),
('art:planar-field',['C.span.6','C.span.7','C.span.8','C.span.9'],[
 'BfgsVerification.PlanarAllPairs.source_all_endpoint_estimates',
 'BfgsVerification.PlanarAllPairs.sourceAllEndpointEstimates',
 'BfgsVerification.PlanarAllPairs.SourceAllEndpointEstimatesTarget'],
 'One objective-constructed actual field on compact regular noncritical planar level set; strict contour at that level; all sufficiently short eligible endpoint pairs, full segment buffer/transversality, visible common pairing, bounded correction, positive transport factor and absolute log bound; square-factor bound requires d≤1. Added article nonempty C/positive attained level are harmless specializations. All field/constant choices precede endpoints, no H dependency, no finite crossing count. Full proof in appendix; elementary right-derivative comparison included.')]
rows=[]
for label,spans,primary,note in specs:
 loc=locs[label];s=texts[loc['path']];offset=s.index('\\label{'+label+'}')
 begins=list(re.finditer(r'\\begin\{(theorem|lemma|corollary|proposition|definition)\}',s[:offset]))
 begin=begins[-1];kind=begin[1];end=s.index('\\end{'+kind+'}',offset)+len('\\end{'+kind+'}')
 row={'label':label,'kind':kind,'article_location':loc,'article_statement':s[begin.start():end],
      'source_span_ids':spans,'primary_declarations':primary,'all_span_exports':exports(spans),
      'exact_formal_declarations':[exact(n) for n in primary],
      'hypothesis_and_proof_correspondence':note,'status':'CONTRACT_REVIEWED_PROOF_COMPLETE_DRAFT'}
 rows.append(row)

eqspec=[('art:radial-condition','art:radial-equivalence'),('art:inward-condition','art:radial-equivalence'),('art:inward-to-radial','art:radial-equivalence'),
 ('art:corner-velocity','art:planar-field'),('art:planar-height','art:planar-field'),('art:planar-field-formula','art:planar-field'),('art:planar-corner-field','art:planar-field'),('art:planar-tangent-cancellation','art:planar-field'),('art:planar-determinant-derivative','art:planar-field')]
bylabel={x['label']:x for x in rows}
eqs=[{'label':label,'article_location':locs[label],'governing_statement':parent,
 'source_span_ids':bylabel[parent]['source_span_ids'],'all_span_exports':bylabel[parent]['all_span_exports']} for label,parent in eqspec]

dedspec=[
('This condition controls only inward first-order modeling error.',['R.span.6'],'Inward remainder controls actual radial second-derivative expression; an a.e. bound alone can miss singular radial curvature. No a.e.-Hessian equivalence claimed.'),
('A finite convex positively homogeneous function is sublinear:',['F.span.1','H.span.9'],'Actual degree-one radial identity; angular jumps not bounded by a full Hessian hypothesis.'),
('In particular, a finite convex polyhedral penalty,',['R.span.8','R.span.11'],'Finite piecewise-affine specialization of finite-cell theorem; losses locally C1,1 and uniqueness retained.'),
('For example, a locally $C^{1,1}$ convex loss plus finitely many Euclidean',['F.span.1','R.span.12'],'Exact split of each Euclidean residual into smooth nonzero-residual or centered homogeneous zero-residual term; no assertion for arbitrary spectral penalties.'),
('At a point outside this set, let $a$',['C.span.3'],'Minimum-norm point of affine hull of full convex subdifferential; equal pairing and common unit rate, distinguished from ordinary strict common descent.'),
('The complete companion,',['H.span.3','H.span.12','H.span.20'],'Companion-only disposition: noncompact homogeneous value dichotomy and additional iterate consequences are not article-proof claims.')]
deds=[]
for anchor,spans,note in dedspec:
 hits=[(f,s.index(anchor)) for f,s in texts.items() if anchor in s]
 if len(hits)!=1: raise ValueError((anchor,hits))
 f,pos=hits[0]
 deds.append({'anchor':anchor,'article_location':{'path':f,'line':texts[f][:pos].count('\n')+1},
 'source_span_ids':spans,'all_span_exports':exports(spans),'hypothesis_and_proof_correspondence':note,
 'status':'Explicit proved deduction or explicitly marked companion disposition; bibliography separate.'})
roots={n for r in rows for n in r['all_span_exports']+r['primary_declarations'] if n in index}
roots.update(n for r in deds for n in r['all_span_exports'])
closure=set();pending=list(roots)
while pending:
 n=pending.pop()
 if n in closure:continue
 d=index[n];closure.add(n)
 if d['unsafe'] or d['partial'] or set(d['axioms'])-{'propext','Classical.choice','Quot.sound'}:raise ValueError('Unsafe axiom scope '+n)
 for key in ['value_project_dependencies','type_project_dependencies','structural_project_dependencies']:
  pending.extend(d[key])
spanids=sorted({span for r in rows+deds for span in r['source_span_ids']})
sourcefiles={str(PROJECT/'master_report'/claims[i]['corrected_source']) for i in spanids}
sourcefiles.update(str(PROJECT/'master_report'/p) for p in ['CLAIMS.json','DECLARATION_INDEX.json'])
labels=set(locs);mapped=set(bylabel)|{x[0] for x in eqspec}
scope_labels={'art:global','art:local','art:positive','art:planar-appendix'}
if labels-mapped-scope_labels:raise ValueError('Unmapped '+str(labels-mapped-scope_labels))
out={
 'status':'PROOF_COMPLETE_SOURCE_CONTRACT_REVIEWED_AWAITING_FINAL_ASSEMBLY',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'baseline_commit':'00362c0249262d182866f14bac756a7c4edac95c',
 'article_files':files,'article_sha256':{f:sha(ROOT/f) for f in files},
 'source_sha256':{str(Path(p).relative_to(ROOT)):sha(Path(p)) for p in sorted(sourcefiles)},
 'statements':rows,'equation_mappings':eqs,'unnumbered_mathematical_deductions':deds,
 'full_source_span_register':[{k:claims[i][k] for k in ['id','module','corrected_source','corrected_line_ranges','classification','exports','review_note'] if k in claims[i]} for i in spanids],
 'supplemental_formal_evidence':{'run':'editorial/narrative_rebuild/positive_formal/runs/20260912_mixed_benchmark_02','summary':json.loads((run/'SUMMARY.json').read_text()),'declarations':list(supplement.values())},
 'formal_project_dependency_closure':sorted(closure),
 'formal_dependency_audit':{'selected_project_roots':len(roots),'transitive_project_declarations':len(closure),
 'axioms':['Classical.choice','Quot.sound','propext'],'unsafe_or_partial':[],
 'compiler_scope':'Fresh literal benchmark supplemental compile and full structural audit; other source proof evidence remains the sealed original audit, with unchanged inputs.'},
 'standard_external_inputs':['Finite-dimensional compactness, supporting-plane calculus and separation; finite-max subdifferential formula proved in article.','Classical inverse function theorem and smooth cutoffs on finitely separated circle arcs; used in actual field construction, with corresponding Lean exports.','Normal-angle formula and local convex-gradient inequality are cited at point of use and also calculated/proved in article.'],
 'companion_retained_variants':[
 {'source_span_ids':['R.span.3','R.span.4','R.span.5'],'location':'companion/chapters/04_R.tex','disposition':'Full RS⇔IR equivalence remains; article proves only sufficient IR⇒RS direction and says so.'},
 {'source_span_ids':['H.span.3','H.span.4','H.span.5','H.span.19','H.span.20'],'location':'companion/chapters/07_H.tex','disposition':'Noncompact values and distinct iterate conclusions remain companion-only.'},
 {'source_span_ids':['C.span.12','C.span.15'],'location':'companion/chapters/09_C.tex','disposition':'Semialgebraic planar alternative and arbitrary-dimensional secant-only result remain separate; not substituted for article planar hypotheses.'}],
 'proof_completeness_review':{'essential_companion_outsourcing':False,'labeled_mathematical_statements':len(rows),'labeled_equations':len(eqs),
 'length_local_planar_field_distinguished_from_decrease_local_band_certificate':True,
 'all_math_labels_mapped':True,'no_unchecked_computation_premises':True,
 'reader_facing_main_conditions_explained':['inward accuracy','compact centered structure','coercive homogeneous geometry','finite local cells','affine correctness and regular planar contours','positive active multipliers'],
 'status':'Root and independent bibliography reviewer found no blocking mathematical gap; final render and merged correspondence managed by root.'}
}
OUT.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'statements':len(rows),'equations':len(eqs),'unnumbered':len(deds),'source_spans':len(spanids),'full_export_roots':len(roots),'project_closure':len(closure),'output':str(OUT.relative_to(ROOT))},indent=2))
