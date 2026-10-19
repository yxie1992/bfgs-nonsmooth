#!/usr/bin/env python3
"""Reorganize the frozen corrected mathematics with explicit source correspondence."""
from pathlib import Path
import argparse,hashlib,json,re,sys
ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'bfgs_lean_stage1/master_report'
OUT=ROOT/'companion'
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true',help='Regenerate in memory and compare all managed outputs without writing.')
args=parser.parse_args()
baseline=json.loads((ROOT/'editorial/BASELINE.json').read_text())
def guard_source(path):
 relative=str(path.relative_to(ROOT))
 expected=baseline['files'].get(relative)
 if expected is None:
  raise SystemExit('Source is absent from the frozen editorial baseline: '+relative)
 actual=hashlib.sha256(path.read_bytes()).hexdigest()
 if actual!=expected:
  raise SystemExit('Frozen source SHA256 mismatch: '+relative)
guard_source(SOURCE/'CLAIMS.json')
guard_source(SOURCE/'DECLARATION_INDEX.json')
claims=json.loads((SOURCE/'CLAIMS.json').read_text())['claims']
index=json.loads((SOURCE/'DECLARATION_INDEX.json').read_text())
for source in {SOURCE/c['corrected_source'] for c in claims}:
 guard_source(source)
outputs={}
order=[('I','Scope, quantifiers and the result map'),('M','BFGS algebra and reciprocal budgets'),('T','Transported comparison energies'),('R','Radial modeling and finite partitions'),('G','What comparison certificates express'),('F','Concrete objectives, lifting and rates'),('H','Homogeneous objectives without compactness'),('A','Affine criticality and stratified geometry'),('C','Planar switching and affine-critical cluster points'),('Q','Flat contours and parabolic branches'),('U','Fixed normal geometry in arbitrary dimension'),('D','The exact deterministic seed and local smooth embedding'),('L','Failure with positive lower curvature'),('E','Formal correspondence and verification')]
number={m:str(i+1) for i,(m,_) in enumerate(order)}
internal={'SM':'M','SH':'H','ST':'T','SG':'G','SR':'R','SL':'R','SP':'F','SQ':'F','SE':'F','SV':'M','SA':'A','SC':'C','SU':'U','SD':'D','SLC':'L'}
introductions={
'I':'The scope map separates objective convergence, convergence to the solution set and convergence of the full sequence. It also separates universal admissible-run statements from the particular deterministic executions used in the counterexamples.',
'M':'The same matrix calculation supports every positive result in this volume. We establish it once for the full BFGS matrices, then derive its qualitative, finite-horizon and summable-budget consequences.',
'T':'The reciprocal budget becomes a convergence theorem when geometry controls a comparison energy. Visibility, secant control and transport are conditions on the objective, with no assumption on the BFGS matrices.',
'R':'The global mixed-benchmark question is answered through inward model accuracy: a centered sublinear term contributes no inward remainder, and a smooth term contributes a quadratic one. The same condition localizes to finite polyhedral partitions without requiring cell identification.',
'G':'The certificate is a sufficient condition for convergence. Its normalization and pointwise geometry help interpret it, and scalar examples show that BFGS converges where the condition fails.',
'F':'These applications turn the common analytic mechanism into verifiable objective classes. The chapter also derives an affine-fiber selection formula and quantitative rates.',
'H':'Coercive homogeneous objectives provide a broad global convergence family. This chapter goes beyond that compact case: a different potential gives noncompact value alternatives, recurrent-gradient obstructions and conditional iterate conclusions.',
'A':'Affine balance concerns equal-rate descent, whereas convex balance concerns stationarity. Chapters~\\ref{comp:C} and~\\ref{comp:U} turn this geometry into convergence theorems.',
'C':'Curved switching interfaces can defeat inward radial accuracy even in a convergent problem. The planar contour construction supplies moving comparison geometry; the explicit three-quadratic basin demonstrates its added scope. The signed determinant and one-sided transport proof make the resulting convergence theorem independent of assumed matrix behavior.',
'Q':'Flat contour segments are allowed in this finite parabolic family. Its explicit field gives a convergence theorem that reaches flat-contour objectives outside the strict-contour planar theorem.',
'U':'A fixed space of jump normals leaves controlled smooth directions in arbitrary dimension. Residual transport can be paid for in those directions; this is a different hypothesis from planar switching geometry.',
'D':'A finite algebraic cycle first determines every query of a specified line search. Scaled copies then produce one fixed convex objective with failing initial points approaching its optimizer.',
'L':'Positive lower curvature requires a separate construction. The local finite-branch functions have Lipschitz gradients, and three of the four lose second differentiability at the minimizer.',
'E':'This chapter records the formal verification: the dated authoring audit comes first, followed by the preserved release record.'}
# M44 in TODO_MANUSCRIPT_REVIEW.md (18 October 2026): wording edits that remove
# defensive or over-qualifying sentences, applied to the finished chapter bodies.
m44_edits=json.loads((ROOT/'editorial/defensive_wording_20261018/companion_edits.json').read_text())['edits']
rows=[];transform_log=[];chapter_inputs=[]
for module,title in order:
 group=[c for c in claims if c['module']==module];path=SOURCE/group[0]['corrected_source'];text=path.read_text();original=text
 for c in sorted(group,key=lambda c:len(c['corrected_excerpt']),reverse=True):
  excerpt=c['corrected_excerpt'];assert text.count(excerpt)==1,c['id']
  text=text.replace(excerpt,'\n% SOURCE_BEGIN '+c['id']+'\n'+excerpt+'\n% SOURCE_END '+c['id']+'\n',1)
 notes=[]
 def note(m):
  block=m[0];notes.append(re.sub(r'^\\paragraph\{Attribution and comparison\.\}\s*','',block.split('\n',1)[1].rsplit('% END ATTRIBUTION',1)[0].strip()))
  transform_log.append({'module':module,'kind':'move_editorial_attribution_to_chapter_notes','note':m[1]})
  return ''
 text=re.sub(r'% BEGIN ATTRIBUTION ([\w.]+)\n.*?% END ATTRIBUTION \1\n?',note,text,flags=re.S)
 if notes:
  # Relocated notes use neutral direction words; their mathematical content is unchanged.
  notes=[re.sub(r'\bbelow\b','in this chapter',n) for n in notes]
  text+='\n\\section*{Relation to earlier work}\n'+'\n\n'.join(notes)+'\n'
 def cite(m):
  keys=[k.strip() for k in m[2].split(',')];ext=[k for k in keys if k not in internal];refs=list(dict.fromkeys(internal[k] for k in keys if k in internal));parts=[]
  if ext:parts.append('\\cite'+(m[1] or '')+'{'+','.join(ext)+'}')
  if refs:parts.append('Chapter'+('s' if len(refs)>1 else '')+'~'+', '.join('\\ref{comp:'+x+'}' for x in refs))
  return '; '.join(parts)
 text=re.sub(r'\\cite(\[[^\]]*\])?\{([^}]+)\}',cite,text)
 # October 2026 Lean coverage of the companion (TODO_MANUSCRIPT_REVIEW.md, M17
 # and M28): the source notes of H and Q cite some of their own tagged equations,
 # and H its Theorem H.A, without the module prefix, so the renumbering below did
 # not reach them. With the prefix it prints the chapter's numbers.
 source_prefix={
  'H':[('prefix_theorem_reference_in_section_title','Theorem\nA}','Theorem\nH.A}',1),
       ('prefix_hessian_form_references','(2.1)','(H.2.1)',2),
       ('prefix_telescoping_reference','(5.2)','(H.5.2)',1),
       ('prefix_anchor_limit_references','(7.3)','(H.7.3)',2),
       ('prefix_invariant_subspace_reference','(7.1)','(H.7.1)',1),
       ('prefix_zero_limit_formula_reference','(7.2)','(H.7.2)',1)],
  'Q':[('prefix_visibility_reference','(11)','(Q.11)',1),
       ('prefix_radial_error_reference','(12)','(Q.12)',1),
       ('prefix_multiplier_reference','(13)','(Q.13)',1),
       ('prefix_segment_vanishing_reference','(7)','(Q.7)',1),
       ('prefix_branch_change_reference','(16)','(Q.16)',1),
       ('prefix_example_scale_reference','(8)','(Q.8)',1)]}
 prefix_reason={
  'H':'M17 in TODO_MANUSCRIPT_REVIEW.md: the source cites the Hessian form (H.2.1), (H.5.2), (H.7.1)-(H.7.3) and Theorem H.A without the prefix, so the companion printed (2.1), (5.2), (7.1)-(7.3) and Theorem A, which are other displays or do not exist. Lean: Ch07H.energy_identity, Ch07H.weighted_sum_finite, Ch07H.common_vector_energy_step, Ch07H.endpoint_pairings, Ch07H.iterate_lift, Ch07H.zero_limit_formula, Ch07H.theorem_7A.',
  'Q':'M28 in TODO_MANUSCRIPT_REVIEW.md: the source cites (Q.7), (Q.8), (Q.11)-(Q.13) and (Q.16) without the prefix, so the companion printed numbers that no companion equation has. Lean: Ch10Q.secant_visibility, Ch10Q.radial_error, Ch10Q.multiplier_estimates, Ch10Q.segment_bound_facts, Ch10Q.branch_change, Ch10Q.example_scale.'}
 for kind,old,new,count in source_prefix.get(module,[]):
  assert text.count(old)==count,(module,kind)
  text=text.replace(old,new)
  transform_log.append({'module':module,'kind':kind,'reason':prefix_reason[module]})
 # Source theorem tags are retained with their chapter number replacing the module letter.
 for m,num in number.items():
  text=re.sub(r'\b'+m+r'\.(?=[0-9A-Z])',num+'.',text)
  text=re.sub(r'\bModule~? '+m+r'\b',r'Chapter~\\ref{comp:'+m+'}',text)
  text=re.sub(r'\bModule~'+m+r'\b',r'Chapter~\\ref{comp:'+m+'}',text)
 # Complete the source-to-chapter aliases, including plural and label forms.
 def plural_chapters(match):
  first,second=match.group(1),match.group(2)
  if first not in number or second not in number:return match[0]
  replacement='Chapters~\\ref{comp:'+first+'} and~\\ref{comp:'+second+'}'
  transform_log.append({'module':module,'kind':'replace_plural_source_module_reference','old':match[0],'new':replacement,'reason':'Point to the operative numeric companion chapters; no mathematical assertion changes.'})
  return replacement
 text=re.sub(r'\bModules ([A-Z]) and ([A-Z])\b',plural_chapters,text)
 def labeled_chapter(match):
  target=match.group(1)
  if target not in number:return match[0]
  replacement='Chapter~\\ref{comp:'+target+'}'
  transform_log.append({'module':module,'kind':'replace_labeled_source_module_reference','old':match[0],'new':replacement,'reason':'Use companion chapter terminology with the corresponding existing label.'})
  return replacement
 text=re.sub(r'\bModule~\\ref\{([A-Z]):chapter\}',labeled_chapter,text)
 # The R/G source overrides print their prefix before a macro, which the
 # preceding printed-number substitution deliberately does not match.
 old_numbering=r'\renewcommand{\thetheorem}{'+module+r'.\arabic{section}.\arabic{theorem}}'
 new_numbering=r'\renewcommand{\thetheorem}{'+number[module]+r'.\arabic{section}.\arabic{theorem}}'
 if old_numbering in text:
  assert text.count(old_numbering)==1,module
  text=text.replace(old_numbering,new_numbering)
  transform_log.append({'module':module,'kind':'replace_source_theorem_macro_prefix','old':old_numbering,'new':new_numbering,'reason':'Keep printed theorem numbering consistent with the numeric companion chapter.'})
 # Remove redundant manual prefixes inside automatic section titles.
 text=re.sub(r'(\\subsection\{)(?:\d+\.\d+\s+)',r'\1',text)
 # The old program-execution sentence is not an available proof dependency.
 old='The standard-library program \\texttt{verify\\_certificate.py} constructs the two polynomials, differentiates them, constructs $M$, and checks these rational inequalities without floating-point arithmetic. This is an existence certificate, not a residual-tolerance assertion.'
 if old in text:
  text=text.replace(old,'These bounds are exact rational certificate inequalities. Appendix~\\ref{comp:seed_certificate} specifies the polynomial residual, coefficient bounds, sound interval operations and finite query inequalities. The contraction argument explains how these bounds imply existence and uniqueness. The formal root and coefficient certificates are separately indexed in the theorem ledger.')
  transform_log.append({'module':module,'kind':'remove_unavailable_program_execution_dependency','reason':'Actual exact formal certificates and explicit contraction deduction replace an unsupported program-execution reference; mathematical inequalities and conclusion unchanged.'})
 text=text.replace('Section 13.2, Theorem 13.3','Theorem 13.3')
 # Publication comparisons preserve the inspected line-search scope of LO 5.1.
 if module in {'R','H'}:
  transform_log.append({'module':module,'kind':'qualify_LO_scalar_attribution','reason':'The inspected LO Section 5.1 scalar analysis specializes c1=0; it is not equated with a theorem for every positive Armijo parameter.'})
 text=text.replace('scalar absolute-value convergence appears in Lewis--Overton~\\cite[Section~5.1]{LO}. These are known cases recovered here.',
                   'Lewis--Overton~\\cite[Section~5.1]{LO} analyzes the scalar absolute-value model with its stated line-search conventions. The Euclidean-norm theorem is a known case recovered here.')
 text=text.replace('and the scalar absolute-value case is established in Lewis--Overton~\\cite[Section~5.1]{LO}.',
                   'while Lewis--Overton~\\cite[Section~5.1]{LO} analyzes the scalar absolute-value model with its stated line-search conventions.')
 old_scope='The proof modules retain their internal numbering and shared algebra in '
 if old_scope in text:
  assert text.count(old_scope)==1,module
  text=text.replace(old_scope,'The chapters use ordinary chapter numbering and shared algebra in ')
  transform_log.append({'module':module,'kind':'update_numbering_scope_prose','reason':'The companion uses chapter numbers, with source identifiers retained in correspondence metadata.'})
 if module=='D':
  trial_heading=r'\section{Every deterministic oracle decision is certified}'
  assert text.count(trial_heading)==1
  text=text.replace(trial_heading,trial_heading+r'\label{comp:trial_table}')
  transform_log.append({'module':module,'kind':'add_stable_trial_table_cross_reference','label':'comp:trial_table','reason':'The companion finite-certificate appendix refers to this retained full trial table.'})
 if module=='I':
  heading=r'\section{Supersession policy}'
  assert text.count(heading)==1
  text=text.replace(heading,'\\clearpage\n'+heading)
  transform_log.append({'module':module,'kind':'keep_heading_with_table','reason':'All-page visual review found the supersession heading stranded before its longtable. Explicit page break changes layout only.'})
 if module=='C':
  pattern=r'\\begin\{align\*\}\n f_0\(u,v\).*?\\end\{align\*\}'
  blocks=list(re.finditer(pattern,text,re.S));assert len(blocks)==1
  block=blocks[0][0]
  replacement=block.replace(r'\begin{align*}',r'\[\begin{aligned}').replace(r'\end{align*}',r'\end{aligned}\]')
  text=text.replace(block,replacement)
  transform_log.append({'module':module,'kind':'keep_three_branch_definition_together','reason':'Visual review found the definition split across pages. Unbreakable aligned display retains every formula and all theorem hypotheses.'})
 # October 2026 Lean review: the lower-curvature failures hold for every
 # admissible pair of line-search constants, with one orbit, objective and
 # family of initial points chosen before the pair (bfgs_lean_article,
 # LUniform.uniform_global_failure and LUniform.uniformSmoothLocalFailure), as
 # in the article's Proposition art:quadratic_failure and Theorem
 # art:local-failure-lower.
 constant_range={
  'L':[('state_lower_failures_for_admissible_constants',
        'otherwise. Fix\n\\[\n c_1=10^{-4},\\qquad c_2=\\tfrac12.\n\\]\n',
        'otherwise. Fix\n\\[\n 0<c_1\\le\\tfrac13,\\qquad c_1<c_2<1.\n\\]\nThe orbits, objectives and initial points below are chosen before this pair.\n'),
       ('choose_global_initial_states_before_constants',
        'yet admits initial states $(x_0,H_0)$ producing deterministic full-BFGS iterates converging to the nonstationary origin.',
        'yet admits initial states $(x_0,H_0)$ that produce, for every such pair $(c_1,c_2)$, the same deterministic full-BFGS iterates converging to the nonstationary origin.'),
       ('seed_decisions_strict_for_all_admissible_constants',
        'The seed has strict branch gaps and strict decisions at its finite list of nine queries.',
        'The seed has strict branch gaps and strict decisions at its finite list of nine queries: accepted queries pass Armijo with $c_1=1/3$ and have positive new directional derivatives, and rejected queries raise the value, so the same finitely many strict inequalities decide every such pair $(c_1,c_2)$.'),
       ('agreement_neighborhood_for_all_constants',
        'such that for every state in $\\mathcal N$ with $\\tau>0$, the actual three consecutive',
        'such that for every state in $\\mathcal N$ with $\\tau>0$ and every such pair $(c_1,c_2)$, the actual three consecutive'),
       ('local_embedding_uses_one_orbit_for_all_constants',
        'Use Theorem~\\ref{L:thm:global} to choose one entire bad orbit',
        'Use Theorem~\\ref{L:thm:global}, whose orbit does not depend on $(c_1,c_2)$, to choose one entire bad orbit'),
       ('local_failure_for_admissible_constants',
        'yet the fixed deterministic full-BFGS implementation with $H_0=I$ has bad initial points $x_0^{(n)}\\to0$ converging to nonstationary points $p_n\\to0$.',
        'yet the fixed deterministic full-BFGS implementation with $H_0=I$ has bad initial points $x_0^{(n)}\\to0$ whose runs, the same for every such pair $(c_1,c_2)$, converge to nonstationary points $p_n\\to0$.')],
  'I':[('state_global_lower_failure_for_admissible_constants',
        'For every \\(\\mu>0\\), suitable initial states produce deterministic nonstationary convergence to zero.',
        'For every \\(\\mu>0\\), suitable initial states produce, for every fixed \\(0<c_1\\le1/3\\), \\(c_1<c_2<1\\), the same deterministic nonstationary convergence to zero.'),
       ('state_local_lower_failure_for_admissible_constants',
        'The source uses \\(c_1=10^{-4}\\), \\(c_2=1/2\\).',
        'The source fixed \\(c_1=10^{-4}\\), \\(c_2=1/2\\); the same objective and bad starts serve every \\(0<c_1\\le1/3\\), \\(c_1<c_2<1\\).')]}
 for kind,old,new in constant_range.get(module,[]):
  assert text.count(old)==1,(module,kind)
  text=text.replace(old,new)
  transform_log.append({'module':module,'kind':kind,'reason':'The seed decisions are strict at the corners of the admissible range (accepted queries pass Armijo with c1=1/3 and have positive new slopes; rejected values exceed the current value), so one neighborhood of the seed, and hence one stable-manifold orbit, serves every 0<c1<=1/3 and c1<c2<1. Lean: bfgs_lean_article, LUniform.uniform_global_failure and LUniform.uniformSmoothLocalFailure; article: Proposition art:quadratic_failure and Theorem art:local-failure-lower.'})
 # October 2026 Lean coverage of the companion: corrections M8 and M30 (recurrences),
 # M12-M29 and M33 (reader point R-F-1), and the wording points W1-W46 (except W12,
 # W13, and W45, which is in introductions['L']) of TODO_MANUSCRIPT_REVIEW.md, each
 # with the Lean theorems (bfgs_lean_article, BfgsArticle/Coverage/Companion) that
 # state the corrected text. Further companion recurrences of the article's
 # M30, M34 and M38 found by the line-by-line reading of the article (reader points
 # R-A-1, R-E-2, R-B-5, R-B-3), and the wording point W47.
 # M42 (16 October) makes the known common-tilt nonexistence cases and open case explicit.
 why={
  'M42':'M42 in TODO_MANUSCRIPT_REVIEW.md: distinguish conditional homogeneous convergence from existence of an infinite admissible run. The affine-free case in dimension at most two and the collinear common-tilt case in any dimension have no such run; the noncollinear higher-dimensional case remains open. Lean: Ch07H.maxLinear_affine_free_no_run, Ch07H.tilt_collinear_no_run, Ch07H.tilt_two_values_no_run, Ch07H.maxLinear_line_no_run, Ch07H.linear_objective_no_run; open proposition Ch07H.TiltNoInfiniteRunQuestion.',
  'M30':'M30 in TODO_MANUSCRIPT_REVIEW.md (reader points R-A-1, R-E-2 of the line-by-line reading of the article, 15 October 2026): the first three branches fail to be twice differentiable at the minimizer 0 of the local objective, where the bad starts accumulate; at the limit of a failing run every branch is smooth. Lean: Ch13L.branch_regularity, Article.LowerCurvature.branch_second_differentiability.',
  'M34':'M34 in TODO_MANUSCRIPT_REVIEW.md (reader point R-B-5, as in the article\'s proof of Theorem art:reciprocal-growth): beta_k, used but not defined, is the beta of Theorem M:hierarchy for the k-th update, -y_k^TH_kg_k/q_k = t_k/d_k >= c. Lean: Article.Energy.run_bounds.',
  'M38':'M38 in TODO_MANUSCRIPT_REVIEW.md (reader point R-B-3, as in the article\'s Appendix A): with the scalar factor first, det A(r-z) cannot be read as det(A(r-z)); the identities are unchanged. Lean: Article.MatrixAlgebra.gram_schur.',
  'W47':'W47 in TODO_MANUSCRIPT_REVIEW.md: the regularity class in the section title is typeset as C^{2,1}, with the plain text C2,1 in the PDF bookmark; the label is unchanged. No mathematical assertion changes.',
  'M8':'M8, with M30 (at the minimizer), in TODO_MANUSCRIPT_REVIEW.md: only three of the four branches of the four-branch local construction lose second differentiability, at the minimizer 0 of the local objective, where the bad starts accumulate; the fourth branch is a quadratic. Lean: Ch13L.branch_regularity_at_minimizer, Ch13L.branch_regularity.',
  'M12':'M12 in TODO_MANUSCRIPT_REVIEW.md: read literally, the step version was said to have no finite smooth-branch representation, which is false; the descriptive statement (a countable polyhedral nonsmooth part, used instead of four smooth branches) is kept. Lean: Ch13L.local_failure, Ch13L.step_decomposition.',
  'M13':'M13 in TODO_MANUSCRIPT_REVIEW.md: remnant of the fixed-pair edition; the chapter states its theorems for every 0<c1<=1/3, c1<c2<1, the family of Chapter D. Lean: Ch13L.global_failure, Ch13L.local_failure, Ch13L.admissible_iff.',
  'M14':'M14 in TODO_MANUSCRIPT_REVIEW.md: the fourth branch f3(u,v)=v is linear, hence analytic; the first three are not analytic and no branch is uniformly strongly convex. Lean: Ch12D.not_analytic, Ch12D.branch3_analytic.',
  'M18':'M18 in TODO_MANUSCRIPT_REVIEW.md: the source cites its equations and Theorems 1 and 2 by bare numbers that point to nothing in the companion; (11.14) is the transport hypothesis of Theorem M:residualtheorem with T=I. Lean: Ch11U.transport_hypothesis, Ch11U.series_exact, Ch11U.spike_rs_fails_band.',
  'M19':'M19 in TODO_MANUSCRIPT_REVIEW.md: the spike vanishes for v<=0, so r(v)<=6v^3 fails for every v<0; both bounds hold for every v>=0. Lean: Ch11U.spike_small_bounds, Ch11U.spike_cubic_bound_fails.',
  'M20':'M20 in TODO_MANUSCRIPT_REVIEW.md: "A" is the source letter of Chapter 8; the result meant is Proposition A:semialgebraic. Lean: Ch09C.semialgebraic_low_basin.',
  'M21':'M21 in TODO_MANUSCRIPT_REVIEW.md: the theorem meant is the one-sided transported-certificate convergence theorem of Chapter 3, not the preceding Theorem R:thm:plq. Lean: Ch05G.preceding_theorem, Ch05G.sufficient_condition.',
  'M22':'M22 in TODO_MANUSCRIPT_REVIEW.md: false for the sublevel {f<=2}, which contains zero on its boundary; the claim needs zero in the interior of the sublevel and (c1,c2)=(1/4,1/2). Lean: Ch05G.shifted_global_nonnecessity_interior, Ch05G.two_sublevel_counterexample.',
  'M23':'M23 in TODO_MANUSCRIPT_REVIEW.md: false when the knot lies on the boundary of the band; the argument needs the knot in its interior. Lean: Ch05G.no_certificate_knot_band, Ch05G.knot_band_literal_counterexample.',
  'M24':'M24 in TODO_MANUSCRIPT_REVIEW.md: with the radial field, (S) is the (RS) inequality restricted to eligible pairs, so (RS) gives (S) but not conversely. Lean: Ch03T.rs_gives_s, Ch03T.radial_secant_exact, Ch03T.s_not_exactly_rs.',
  'M25':'M25 in TODO_MANUSCRIPT_REVIEW.md: the source cites its equations (T.3)-(T.6) without the prefix, so the renumbering did not reach them. Lean: Ch03T.hessian_form, Ch03T.annihilation_projection, Ch03T.trace_recurrence, Ch03T.reciprocal_budget, Ch03T.reciprocal_mean_diverges.',
  'M26':'M26 in TODO_MANUSCRIPT_REVIEW.md: Theorem M:residualtheorem requires no invertible transport either; the contrast is with the moving-frame criterion of Section 2.4. Lean: Ch03T.rank_one_degenerate, Ch03T.degenerate_multiplier, Ch02M.frame_criterion.',
  'M27':'M27 in TODO_MANUSCRIPT_REVIEW.md: the bracketed letters named working reports of the original master report and resolve to nothing in the companion; no mathematical assertion.',
  'M29':'M29 in TODO_MANUSCRIPT_REVIEW.md: "L" and "R" are the source letters of Chapters 13 and 4. Lean: Article.LowerCurvature.stable_manifold_positive_scale, Ch13L.global_failure, Ch04R.fourPiece_failure_run.',
  'RF1':'M33 (reader point R-F-1) in TODO_MANUSCRIPT_REVIEW.md: copy n starts at p_n plus a_n times the initial point of the chosen orbit, so the local model must hold there too; the orbit is chosen with its initial point and all its queries in the neighborhood. Lean: Ch13L.chosen_orbit, Ch13L.local_model_along_orbit, Ch13L.global_failure, LUniform.source_spec.',
  'W1':'W1 in TODO_MANUSCRIPT_REVIEW.md: excluding a positive gap needs the divergence of the reciprocal sum, which Theorem M:average gives along runs with bounded gradients. Lean: Ch02M.negligible_corrections, Ch02M.negligible_corrections_of_divergent.',
  'W2':'W2 in TODO_MANUSCRIPT_REVIEW.md: the contradiction uses the hypotheses of Theorem M:average (bounded gradients, d_k -> 0). Lean: Ch02M.frame_criterion.',
  'W3':'W3 in TODO_MANUSCRIPT_REVIEW.md: G, K_0 and V_eta are defined in the proof of Theorem M:average. Lean: Ch02M.superquadratic.',
  'W4':'W4 in TODO_MANUSCRIPT_REVIEW.md: H positive definite and alpha>0, implicit before, are stated as in the article\'s Theorem art:minor-hierarchy. Lean: Ch02M.hierarchy.',
  'W5':'W5 in TODO_MANUSCRIPT_REVIEW.md: the citation map made the chapter cite itself among its sources; "This module" is the source reports\' word for a chapter. No mathematical assertion changes.',
  'W7':'W7 in TODO_MANUSCRIPT_REVIEW.md: the previous admissible-length counterexample belongs to the history of the source report and is not in the companion. No mathematical assertion changes.',
  'W8':'W8 in TODO_MANUSCRIPT_REVIEW.md: "note" is the source reports\' word for a chapter; the earlier notes are not part of the companion. No mathematical assertion changes.',
  'W10':'W10 in TODO_MANUSCRIPT_REVIEW.md: the nonsplitting conclusion comes earlier, in Section 11.7.2; "later" is a remnant of the relocated attribution note. No mathematical assertion changes.',
  'W11':'W11 in TODO_MANUSCRIPT_REVIEW.md: results that the companion states are named by their labels. Lean: Ch11U.spike_rs_fails_band, Ch04R.plq_theorem.',
  'W14':'W14 in TODO_MANUSCRIPT_REVIEW.md: the sentence states the supposition of the proof by contradiction. Lean: Ch09C.contradiction_setup.',
  'W15':'W15 in TODO_MANUSCRIPT_REVIEW.md: the later estimates use 0<=chi_j<=1. Lean: Ch09C.cutoffs_exist, Ch09C.height_convex_combination.',
  'W16':'W16 in TODO_MANUSCRIPT_REVIEW.md: the formulas need epsilon>0. Lean: Ch05G.shifted_crossing_gradients, Ch05G.shifted_crossing_quantities, Ch05G.shifted_crossing_eligible_divergent.',
  'W17':'W17 in TODO_MANUSCRIPT_REVIEW.md: "(V)--(S)" means the two conditions (V) and (S). Lean: Ch03T.rank_one_conditions.',
  'W18':'W18 in TODO_MANUSCRIPT_REVIEW.md: (RS) is defined in Chapter 4. Lean: Ch03T.rs_iff.',
  'W19':'W19 in TODO_MANUSCRIPT_REVIEW.md: the proofs use nonnegative constants, as the article states them (art:radial-condition, art:inward-condition). Lean: Ch04R.RSNonneg, Ch04R.IRNonneg, Ch04R.RSNonneg_iff, Ch04R.IRNonneg_iff, Ch04R.rs_constant_nonneg.',
  'W20':'W20 in TODO_MANUSCRIPT_REVIEW.md: the bound T<=4GR holds for x, z in K, as in the article. Lean: Ch04R.curvature_split, Ch04R.secant_notation.',
  'W21':'W21 in TODO_MANUSCRIPT_REVIEW.md: references to unnamed, later or absent material are made explicit or dropped. Lean: Ch04R.plq_theorem, Ch04R.finite_max_branch_test, Ch04R.finite_max_necessity, Ch04R.spectral_RS_fails.',
  'W22':'W22 in TODO_MANUSCRIPT_REVIEW.md: "D" is the source letter of Chapter 12. Lean: Ch04R.fourPiece_constants, Ch04R.fourPiece_optimizer, Ch04R.fourPiece_transformed_data, Ch04R.fourPiece_curvatures.',
  'W23':'W23 in TODO_MANUSCRIPT_REVIEW.md: the former reason separated the classes only for C^2 summands; a gradient jump that varies along one cell boundary cannot come from one smooth summand plus affine pieces. Lean: Ch04R.plq2d_hessians_and_varying_jump, Ch04R.plq_broader_2d, Ch04R.plq2d_not_smooth_plus_max_affine.',
  'W24':'W24 in TODO_MANUSCRIPT_REVIEW.md: the little-o rate uses Theorem M:superquadratic, which assumes bounded gradients; the inequality needs nothing more. Lean: Ch06F.bounded_correction_rate, Ch06F.linear_budget_rate.',
  'W25':'W25 in TODO_MANUSCRIPT_REVIEW.md: the source rate note and the earlier proof route are not part of the companion, and Theorem M:superquadratic is in Chapter 2. Lean: Ch06F.quadGauge_bigO.',
  'W26':'W26 in TODO_MANUSCRIPT_REVIEW.md: the theorem and the conditions are those of Chapter 3. Lean: Ch10Q.band_certificate, Ch10Q.secant_visibility.',
  'W27':'W27 in TODO_MANUSCRIPT_REVIEW.md: no tolerance is printed in the companion, and the planar example is proved to converge from its basin. Lean: Ch14E.planar_tolerance, Ch14E.spike_tolerance.',
  'W28':'W28 in TODO_MANUSCRIPT_REVIEW.md: every result named uses a uniform gradient bound. Lean: Ch02M.hierarchy_step, Ch02M.weighted_step, Ch02M.average, Ch02M.superquadratic.',
  'W29':'W29 in TODO_MANUSCRIPT_REVIEW.md: the suite labels are names of the original report, not chapter letters. No mathematical assertion changes.',
  'W30':'W30 in TODO_MANUSCRIPT_REVIEW.md: the README describes the read-only check; the runner defines and prints the timestamped output directory. No mathematical assertion changes.',
  'W31':'W31 in TODO_MANUSCRIPT_REVIEW.md: the index classifies every retained assertion and pairs each asserted result with its formal statement; it does not pair every sentence. No mathematical assertion changes.',
  'W32':'W32 in TODO_MANUSCRIPT_REVIEW.md: the bare subsection number now reads as a section reference. No mathematical assertion changes.',
  'W33':'W33 in TODO_MANUSCRIPT_REVIEW.md: the moving-frame contradiction uses Theorem M:average, which assumes bounded gradients. Lean: Ch02M.frame_criterion.',
  'W34':'W34 in TODO_MANUSCRIPT_REVIEW.md: Theorem M:residualtheorem assumes bounded gradients and summable predicted decreases. Lean: Ch02M.residual_theorem.',
  'W35':'W35 in TODO_MANUSCRIPT_REVIEW.md: drafting remnant replaced by a citation of the prior paper. No mathematical assertion changes.',
  'W36':'W36 in TODO_MANUSCRIPT_REVIEW.md: as W1. Lean: Ch02M.negligible_corrections, Ch02M.negligible_corrections_of_divergent.',
  'W37':'W37 in TODO_MANUSCRIPT_REVIEW.md: the source rate note is not part of the companion, Theorem M:superquadratic is in Chapter 2, and the first rate needs bounded gradients. Lean: Ch06F.bounded_correction_rate, Ch06F.linear_budget_rate, Ch06F.homogeneous_rate, Ch06F.quadGauge_rate.',
  'W38':'W38 in TODO_MANUSCRIPT_REVIEW.md: the literature register is bfgs_lean_stage1/literature_audit/ in the repository. No mathematical assertion changes.',
  'W40':'W40 in TODO_MANUSCRIPT_REVIEW.md: the compact sublevel of Chapter 9 lies above the minimum. Lean: Ch01I.p5_cluster, Ch01I.sublevels_compact_of_one.',
  'W41':'W41 in TODO_MANUSCRIPT_REVIEW.md: the disclaimer concerns the constructed branches. Lean: Ch01I.n1_n2_comparison; open question Article.Verification.C2StronglyConvexLocalFailure.',
  'W42':'W42 in TODO_MANUSCRIPT_REVIEW.md: the relocated attribution note names the positive families of Section 1.4. Lean: Ch04R.euclidean_norm_recovered.',
  'W43':'W43 in TODO_MANUSCRIPT_REVIEW.md: E_k and B_k are defined at their first use in Chapter 1. Lean: Ch02M.fixed_energy, Ch01I.smooth_subspace_trace_linear.',
  'W8L':'W8 in TODO_MANUSCRIPT_REVIEW.md (further place): the cited deterministic-bracketing report is Chapter 12 of the companion. No mathematical assertion changes.',
  'W8H':'W8 in TODO_MANUSCRIPT_REVIEW.md (further place): the earlier note is a source note, not part of the companion. No mathematical assertion changes.',
  'W8R':'W8 in TODO_MANUSCRIPT_REVIEW.md (further place): the companion has no preceding report; the sentence now gives the condition (4.RS) its name, the radial secant condition, used in Chapter 3 (W18) and in the article (art:radial-condition). Lean: Ch04R.RSNonneg, Ch04R.RSNonneg_iff, Ch04R.RS_iff_article.',
  'W10H':'W10 in TODO_MANUSCRIPT_REVIEW.md (further place): the three-gradient, rank-two stagnation example is the seed run of Chapter 12, which comes later in the companion; "earlier" is the order of the source notes. Lean: Ch07H.seed_cardinality_sharp, SeedOrbit.sharpRecurrentCardinality.',
  'W17G':'W17 in TODO_MANUSCRIPT_REVIEW.md (the same wording in Chapter 5): "(V)--(S)" means the two conditions (V) and (S), as in the title of the proposition. Lean: Ch05G.pointwise_characterization, Ch05G.proof_direction, Ch05G.rank_one_suffices.',
  'W44':'W44 in TODO_MANUSCRIPT_REVIEW.md: drafting remnant, as in W35. No mathematical assertion changes.',
  'W46':'W46 in TODO_MANUSCRIPT_REVIEW.md: the equation-counter values set by the frozen sources omit the numbered lines of align and gather displays, so the companion printed (12.9)-(12.11), (13.3)-(13.5) and (13.8) twice; the counter now continues. Labels, references and mathematics are unchanged.'}
 corrections={
  'I':[('state_three_of_four_branches_lose_second_differentiability','M8',
        'The individual branches \\textbf{are not twice differentiable at the accumulation point}.',
        'Three of the four branches \\textbf{are not twice differentiable at the minimizer}.'),
       ('describe_step_version_construction','M12',
        'wherever it exists, but a countably piecewise-affine nonsmooth component rather than finitely many smooth branches.',
        'wherever it exists; it is constructed from a countably piecewise-affine nonsmooth component rather than from four smooth branches.'),
       ('rs_implies_radial_specialization','M24',
        'RS is the radial specialization \\(W(x)=(x-x_*)(x-x_*)^T\\).',
        'RS implies the radial specialization \\(W(x)=(x-x_*)(x-x_*)^T\\).'),
       ('describe_claim_index_classification','W31',
        'Every retained mathematical assertion is paired with its reviewed formal statement and Lean proof in the claim/proof index.',
        'Every retained mathematical assertion is classified in the claim/proof index, and each asserted result is paired there with its formal statement and Lean proof.'),
       ('name_section_of_simple_global_failure','W32',
        '\\textbf{Proofs: 12.3.1 and Chapter~\\ref{comp:L}.}',
        '\\textbf{Proofs: Section~12.3.1 and Chapter~\\ref{comp:L}.}'),
       ('state_bounded_gradients_of_frame_criterion','W33',
        'exclude positive-level stagnation.',
        'exclude positive-level stagnation along runs with bounded gradients.'),
       ('state_hypotheses_of_residual_theorem','W34',
        'Together with uniform visibility and bounded secant correction, the resulting \\(O(N^2)\\) error budget',
        'Together with uniform visibility and bounded secant correction, along runs with bounded gradients and \\(\\sum d_k<\\infty\\), the resulting \\(O(N^2)\\) error budget'),
       ('cite_prior_paper','W35',
        "The user's paper is supplied separately, not rebranded as a new result.",
        'That paper~\\cite{XW} is prior work, not a new result of this report.'),
       ('state_bounded_gradients_of_negligible_corrections','W36',
        'A cumulative correction \\(o(\\sum q_k^{-1})\\) excludes a positive gap.',
        'Along runs with bounded gradients, a cumulative correction \\(o(\\sum q_k^{-1})\\) excludes a positive gap.'),
       ('cite_superquadratic_theorem_for_rates','W37',
        'The original rate note recorded big-\\(O\\) corollaries. The later superquadratic reciprocal theorem strengthens them to \\(o(N^{-1/2})\\) for uniformly bounded radial correction,',
        'Big-\\(O\\) versions of the following rates appeared in the source notes. Theorem~\\ref{M:superquadratic} strengthens them to \\(o(N^{-1/2})\\) for uniformly bounded radial correction along runs with bounded gradients,'),
       ('give_repository_path_of_literature_register','W38',
        'The detailed source/version register is delivered in \\path{literature_audit/};',
        'The detailed source/version register is delivered in \\path{bfgs_lean_stage1/literature_audit/};'),
       ('compact_sublevel_above_minimum','W40',
        'have an attained minimum and a compact sublevel,',
        'have an attained minimum and a compact sublevel above the minimum,'),
       ('constructions_not_from_c2_branches','W41',
        'Neither proves local failure for a finite maximum of uniformly strongly convex \\(C^2\\) branches through the optimizer.',
        'Neither is constructed from finitely many uniformly strongly convex \\(C^2\\) branches through the optimizer, so neither proves local failure for that class.'),
       ('name_families_of_relocated_note','W42',
        'These families include established special cases',
        'The positive families of Section~\\ref{strongest-concrete-local-and-global-positive-families} include established special cases'),
       ('define_fixed_reference_energy','W43',
        'The fixed-reference identity is',
        'For a fixed reference point \\(x_*\\) and \\(E_k=(x_k-x_*)^TB_k(x_k-x_*)\\), the fixed-reference identity is'),
       ('define_inverse_matrix','W43',
        'the actual update gives \\(\\operatorname{tr}(P_SB_k)=O(k)\\).',
        'the actual update gives \\(\\operatorname{tr}(P_SB_k)=O(k)\\) for \\(B_k=H_k^{-1}\\).'),
       ('n2_differentiability_at_minimizer','M30',
        'N2 has positive lower curvature and less differentiability at the accumulation point.',
        'N2 has positive lower curvature and less differentiability at the minimizer.'),
       ('typeset_regularity_class_in_n1_title','W47',
        'globally C2,1 convex branches}',
        'globally \\texorpdfstring{$C^{2,1}$}{C2,1} convex branches}')],
  'M':[('drop_self_citation','W5',
        'This module consolidates the common algebra from sources~Chapters~\\ref{comp:M}, \\ref{comp:H}, \\ref{comp:F}, \\ref{comp:U}.',
        'This chapter consolidates the common algebra of the source notes.'),
       ('state_hierarchy_hypotheses','W4',
        'For an ordinary inverse-BFGS update with $s=-\\alpha Hg$, $q=g^THg>0$',
        'For $H\\succ0$ and an ordinary inverse-BFGS update with $s=-\\alpha Hg$, $\\alpha>0$, $q=g^THg>0$'),
       ('define_finite_horizon_constants','W3',
        'For every $\\eta>0$ and $m\\ge2$,\n\\begin{equation}\\label{M:finitehorizon}',
        'For every $\\eta>0$ and $m\\ge2$, with $G$, $K_0$ and $V_\\eta$ as in the proof of Theorem~\\ref{M:average},\n\\begin{equation}\\label{M:finitehorizon}'),
       ('state_bounded_gradients_of_negligible_corrections','W1',
        'Thus $\\sum_{k<N}R_k=o(\\sum_{k<N}q_k^{-1})$ excludes a positive gap.',
        'Thus, along runs with bounded gradients, $\\sum_{k<N}R_k=o(\\sum_{k<N}q_k^{-1})$ excludes a positive gap.'),
       ('frame_contradiction_under_average_hypotheses','W2',
        'Positivity gives $\\sum_{J\\le k<N}q_k^{-1}=O(N)$, contradicting Theorem~\\ref{M:average}.',
        'Positivity gives $\\sum_{J\\le k<N}q_k^{-1}=O(N)$, contradicting Theorem~\\ref{M:average} under its hypotheses.'),
       ('scalar_factor_first_gram_y','M38',
        ' \\det\\operatorname{Gram}_H(y,Z)=\\det A(r-z),',
        ' \\det\\operatorname{Gram}_H(y,Z)=(r-z)\\det A,'),
       ('scalar_factor_first_gram_gy','M38',
        ' =\\det A\\bigl((q-u)(r-z)-(\\kappa-w)^2\\bigr).',
        ' =\\bigl((q-u)(r-z)-(\\kappa-w)^2\\bigr)\\det A.'),
       ('define_beta_k','M34',
        'Since $\\beta_k\\ge c$ and',
        'Since $\\beta_k=-y_k^TH_kg_k/q_k=t_k/d_k\\ge c$ and')],
  'T':[('number_hessian_and_annihilation_references','M25','Using (3)--(4),','Using (3.3)--(3.4),'),
       ('number_trace_recurrence_reference','M25','Divide (6) by','Divide (3.6) by'),
       ('number_reciprocal_divergence_reference','M25','This contradicts (5).','This contradicts (3.5).'),
       ('name_two_conditions','W17','Conditions (V)--(S) become','Conditions (V) and (S) become'),
       ('point_to_moving_frame_criterion','M26','Unlike the preceding moving-frame theorem,',
        'Unlike the moving-frame criterion of Section~\\ref{M:energy},'),
       ('point_to_radial_secant_condition','W18','Given (RS), take',
        'Given the radial secant condition (RS) of Chapter~\\ref{comp:R}, take'),
       ('rs_gives_s_on_eligible_pairs','M24','Condition (S) is exactly (RS), while',
        'With this $W$, (S) is the inequality of (RS) restricted to eligible pairs in $K_\\eta$ with $d\\le\\delta_\\eta$, so (RS) gives (S) with the same constant, while')],
  'R':[('restrict_secant_notation_to_sublevel','W20','For differentiable $x,z$, put','For differentiable $x,z\\in K$, put'),
       ('nonnegative_radial_secant_constants','W19','\\forall\\eta>0\\ \\exists C_\\eta<\\infty:\\quad','\\forall\\eta>0\\ \\exists C_\\eta\\ge0:\\quad'),
       ('nonnegative_inward_model_constants','W19','there exist $M_\\eta<\\infty$ and $\\theta_\\eta\\in(0,1/2]$',
        'there exist $M_\\eta\\ge0$ and $\\theta_\\eta\\in(0,1/2]$'),
       ('chapter_not_note','W8','is descriptive terminology in this note,','is descriptive terminology in this chapter,'),
       ('point_to_later_sufficient_classes','W21','These identities explain the breadth of the preceding sufficient classes',
        'These identities explain the breadth of the sufficient classes of Section~4.6'),
       ('name_seed_parameters_by_chapter','W22','The positivity of $\\delta$ follows from the certified D parameters.',
        "The positivity of $\\delta$ follows from Chapter~\\ref{comp:D}'s certified parameters."),
       ('name_seed_optimizer_by_chapter','W22','The unique D optimizer $(-1,16)$',
        "Chapter~\\ref{comp:D}'s unique optimizer $(-1,16)$"),
       ('name_seed_run_by_chapter','W22','let $x_k,g_k,H_k,\\alpha_k$ be the verified D run.',
        'let $x_k,g_k,H_k,\\alpha_k$ be the verified run of Chapter~\\ref{comp:D}.'),
       ('name_seed_curvatures_by_chapter','W22','The actual positive secant curvatures are $a$ times those of D and',
        'The actual positive secant curvatures are $a$ times those of the run of Chapter~\\ref{comp:D} and'),
       ('name_convergence_theorem_of_chapter_t','W21',
        'A low compact sublevel is trapped there, and the preceding convergence theorem applies.',
        'A low compact sublevel is trapped there, and the convergence theorem of Chapter~\\ref{comp:T} (Theorem 3.1, through Section 3.4 and its local form in Section 3.3.2) applies.'),
       ('state_varying_gradient_jump','W23',
        'different cells can have different quadratic Hessians and different gradient jumps.',
        'different cells can have different quadratic Hessians, and the gradient jump can vary along a cell boundary (for example $u^2+v^2+(2+|u|)|v|$ near the origin).'),
       ('drop_absent_segment_proof','W21','This proves (IR) directly, shortening the earlier segment-based proof.',
        'This proves (IR) directly.'),
       ('name_radial_secant_necessity','W21','The necessity for the old radial condition is also clear',
        'The necessity for (RS) is also clear'),
       ('name_radial_secant_on_neighborhoods','W21',
        'need not satisfy the original local radial criterion at a nonzero rank-deficient minimizer.',
        'need not satisfy (RS) on any neighborhood of a nonzero rank-deficient minimizer.'),
       ('name_radial_secant_condition','W8R','The preceding report assumes the following positive-band condition:',
        'The radial secant condition is the following positive-band condition:')],
  'G':[('name_one_sided_convergence_theorem','M21','The preceding theorem says that this condition implies',
        'The one-sided transported-certificate convergence theorem of Chapter~\\ref{comp:T} says that this condition implies'),
       ('name_proof_using_expansion_budget','W11','was useful in the proof, but is not essential',
        'was useful in the proof of the convergence theorem of Chapter~\\ref{comp:T}, but is not essential'),
       ('no_certificate_on_sublevels_with_zero_inside','M22','but no global certificate on a sublevel containing zero.',
        'but, for $(c_1,c_2)=(1/4,1/2)$, no global certificate on any sublevel containing zero in its interior.'),
       ('state_positive_epsilon','W16','For $x=\\epsilon$, $z=-\\epsilon/2$,',
        'For $x=\\epsilon$, $z=-\\epsilon/2$ with $\\epsilon>0$,'),
       ('knot_in_interior_of_band','M23','No certificate exists on a positive band containing this knot.',
        'No certificate exists on a positive band whose interior contains this knot ($b>h(a)>\\eta$).'),
       ('name_two_conditions_in_proof','W17G','If $C>0$ and $W$ satisfies (V)--(S),','If $C>0$ and $W$ satisfies (V) and (S),'),
       ('name_two_conditions_in_rank_remark','W17G','adds no pointwise power to (V)--(S);','adds no pointwise power to (V) and (S);')],
  'F':[('drop_unresolved_source_labels','M27',
        'This module collects the nonredundant structural consequences from [M], [P], [E] and [Q].',
        'This chapter collects nonredundant structural consequences of the general theory.'),
       ('cite_superquadratic_theorem_for_rates','W25',
        'The source rate note recorded big-$O$ bounds. The little-$o$ versions below are explicit consolidation deductions from the later superquadratic theorem; they do not assert a sharp rate.',
        'Big-$O$ versions of these rates appeared in the source notes. The little-$o$ versions below follow from Theorem~\\ref{M:superquadratic}; they do not assert a sharp rate.'),
       ('state_bounded_gradients_of_rate','W24',
        '=o(N^{-1/2}),\n\\]\nbecause $S_N/N^2\\to\\infty$.',
        ',\n\\]\nand along runs with bounded gradients this is $o(N^{-1/2})$, because $S_N/N^2\\to\\infty$.'),
       ('drop_source_bounds_remnant','W25','Summing first recovers the source bounds','Summing first gives the bounds'),
       ('drop_earlier_route_remnant','W25',
        'This is the proved tilted-minimum construction, replacing the earlier first-right-derivative-threshold route.',
        'This is the proved tilted-minimum construction.')],
  'H':[('chapter_not_note','W8','This note continues the investigation','This chapter continues the investigation'),
       ('earlier_source_note','W8H','This potential inequality was established in the earlier note.',
        'This potential inequality was established in an earlier source note.'),
       ('name_chapter_of_stagnation_example','W10H','The earlier three-gradient, rank-two stagnation example attains this',
        'The three-gradient, rank-two stagnation example of Chapter~\\ref{comp:D} attains this'),
       ('state_common_tilt_run_existence_boundary','M42',
        'not a proof of finite termination for every many-piece objective.',
        'not a proof of finite termination for every many-piece objective.\n\n'
        'Existence of an infinite admissible run is a separate issue. Under\n'
        '\\(0\\notin\\operatorname{aff}\\{a_1,\\ldots,a_m\\}\\), no such run exists\n'
        'in ambient dimension at most two. For the displayed common-tilt family,\n'
        'no such run exists in any dimension when the tangential slopes are collinear:\n'
        '\\(b_i=c+\\beta_i d\\) for fixed \\(c,d\\), including at most two distinct \\(b_i\\).\n'
        'These cases reduce to a linear objective or the maximum of two independent\n'
        'linear forms, whose infinite admissible runs are excluded by the two-piece\n'
        'analysis discussed in Section~\\ref{H:connection-to-the-two-piece-paper}.\n'
        'For noncollinear families in higher dimension, existence of such a run\n'
        'remains open here.')],
  'A':[('drop_self_citation','W5',
        'This module preserves the geometric propositions of the affine-criticality note~Chapter~\\ref{comp:A}.',
        'This chapter preserves the geometric propositions of the original affine-criticality note.'),
       ('drop_self_citation_of_references','W5','the references~\\cite{BDLS}; Chapter~\\ref{comp:A} supply',
        'the references~\\cite{BDLS} supply')],
  'C':[('name_chapter_of_conjecture','W8','recorded in the previous note~Chapter~\\ref{comp:A}.','recorded in Chapter~\\ref{comp:A}.'),
       ('chapter_not_note','W8','the missing algorithmic assertion is the subject of this note.',
        'the missing algorithmic assertion is the subject of this chapter.'),
       ('state_supposition_for_contradiction','W14',
        'We will argue by contradiction that the compact cluster set $\\Gamma$ contains no affine-critical point.',
        'We suppose, for a contradiction, that the compact cluster set $\\Gamma$ contains no affine-critical point.'),
       ('state_range_of_cutoffs','W15','smooth angular cutoffs $\\chi_j$ with disjoint supports',
        'smooth angular cutoffs $0\\le\\chi_j\\le1$ with disjoint supports'),
       ('name_low_affine_critical_gap','M20',"Combining A's low affine-critical gap with Theorem~\\ref{C:thm:cluster}",
        'Combining the low affine-critical gap of Proposition~\\ref{A:semialgebraic} with Theorem~\\ref{C:thm:cluster}')],
  'Q':[('name_transported_certificate_theorem','W26','This is a concrete application of the objective-pair theorem,',
        'This is a concrete application of the transported-certificate theorem of Chapter~\\ref{comp:T},'),
       ('name_secant_condition_of_chapter_t','W26','Multiplication by $\\theta(z)^2$ proves (S).',
        'Multiplication by $\\theta(z)^2$ proves (S) of Chapter~\\ref{comp:T}.'),
       ('name_general_theorem','W26','The general theorem proves convergence',
        'The transported-certificate theorem of Chapter~\\ref{comp:T} proves convergence')],
  'U':[('number_theorem_references','M18','covers Theorems 1 and 2.','covers Theorems 11.1 and 11.2.'),
       ('number_tangential_reference','M18','follows from (11).','follows from (11.11).'),
       ('name_transport_hypothesis','M18','Thus (6) holds with \\(T=I\\) and',
        'Thus (11.14) is the transport hypothesis of Theorem~\\ref{M:residualtheorem}, with \\(T=I\\), rank-one term \\(s(\\beta e_n)^T\\) and'),
       ('number_replaced_reference','M18','This replaces (11).','This replaces (11.11).'),
       ('number_cutoff_frame_references','M18','Equations (16)--(17)','Equations (11.16)--(11.17)'),
       ('number_curvature_divergence_reference','M18','bound the left side of\n(21).','bound the left side of\n(11.21).'),
       ('number_series_reference','M18','truncate (18).','truncate (11.18).'),
       ('number_objective_reference','M18','For the objective (20),','For the objective (11.20),'),
       ('state_range_of_spike_bounds','M19','\\] near zero. However,','\\] for \\(v\\ge0\\). However,'),
       ('name_source_notes','W8','cases were already proved in earlier notes.','cases were already proved in the source notes.'),
       ('name_section_of_nonsplitting_conclusion','W10','The later nonsplitting conclusion',
        'The nonsplitting conclusion of Section~\\ref{U:the-objective-need-not-split-as-a-smooth-function-plus-one-scalar-penalty}'),
       ('name_affine_criticality_chapter','W11','The method also fits the affine-criticality program directly.',
        'The method also fits the affine-criticality program of Chapter~\\ref{comp:A} directly.'),
       ('cite_radial_equivalence_theorem','W11','The recorded equivalence between inward radial',
        'The equivalence of Theorem~\\ref{R:thm:equiv} between inward radial'),
       ('name_chapter_of_conjecture','W11','rather than settling the original arbitrary\ncurved finite-\\(C^2\\)-max conjecture.',
        'rather than settling the original arbitrary\ncurved finite-\\(C^2\\)-max conjecture of Chapter~\\ref{comp:A}.'),
       ('cite_polyhedral_partition_theorem','W11','the older\nfinite-polyhedral-partition theorem already gave local convergence.',
        'the\nfinite-polyhedral-partition Theorem~\\ref{R:thm:plq} already gives local convergence.')],
  'D':[('drop_history_of_admissible_lengths','W7',
        'Thus the construction resolves the implementation-selection issue left open by the previous admissible-length counterexample.',
        'Thus the construction resolves the implementation-selection issue.'),
       ('chapter_not_note','W8','All denominators in this note are nonzero there','All denominators in this chapter are nonzero there'),
       ('fourth_branch_is_analytic','M14','This does not make them analytic or uniformly strongly convex.',
        'This does not make the first three branches analytic, nor any branch uniformly strongly convex.'),
       ('continue_equation_numbering_before_single_objective','W46','\\setcounter{equation}{8}','\\setcounter{equation}{11}'),
       ('continue_equation_numbering_before_rejected_trials','W46','\\setcounter{equation}{10}','\\setcounter{equation}{13}')],
  'L':[('describe_step_version_without_denial','M12',
        '; the latter version has a countable polyhedral nonsmooth part, not a finite smooth-branch representation.',
        '; the latter version has a countable polyhedral nonsmooth part.'),
       ('small_orbit_includes_initial_point','RF1','so that \\emph{all queries of the orbit} lie inside it.',
        'so that \\emph{the initial point and all queries of the orbit} lie inside it.'),
       ('chosen_orbit_includes_initial_point','RF1','whose accepted and rejected queries are all in that neighborhood.',
        'whose initial point and accepted and rejected queries are all in that neighborhood.'),
       ('local_model_at_initial_point','RF1','applies to every query by the choice of the whole seed orbit.',
        'applies at the initial point and to every query by the choice of the whole seed orbit.'),
       ('state_admissible_family_of_chapter','M13',
        "This chapter uses the fixed line-search pair displayed in this chapter; D's wider parameter family is not imported.",
        'Like Chapter~\\ref{comp:D}, the chapter covers every pair $0<c_1\\le1/3$, $c_1<c_2<1$.'),
       ('chapter_not_report','W8L','certified in the preceding deterministic-bracketing report~Chapter~\\ref{comp:D}.',
        'certified in Chapter~\\ref{comp:D}.'),
       ('drop_drafting_remnant','W44',"the user's literal classical-Hessian assumption",'the literal classical-Hessian assumption'),
       ('continue_equation_numbering_before_step_variant','W46','\\setcounter{equation}{8}','\\setcounter{equation}{13}'),
       ('continue_equation_numbering_before_scaled_copies','W46','\\setcounter{equation}{7}','\\setcounter{equation}{12}'),
       ('continue_equation_numbering_before_embedding','W46','\\setcounter{equation}{4}','\\setcounter{equation}{7}'),
       ('continue_equation_numbering_before_hyperbolic_fixed_point','W46','\\setcounter{equation}{2}','\\setcounter{equation}{5}'),
       ('first_three_branches_at_minimizer','M30',
        'fail to be twice differentiable at the accumulation point.',
        'fail to be twice differentiable at the minimizer.')],
  'E':[('name_lower_curvature_chapter','M29','The stable-manifold conclusion in L follows',
        'The stable-manifold conclusion in Chapter~\\ref{comp:L} follows'),
       ('describe_suite_labels','W29','The labels below preserve correspondence with the original report.',
        "The labels below are the original report's suite names, whose letters are not chapter letters; they preserve correspondence with that report."),
       ('state_bounded_gradients_of_hierarchy','W28','The actual full-matrix hierarchy yields the normalized hierarchy',
        'Along runs with bounded gradients, the actual full-matrix hierarchy yields the normalized hierarchy'),
       ('name_radial_modeling_chapter','M29','The explicit four-piece objective in R is',
        'The explicit four-piece objective in Chapter~\\ref{comp:R} is'),
       ('state_basin_and_tolerances_of_planar_example','W27',
        'the stated planar example converges, and hence every positive displayed tolerance is eventually attained.',
        'the stated planar example converges from its basin~\\eqref{C:eq:explicitbasin}, and hence every positive tolerance on its objective value is eventually attained.'),
       ('every_positive_tolerance','W27','eventual attainment of the printed positive tolerance',
        'eventual attainment of every positive tolerance'),
       ('describe_audit_readme','W30','Its README describes the read-only evidence check and the exact default output path.',
        'Its README describes the read-only evidence check; the runner prints the new timestamped output directory.')]}
 for kind,item,old,new in corrections.get(module,[]):
  assert text.count(old)==1,(module,kind)
  text=text.replace(old,new)
  transform_log.append({'module':module,'kind':kind,'reason':why[item]})
 if module=='E':
  heading=r'\section{Rebuild the corrected report}'
  assert text.count(heading)==1
  text=text.replace(heading,'\\needspace{6\\baselineskip}\n'+heading)
  transform_log.append({'module':module,'kind':'keep_rebuild_heading_with_commands','reason':'Visual review after the 13 October 2026 verification paragraph found this heading and its first line separated from the command block. needspace changes layout only.'})
 for edit in (e for e in m44_edits if e['module']==module):
  assert text.count(edit['old'])==1,(module,edit['id'])
  text=text.replace(edit['old'],edit['new'])
  transform_log.append({'module':module,'kind':'m44_'+edit['kind'],'id':edit['id'],'reason':'M44 in TODO_MANUSCRIPT_REVIEW.md: '+edit['reason']})
 intro='\\chapter{'+title+'}\\label{comp:'+module+'}\\label{'+module+':chapter}\n\\renewcommand{\\ModuleTag}{'+number[module]+'}\n'+introductions[module]+'\n\n'
 if module=='E':intro+='\\input{current_verification}\n'
 content=intro+text
 out=OUT/'chapters'/f'{number[module].zfill(2)}_{module}.tex';outputs[out]=content
 chapter_inputs.append('\\input{chapters/'+out.name+'}')
 for c in group:
  start_marker='% SOURCE_BEGIN '+c['id']+'\n';end_marker='% SOURCE_END '+c['id']+'\n'
  assert content.count(start_marker)==content.count(end_marker)==1,c['id']
  start=content.index(start_marker);end=content.index(end_marker)
  exports=c['exports'];assert all(n in index for n in exports)
  labels=re.findall(r'\\label\{([^}]+)\}',content[start:end])
  rows.append({'editorial_id':'source.'+c['id'],'source_span':c['id'],'source_module':module,'source_file':str(path.relative_to(ROOT)),'source_sha256':hashlib.sha256(original.encode()).hexdigest(),'source_corrected_lines':c['corrected_line_ranges'],'source_classification':c['classification'],'companion_file':str(out.relative_to(ROOT)),'companion_lines':[content[:start].count('\n')+1,content[:end].count('\n')+1],'companion_chapter':number[module],'statement_labels':labels,'formal_exports':exports,'formal_status':'Inherited exact Lean contracts with retained mathematical statements; prose correspondence reviewed separately' if exports else 'Scope, definition, editorial or execution record; not an additional proved theorem','correspondence':'Original mathematical body retained under explicit editorial transformations; all source-span exports included, never only the sample coverage export','disposition':'retained','article_status':'see article contract ledger when authored'})
outputs[OUT/'contents.tex']='\n'.join(chapter_inputs)+'\n'
outputs[OUT/'SOURCE_CORRESPONDENCE.json']=json.dumps({'schema_version':1,'scope':'Full original-span correspondence; not a claim that natural language is parsed by Lean','rows':rows,'transformations':transform_log},indent=2)+'\n'
outputs[ROOT/'editorial/SUPERSESSION_LEDGER.json']=json.dumps({'policy':'No source result omitted. Earlier supersessions remain explicit in the retained inventory; incomparable statements stay separate.','entries':[{'source_span':r['source_span'],'classification':r['source_classification'],'disposition':'retained','retained_location':r['companion_file'],'chapter':r['companion_chapter'],'formal_exports':r['formal_exports']} for r in rows]},indent=2)+'\n'
if args.check:
 mismatches=[str(path.relative_to(ROOT)) for path,text in outputs.items() if not path.is_file() or path.read_bytes()!=text.encode('utf-8')]
 extras=sorted(str(path.relative_to(ROOT)) for path in (OUT/'chapters').glob('*.tex') if path not in outputs)
 print(json.dumps({'status':'FAIL' if mismatches or extras else 'PASS','mode':'read_only_regeneration_check','source_commit':baseline['source_commit'],'source_sha256_guard':'PASS','chapters':len(order),'source_spans':len(rows),'unique_formal_exports':len(set(n for r in rows for n in r['formal_exports'])),'managed_outputs':len(outputs),'missing_or_changed_outputs':mismatches,'unexpected_chapter_outputs':extras},indent=2))
 sys.exit(1 if mismatches or extras else 0)
for path,text in outputs.items():
 path.parent.mkdir(parents=True,exist_ok=True)
 path.write_bytes(text.encode('utf-8'))
print('Generated',len(order),'thematic chapters;',len(rows),'source spans;',len(set(n for r in rows for n in r['formal_exports'])),'full formal exports; frozen source SHA256 guard PASS.')
