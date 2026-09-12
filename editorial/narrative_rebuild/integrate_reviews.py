#!/usr/bin/env python3
"""Integrate reviewed narrative contracts with the unchanged analytical core."""
from pathlib import Path
import copy, datetime, hashlib, json, re, sys, subprocess
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'editorial'))
from active_tex_sources import sources
def read(p): return json.loads((ROOT/p).read_text())
def save(p,d): (ROOT/p).write_text(json.dumps(d,indent=2)+'\n')
def sha(p): return hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
texts={str(p.relative_to(ROOT)):p.read_text() for p in sources(ROOT)}
def locate(anchor,path=None):
 hits=[(p,t.index(anchor)) for p,t in texts.items() if (not path or p==path) and anchor in t]
 assert len(hits)==1,(anchor,hits)
 p,i=hits[0];return {'path':p,'line':texts[p][:i].count('\n')+1}
prior=read('editorial/narrative_rebuild/prior_records/positive_contract_review.json')
new=read('editorial/narrative_rebuild/positive_contract_review.json')
core={'paper/sections/energy.tex','paper/appendices/matrix_algebra.tex'}
rows=[]
for r in prior['statements']:
 if r['article_location']['path'] not in core: continue
 r=copy.deepcopy(r);p=r['article_location']['path'];t=texts[p]
 offset=t.index('\\label{'+r['label']+'}')
 begins=list(re.finditer(r'\\begin\{(theorem|lemma|corollary|proposition|definition)\}',t[:offset]))
 begin=begins[-1];end=t.index('\\end{'+begin[1]+'}',offset)+len('\\end{'+begin[1]+'}')
 historical=subprocess.check_output(['git','show','7f53b4cafd6bf98c24d7d45883a8f8d983571149:'+p],cwd=ROOT,text=True)
 hi=historical.index('\\label{'+r['label']+'}')
 hb=list(re.finditer(r'\\begin\{(theorem|lemma|corollary|proposition|definition)\}',historical[:hi]))[-1]
 he=historical.index('\\end{'+hb[1]+'}',hi)+len('\\end{'+hb[1]+'}')
 assert historical[hb.start():he]==t[begin.start():end],r['label']
 r['article_statement']=t[begin.start():end]
 r['article_location']=locate('\\label{'+r['label']+'}',p)
 r['review_note_narrative']='Statement unchanged byte-for-byte from the reviewed preceding edition; full proof reread during narrative integration. Updated exposition precedes the matrix hierarchy and motivates certificate assumptions.'
 rows.append(r)
eq=[]
for r in prior['equation_mappings']:
 if r['article_location']['path'] not in core: continue
 r=copy.deepcopy(r);r['article_location']=locate('\\label{'+r['label']+'}',r['article_location']['path']);eq.append(r)
new['statements']=rows+new['statements'];new['equation_mappings']=eq+new['equation_mappings']
for r in new['statements']:
 if r['kind']=='definition':
  r['proof_location']={'kind':'definition_not_a_proved_claim',**r['article_location']};continue
 p=r['article_location']['path']
 if r['label']=='art:polyhedral':
  p='paper/sections/local.tex';t=texts[p];start=t.index('\\begin{proof}[Proof of Theorem~\\ref{art:polyhedral}]')
 else:
  t=texts[p];offset=t.index('\\label{'+r['label']+'}');start=t.index('\\begin{proof}',offset)
 end=t.index('\\end{proof}',start)
 r['proof_location']={'path':p,'line':t[:start].count('\n')+1,'end_line':t[:end].count('\n')+1,'scope':'Complete local proof block; cited article lemmas and appendices have their own full mapped proof locations.'}
new['article_files']=sorted(set(new['article_files'])|core)
new['article_sha256']={p:sha(p) for p in new['article_files']}
new['analytical_core_prior_review']='editorial/narrative_rebuild/prior_records/positive_contract_review.json'
declaration_index=read('bfgs_lean_stage1/master_report/DECLARATION_INDEX.json')
source_claims={r['id']:r for r in read('bfgs_lean_stage1/master_report/CLAIMS.json')['claims']}
span_ids=sorted({s for r in new['statements']+new['unnumbered_mathematical_deductions'] for s in r['source_span_ids']})
new['full_source_span_register']=[{k:source_claims[s][k] for k in ['id','module','corrected_source','corrected_line_ranges','classification','exports','review_note'] if k in source_claims[s]} for s in span_ids]
pending=[n for s in span_ids for n in source_claims[s]['exports']];roots=set(pending);closure=set()
while pending:
 n=pending.pop()
 if n in closure:continue
 d=declaration_index[n];closure.add(n)
 assert not d['unsafe'] and not d['partial'] and set(d['axioms'])<={'propext','Classical.choice','Quot.sound'},n
 for key in ['value_project_dependencies','type_project_dependencies','structural_project_dependencies']:pending.extend(d[key])
new['formal_project_dependency_closure']=sorted(closure)
new['formal_dependency_audit']['selected_project_roots']=len(roots)
new['formal_dependency_audit']['transitive_project_declarations']=len(closure)
new['proof_completeness_review']['labeled_mathematical_statements']=len(new['statements'])
new['proof_completeness_review']['labeled_equations']=len(new['equation_mappings'])
for s in span_ids:
 p='bfgs_lean_stage1/master_report/'+source_claims[s]['corrected_source'];new['source_sha256'][p]=sha(p)
new['status']='INTEGRATED_MATHEMATICAL_CORRESPONDENCE_REVIEW_COMPLETE; final build and visual evidence separate'
save('editorial/positive_contract_review.json',new)
save('editorial/negative_contract_review.json',read('editorial/narrative_rebuild/negative_contract_review.json'))

root=read('editorial/narrative_rebuild/prior_records/root_contract_review.json')
old={r['id']:r for r in root['records']}
claims={r['id']:r for r in read('bfgs_lean_stage1/master_report/CLAIMS.json')['claims']}
index=read('bfgs_lean_stage1/master_report/DECLARATION_INDEX.json')
index.update({d['name']:d for d in root['supplemental_declarations']})
for supplement in read('editorial/narrative_rebuild/FORMAL_SUPPLEMENTS.json')['supplements']:
 index.update({d['name']:d for d in read(supplement['declarations'])})
def all_exports(spans): return sorted({n for s in spans for n in claims[s]['exports']})
records=[]
def row(id,path,anchor,spans,primary,note,kind='article_deduction'):
 if path.startswith('companion/') and path not in texts:texts[path]=(ROOT/path).read_text()
 assert all(n in index for n in primary)
 records.append({'id':id,'kind':kind,'article_location':locate(anchor,path),'anchor':anchor,
 'source_span_ids':spans,'all_source_span_exports':all_exports(spans),'primary_declarations':primary,
 'scope_review':note,'status':'REVIEWED_WITH_EXACT_FORMAL_SUPPORT'})
row('root.abstract.three_contributions','paper/master.tex','Ordinary full BFGS often succeeds on nonsmooth objectives,',
 ['R.span.8','F.span.1','H.span.9','C.span.11','C.span.13','C.span.14','D.span.2','L.span.2','M.span.2','M.span.4','T.span.3'],[],
 'Abstract summarizes the actual independently proved article theorem set: compact-centered and coercive homogeneous global families, finite-cell and genuinely nonradial planar local classes, distinct finite-branch local failures, and the actual-matrix mechanism. No complete boundary, matrix asymptotics, generic failure or C2 uniformly strongly convex local negative is asserted. Exact contracts are in the positive and negative component records.', 'canonical_statement_pointer')
row('root.introduction.headlines','paper/sections/introduction.tex','We give three answers:',
 ['R.span.8','F.span.1','H.span.9','C.span.11','C.span.13','C.span.14','D.span.2','L.span.2'],
 ['ArticlePositive.mixed_benchmark_global'],
 'Intro now states three coequal answers before the lineage. Later contribution paragraphs retain all structural/compactness/locality qualifications and canonical theorem cross-references; actual literal all-run benchmark has its own audited wrapper. Literature/novelty and Challenge7.1 paraphrases are assessed separately in literature_primary_review.json.','canonical_statement_pointer')
row('root.introduction.mechanism','paper/sections/introduction.tex','We prove a hierarchy linking adjacent degrees',
 ['M.span.2','M.span.3','M.span.4','T.span.3','E.span.12'],old['root.introduction.mechanism']['primary_declarations'],
 'The arithmetic mean of reciprocals diverges under bounded gradients and vanishing predicted decreases. These follow on compact sublevels for article applications. This is not pointwise q convergence or a metric limit.')
for id,anchor in [('root.geometry.mixed_ridge','The mixed ridge $F(u,v)=u^2+|v|$'),('root.geometry.seed_balance','The right panel asks a different question:'),('root.geometry.affine_convex_balance','This distinction between affine and convex balance')]:
 r=old[id];row(id,'paper/sections/geometry.tex',anchor,r['source_span_ids'],r['primary_declarations'],r['scope_review'])
row('art:positive-outcomes','paper/sections/geometry.tex','\\label{art:positive-outcomes}',
 ['R.span.8','F.span.1','R.span.10','H.span.9','C.span.11'],['ArticlePositive.mixed_benchmark_global'],
 'Scope table is a precise summary of the separately mapped family statements. Every row retains infinite actual-run quantifier, arbitrary SPD initialization, stated compactness/structural basin, and uniqueness where used. Global homogeneous row is coercive linear homogeneity, not a general affine maximum.','table_summary')
row('root.geometry.local_global','paper/sections/geometry.tex','The first two rows make precise global assertions;',
 ['H.span.9','D.span.6','D.span.7','R.span.8','C.span.13','C.span.14'],[],
 'General affine offsets admit the separately proved global wrong-corner example; homogeneous coercive objectives have unique minimum0. Finite incident polyhedral cells give inward models, while actual curved planar example violates radial secants. Geometry is interpretation of those proofs, not classification by jumps.')
row('root.energy.budget_interpretation','paper/sections/energy.tex','The identity makes the intended contradiction visible.',
 ['M.span.4','F.span.1'],[],
 'Persistent gap eta>0 and uniformly bounded R yield eta² sum1/q≤E0+CN by the proved reference-energy identity. Matrix hierarchy contradicts this with bounded gradients and d→0. No uniform bound on B or limiting H is used.')
row('root.energy.companion_quantitative','paper/sections/energy.tex','Finite-horizon bounds',
 ['M.span.3','M.span.4'],['BfgsVerification.superquadraticReciprocalGrowth'],
 'Finite-horizon and summable-budget superquadratic versions remain complete separate companion Chapter2 results; article qualitative assumption d→0 is retained rather than silently strengthened.')
row('root.energy.nonnecessity','paper/sections/energy.tex','The certificate is a sufficient convergence mechanism.',
 ['G.span.9','G.span.10','T.span.7','R.span.15'],old['root.beyond.nonnecessity']['primary_declarations'],
 'Nonnecessity is explicitly companion-only (Ch5/7). Scalar convergence and nonexistence of this comparison certificate remain distinct assertions. Full nonradial example is now proved in this article rather than listed as a companion orientation.')
row('root.synthesis.mathematical_scope','paper/sections/verification.tex','The mixed quadratic--absolute-value benchmark',
 ['F.span.1','H.span.9','R.span.8','C.span.11','C.span.13','C.span.14','D.span.2','L.span.2','M.span.2','T.span.3'],
 ['ArticlePositive.mixed_benchmark_global'],
 'Synthesis matches abstract and proved theorem set. It distinguishes compact-centered, coercive homogeneous, finite local cells and moving planar geometry, and the two incomparable local negative regularity regimes. No probability or complete spectral classification is claimed.')
for id,anchor,spans,note in [
 ('companion.story.positive','The centered smooth--sublinear result here proves', ['F.span.1','R.span.10','R.span.8','H.span.3','H.span.9','H.span.12','C.span.11','C.span.13','C.span.14'], 'Frontmatter summarizes strongest retained classes with compactness, centered representation and whole-iterate uniqueness conditions. Homogeneous noncompact value results remain separate from compact iterate conclusions and XW finite escape.'),
 ('companion.story.negative','The negative results establish a complementary limitation.', ['D.span.2','D.span.7','D.span.8','D.span.9','L.span.2','L.span.6','L.span.7'], 'Both fixed-objective local counterexamples retain identity initialization, arbitrarily close starts, nonstationary limits and all-query family locality. No merged C2/lower-curvature claim.'),
 ('companion.story.mechanism','The common analytical tool is an adjacent-degree hierarchy', ['M.span.2','M.span.3','M.span.4','T.span.3','G.span.9','G.span.10'], 'Actual BFGS/minors, bounded-gradient vanishing-decrease reciprocal growth, and sufficient visibility/secant/transport mechanism. Scalar nonnecessity prevents reading this as complete characterization.')]:
 row(id,'companion/research_story.tex',anchor,spans,[],note,'companion_frontmatter_deduction')
root['records']=records
root['article_file_sha256']={p:sha(p) for p in sorted({r['article_location']['path'] for r in records})}
root['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
root['status']='NARRATIVE_CORRESPONDENCE_REVIEW_COMPLETE; unchanged prior geometry audit plus fresh registered narrative supplements'
root['revision_baseline_commit']='7f53b4cafd6bf98c24d7d45883a8f8d983571149'
root['superseded_prose_records']='editorial/narrative_rebuild/prior_records/root_contract_review.json'
root['narrative_supplement_register']='editorial/narrative_rebuild/FORMAL_SUPPLEMENTS.json'
root['scholarly_scope']='Research lineage before theorem inventory; global benchmark and nonradial payoff explicit. Existing Euclidean norm and finite two-piece escape attributed. Primary-source verification and unresolved novelty limits recorded separately.'
save('editorial/root_contract_review.json',root)
print('Integrated',len(new['statements']),'positive/core statements,',len(new['equation_mappings']),'equations,',len(records),'root narrative records.')
