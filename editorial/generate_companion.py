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
order=[('I','Scope, quantifiers and the result map'),('M','The common BFGS algebra and reciprocal budgets'),('T','Transported comparison energies'),('R','Radial modeling and finite partitions'),('G','What comparison certificates express'),('F','Concrete objectives, lifting and rates'),('H','Homogeneous objectives without compactness'),('A','Affine criticality and stratified geometry'),('C','Planar switching and affine-critical cluster points'),('Q','Flat contours and parabolic branches'),('U','Fixed normal geometry in arbitrary dimension'),('D','The exact deterministic seed and local smooth embedding'),('L','Failure with positive lower curvature'),('E','Formal correspondence and the evidence boundary')]
number={m:str(i+1) for i,(m,_) in enumerate(order)}
internal={'SM':'M','SH':'H','ST':'T','SG':'G','SR':'R','SL':'R','SP':'F','SQ':'F','SE':'F','SV':'M','SA':'A','SC':'C','SU':'U','SD':'D','SLC':'L'}
introductions={
'I':'The scope map separates objective convergence, convergence to the solution set and convergence of the full sequence. It also separates universal admissible-run statements from the particular deterministic executions used in the counterexamples.',
'M':'The same matrix calculation supports every positive result in this volume. We establish it once for actual full BFGS matrices, then retain the distinct qualitative, finite-horizon and summable-budget consequences.',
'T':'The reciprocal budget becomes an objective theorem only when geometry controls a comparison energy. Visibility, secant control and transport are imposed on objective-level pairs, not inferred from a presumed limit of the BFGS matrices.',
'R':'A fixed comparison direction toward an optimizer gives a concrete modeling condition. Its inward formulation explains both local finite partitions and familiar centered nonsmooth terms.',
'G':'The certificate is a sufficient analytic condition. Its normalization and pointwise geometry help interpret it, while scalar examples separate failure of the condition from failure of BFGS.',
'F':'These applications turn the common analytic mechanism into verifiable objective classes. The affine-fiber selection formula and quantitative conclusions retain their own initialization and budget hypotheses.',
'H':'Homogeneity permits a different potential even without compact sublevels. The value dichotomy, recurrent-gradient obstructions and low-effective-rank iterate conclusions must therefore be retained separately from the compact-band theory.',
'A':'Affine balance concerns equal-rate descent, whereas convex balance concerns stationarity. This distinction gives useful local geometry but does not by itself force an algorithm to visit it.',
'C':'The plane allows a comparison direction to be joined along a regular positive contour. The corrected determinant orientation and one-sided transport argument are essential to the conclusion.',
'Q':'Flat contour segments are allowed in this finite parabolic family. Its explicit field supplies a convergence theorem that is not contained in the strict-contour planar result.',
'U':'A fixed space of jump normals leaves controlled smooth directions in arbitrary dimension. Residual transport can be paid for in those directions; this is a different hypothesis from planar switching geometry.',
'D':'A finite algebraic cycle first determines every query of a specified line search. Scaled copies then produce one fixed convex objective with failing initial points approaching its optimizer.',
'L':'Positive lower curvature requires a separate construction. The local finite-branch functions have Lipschitz gradients but lose second differentiability at the accumulation point; no claim combines uniform strong convexity with the preceding local C2,1 branch regularity.',
'E':'Mathematical proof, formal statement correspondence, computation and historical execution are different kinds of evidence. The current authoring audit is stated first; the preserved release record that follows is historical evidence, not a new run count.'}
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
  text+='\n\\section*{Relation to earlier work}\nThe following comparisons are bibliographic scholarship, separate from the formal theorem assertions.\n\n'+'\n\n'.join(notes)+'\n'
 def cite(m):
  keys=[k.strip() for k in m[2].split(',')];ext=[k for k in keys if k not in internal];refs=list(dict.fromkeys(internal[k] for k in keys if k in internal));parts=[]
  if ext:parts.append('\\cite'+(m[1] or '')+'{'+','.join(ext)+'}')
  if refs:parts.append('Chapter'+('s' if len(refs)>1 else '')+'~'+', '.join('\\ref{comp:'+x+'}' for x in refs))
  return '; '.join(parts)
 text=re.sub(r'\\cite(\[[^\]]*\])?\{([^}]+)\}',cite,text)
 # Source theorem tags are retained with their chapter number replacing the module letter.
 for m,num in number.items():
  text=re.sub(r'\b'+m+r'\.(?=[0-9A-Z])',num+'.',text)
  text=re.sub(r'\bModule~? '+m+r'\b',r'Chapter~\\ref{comp:'+m+'}',text)
  text=re.sub(r'\bModule~'+m+r'\b',r'Chapter~\\ref{comp:'+m+'}',text)
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
