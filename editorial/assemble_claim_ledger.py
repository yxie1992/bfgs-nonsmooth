#!/usr/bin/env python3
"""Assemble full per-statement correspondences, preserving exact source exports."""
from pathlib import Path
import hashlib,json,re,html
from companion_statement_inventory import build as companion_inventory
from active_tex_sources import sources as active_sources
ROOT=Path(__file__).resolve().parents[1]
def read(p):return json.loads((ROOT/p).read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
claims={r['id']:r for r in read('bfgs_lean_stage1/master_report/CLAIMS.json')['claims']}
index=read('bfgs_lean_stage1/master_report/DECLARATION_INDEX.json')
article_sources=active_sources(ROOT)
supplement_register=read('editorial/narrative_rebuild/FORMAL_SUPPLEMENTS.json')
branch_supplement=read('editorial/root_contract_review.json')['supplemental_branch_regularity_audit']
for supplement in supplement_register['supplements']+[branch_supplement]:
 audit=read(supplement['summary'])
 assert audit['status']=='PASS' and not audit['unchecked_missing_unsafe_partial']
 assert set(audit['axioms'])<= {'propext','Classical.choice','Quot.sound'}
 for declaration in read(supplement['declarations']):
  assert not declaration['unsafe'] and not declaration['partial'] and declaration['ordinary_collector_agrees']
  index[declaration['name']]=declaration
pos=read('editorial/positive_contract_review.json');neg=read('editorial/negative_contract_review.json')
source=read('companion/SOURCE_CORRESPONDENCE.json')
article=[]
frontmatter=[]
def all_exports(spans):return sorted({n for s in spans for n in claims[s]['exports']})
def where(label):
 found=[]
 for p in article_sources:
  text=p.read_text()
  for m in re.finditer(re.escape('\\label{'+label+'}'),text):
   found.append({'path':str(p.relative_to(ROOT)),'line':text[:m.start()].count('\n')+1,'sha256':sha(p)})
 assert len(found)==1,(label,found)
 return found[0]
for row in pos['statements']+pos['equation_mappings']:
 spans=row['source_span_ids'];label=row['label']
 article.append({'id':label,'kind':row.get('kind','equation'),'location':where(label),'proof_location':row.get('proof_location',row.get('article_location')),'source_spans':spans,'full_formal_exports':sorted(set(all_exports(spans))|set(row.get('primary_declarations',[]))),'principal_exports':row.get('primary_declarations',[]),'exact_contracts':['bfgs_lean_stage1/master_report/DECLARATION_INDEX.json','editorial/narrative_rebuild/FORMAL_SUPPLEMENTS.json'],'review':row.get('hypothesis_and_proof_correspondence',row.get('governing_statement')),'detailed_review':'editorial/positive_contract_review.json','status':'REVIEWED_CORRESPONDENCE_WITH_KERNEL_CHECKED_CONTRACTS'})
for i,row in enumerate(pos['unnumbered_mathematical_deductions']):
 spans=row['source_span_ids'];article.append({'id':'positive.deduction.'+str(i+1),'kind':'unnumbered_mathematical_deduction','location':row['article_location'],'anchor':row['anchor'],'source_spans':spans,'full_formal_exports':all_exports(spans),'review':row,'detailed_review':'editorial/positive_contract_review.json','status':'REVIEWED_CORRESPONDENCE_WITH_KERNEL_CHECKED_CONTRACTS'})
for row in neg['article_labels']:
 spans=row['corrected_spans'];article.append({'id':row['label'],'kind':row['kind'],'location':where(row['label']),'proof_locations':row['proof_locations'],'source_spans':spans,'full_formal_exports':sorted(set(all_exports(spans))|set(row['canonical_exports'])),'principal_exports':row['canonical_exports'],'exact_contracts':['bfgs_lean_stage1/master_report/DECLARATION_INDEX.json','editorial/narrative_rebuild/FORMAL_SUPPLEMENTS.json'],'review':row['review_status'],'detailed_review':'editorial/negative_contract_review.json','status':'ILLUSTRATION_ONLY' if 'illustration' in row['kind'] else 'REVIEWED_CORRESPONDENCE_WITH_KERNEL_CHECKED_CONTRACTS'})
# Every generated theorem environment is matched to containing corrected source spans.
companion=[]
for p in sorted((ROOT/'companion/chapters').glob('*.tex')):
 text=p.read_text();ranges=[]
 for s in source['rows']:
  if s['companion_file']!=str(p.relative_to(ROOT)):continue
  start=text.index('% SOURCE_BEGIN '+s['source_span']);end=text.index('% SOURCE_END '+s['source_span'])
  ranges.append((start,end,s['source_span']))
 for count,m in enumerate(re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary|remark)\}(.*?)\\end\{\1\}',text,re.S),1):
  spans=[s for a,b,s in ranges if a<=m.start()<b];assert spans,(p,m[0][:80])
  labels=re.findall(r'\\label\{([^}]+)\}',m[2]);companion.append({'id':'companion.'+(labels[0] if labels else p.stem+'.'+str(count)),'kind':m[1],'labels':labels,'location':{'path':str(p.relative_to(ROOT)),'line':text[:m.start()].count('\n')+1},'source_spans':spans,'full_formal_exports':all_exports(spans),'exact_contracts':'bfgs_lean_stage1/master_report/DECLARATION_INDEX.json','status':'RETAINED_MATHEMATICS_WITH_REVIEWED_EDITORIAL_TRANSFORMATION'})
manual,inline,unnamed,span_records,companion_coverage=companion_inventory(ROOT,source,claims,companion)
companion.extend(manual)
span_metadata={r['source_spans'][0]:r for r in span_records}
for row in companion:
 if 'source_classification' not in row:
  inherited=span_metadata[row['source_spans'][0]]
  for key in ['source_ids','source_classification','hypothesis_status','definition_status','open_question_status','coverage_policy']:
   row[key]=inherited[key]
  row['status']='RETAINED_NAMED_STATEMENT_UNDER_EXACT_STATED_HYPOTHESES'
for row in article+companion+inline+unnamed+span_records:
 assert all(n in index for n in row['full_formal_exports'])
labels=set(r['id'] for r in article)
missing=[]
for p in article_sources:
 for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary|definition)\}(.*?)\\end\{\1\}',p.read_text(),re.S):
  label=re.search(r'\\label\{([^}]+)\}',m[2]);assert label,(p,m[0][:80])
  if label[1] not in labels:missing.append(label[1])
assert not missing,missing
root_review=ROOT/'editorial/root_contract_review.json'
if root_review.exists():
 root_data=json.loads(root_review.read_text())
 assert root_data['supplemental_audit']['status']=='PASS' and not root_data['remaining_math_obligations']
 for declaration in root_data['supplemental_declarations']:index[declaration['name']]=declaration
 for row in root_data['records']:
  exports=sorted(set(row['all_source_span_exports'])|set(row['primary_declarations']))
  assert all(n in index for n in exports)
  target=frontmatter if row['kind']=='companion_frontmatter_deduction' else article
  target.append({'id':row['id'],'kind':row['kind'],'location':row['article_location'],'anchor':row['anchor'],'source_spans':row['source_span_ids'],'full_formal_exports':exports,'principal_exports':row['primary_declarations'],'review':row['scope_review'],'status':row['status'],'detailed_review':'editorial/root_contract_review.json'})
out={'schema_version':1,'scope':'Exact source-span export sets are conservative unions, not minimal proof bases. Principal exports and expanded contracts in the component reviews govern correspondence. Natural-language correspondence is reviewed separately from kernel checking.','baseline_commit':'00362c0249262d182866f14bac756a7c4edac95c','article_records':article,'companion_theorem_records':companion,'companion_inline_result_records':inline,'companion_unnamed_mathematical_records':unnamed,'companion_source_span_records':span_records,'companion_coverage_audit':companion_coverage,'companion_full_source_span_register':'companion/SOURCE_CORRESPONDENCE.json','companion_shared_appendix':{'canonical_source':'paper/appendices/seed_certificate.tex','transformation':'editorial/prepare_shared_appendix.py','source_spans':['D.span.3','D.span.4','D.span.5'],'review':'Same finite certificate proof is included in each document with local cross-references.'},'root_prose_deductions':{'path':'editorial/root_contract_review.json','status':'AVAILABLE' if root_review.exists() else 'PENDING_ARTICLE_ONLY_FORMAL_WRAPPERS'},'unmapped_named_article_statements':missing,'review_status':'CORE_STATEMENTS_MAPPED; ROOT_PROSE_WRAPPERS_PENDING' if not root_review.exists() else 'ALL_COMPONENT_REVIEWS_AVAILABLE'}
out['companion_frontmatter_deductions']=frontmatter
out['article_selection_dispositions']='editorial/narrative_rebuild/ARTICLE_DISPOSITIONS.json'
out['narrative_formal_supplements']=supplement_register
out['literal_branch_regularity_supplement']=branch_supplement
for row in article:
 if 'exact_contracts' in row and any(n.startswith('ArticleBranchRegularity.') for n in row['full_formal_exports']):
  row['exact_contracts'].append(branch_supplement['declarations'])
(ROOT/'editorial/CLAIM_LEDGER.json').write_text(json.dumps(out,indent=2)+'\n')
# Portable readable navigation: complete exports, exact signatures and source definitions are expandable.
parts=['<!doctype html><html lang="en"><meta charset="utf-8"><title>BFGS article and companion correspondence</title><style>body{font:16px system-ui;max-width:1050px;margin:3em auto;padding:0 1em;line-height:1.5}pre{white-space:pre-wrap;background:#f3f4f5;padding:1em}summary{cursor:pointer}details{margin:.6em 0}code{overflow-wrap:anywhere}</style><h1>Article and companion correspondence</h1><p>Full formal export lists and exact types. A reviewed correspondence is distinct from Lean checking natural-language text. Original definitions and complete dependency records remain in the sealed declaration index.</p>']
for title,rows in [('Article',article),('Companion scientific opening',frontmatter),('Companion named statements',companion),('Companion inline results and conditional criteria',inline),('Companion unnamed mathematical results and proof passages',unnamed),('Complete companion spans: mathematics, definitions, evidence and open boundaries',span_records)]:
 parts.append('<h2>'+title+'</h2>')
 for row in rows:
  loc=row['location'];parts.append('<details><summary>'+html.escape(row['id'])+' — '+html.escape(row.get('title') or row['kind'])+'</summary><p>'+html.escape(str(loc))+'</p><p>Source spans: '+html.escape(', '.join(row['source_spans']))+'</p>')
  parts.append('<p>Status: '+html.escape(row.get('status',''))+'</p><p>'+html.escape(row.get('hypothesis_status',''))+'</p><p>'+html.escape(row.get('definition_status',''))+'</p><p>'+html.escape(row.get('open_question_status',''))+'</p>')
  for n in row['full_formal_exports']:
   parts.append('<details><summary><code>'+html.escape(n)+'</code></summary><pre>'+html.escape(str(index[n]['signature']))+'</pre></details>')
  parts.append('</details>')
parts.append('</html>');(ROOT/'companion/PROOF_CORRESPONDENCE.html').write_text('\n'.join(parts))
print('Mapped',len(article),'article records;',len(companion),'companion named results;',len(inline),'inline results;',len(unnamed),'unnamed mathematical spans;',len(span_records),'complete classified source spans.')
