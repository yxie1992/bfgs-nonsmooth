#!/usr/bin/env python3
"""Read-only generated-book correspondence checks; writes only this peer scope."""
import collections,datetime,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
PROJECT=next(p for p in HERE.parents if (p/'lakefile.toml').is_file())
REPO=PROJECT.parent; BOOK=PROJECT/'master_report'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(b,msg):
 if not b:raise ValueError(msg)
edits=[e for f in sorted((BOOK/'edits').glob('*.json')) for e in read(f)]
byid={e['id']:e for e in edits};need(len(byid)==len(edits),'duplicate edit ids')
reviewed=[]
for f in ['audit/scratch/master21/ac/replacements.json','audit/scratch/master21/tfh_review/additional_edits.json']:
 x=read(PROJECT/f);reviewed.extend(x['edits'] if isinstance(x,dict) else x)
reviewed.extend(read(HERE/'H_dimension_zero_edit.json'))
for e in reviewed:
 need(byid.get(e['id'])==e,'reviewed edit not incorporated exactly: '+e['id'])
 need(e['new'] in (BOOK/'latex/chapters'/Path(e['source']).name).read_text(),'replacement absent '+e['id'])
sm=read(BOOK/'SOURCE_MAP.json'); cs=read(BOOK/'CLAIMS.json')['claims'];need(len(cs)==172,'not172spans')
need(len(sm['modules'])==14,'not14modules');need(sm['edits']==edits,'source-map edits differ')
linecount=0
for m in sm['modules']:
 old=(REPO/m['original']).read_text();new=(BOOK/m['corrected']).read_text()
 need(sha(REPO/m['original'])==m['original_sha256'],'originalhash '+m['module'])
 need(sha(BOOK/m['corrected'])==m['corrected_sha256'],'correctedhash '+m['module'])
 opos=npos=0;chunks=[]
 for z in m['character_map']:
  a,b=z['old'];c,d=z['new'];need(a==opos and c==npos and b>=a and d>=c,'noncontiguouscharacter map')
  if z['edit'] is None:need(old[a:b]==new[c:d],'undisclosed change')
  else:
   e=byid[z['edit']];need(old[a:b]==e['old'] and new[c:d]==e['new'],'edit segment mismatch')
  chunks.append(new[c:d]);opos=b;npos=d
 need(opos==len(old) and npos==len(new) and ''.join(chunks)==new,'incomplete map')
 prev=0;coverage=(BOOK/'latex/coverage'/Path(m['corrected']).name).read_text()
 for c in [x for x in cs if x['module']==m['module']]:
  a,b=c['original_lines'];need(a==prev+1,'source line gap');prev=b
  excerpt='\n'.join('\n'.join(new.splitlines()[a-1:b]) for a,b in c['corrected_line_ranges'])
  need(excerpt==c['corrected_excerpt'],'corrected excerpt mismatch')
  omitted=c['classification']=='notation_or_scope' and not c['exports']
  need((c['id']+' & ' in coverage)!=omitted,'table omission '+c['id'])
 need(prev==len(old.splitlines()),'source end gap');linecount+=prev
need(linecount==4323,'not4323lines')
cc={x['id']:x for x in cs}
need('BfgsVerification.homogeneousDichotomy' in cc['H.span.2']['exports'],'H2 missing actual general theorem')
need('BfgsVerification.AdmissibleBFGSRun.positive_invariants' in cc['H.span.2']['exports'],'H2 missing derived SPD')
need(cc['H.span.6']['classification']=='proved_summary_and_open_question' and 'BfgsVerification.homogeneousDichotomy' in cc['H.span.6']['exports'],'H6 lost proved/open distinction')
need(cc['I.span.22']['classification']=='mathematics_evidence_and_open_boundaries','I22 missing mixed classification')
need('BfgsVerification.deterministicSeedFailure' in cc['I.span.22']['exports'],'I22 missing actual affine max failure')
for c in cs:
 if c['classification']=='proved_mathematics':need(bool(c['exports']),'proved span without export')
needed=set(n for c in cs for n in c['exports'])
known={r['theorem'] for r in read(PROJECT/'audit/declarations.json')}
for f in (PROJECT/'audit/claim_review20/fresh').glob('*/REPORTS.json'):
 known.update(r['name'] for r in read(f))
for f in [BOOK/'audit/main/all_safe_declarations.json',BOOK/'audit/supplemental/all_safe_declarations.json']:
 if f.exists():known.update(r['name'] for r in read(f))
need(needed<=known,'unknown cited declarations '+str(needed-known))
# Check the actual HTML/JSON declaration view against closed compiler inventories.
html=(BOOK/'PROOF_INDEX.html').read_text();pos=html.index('const DATA=')+len('const DATA=')
hdata,_=json.JSONDecoder().raw_decode(html[pos:]);need(hdata['claims']==cs,'HTML claim data differs')
di=read(BOOK/'DECLARATION_INDEX.json');need(hdata['declarations']==di,'HTML declaration data differs')
ba={r['name']:r for r in read(BOOK/'audit/main/all_safe_declarations.json')}
for r in read(BOOK/'audit/supplemental/all_safe_declarations.json'):ba.setdefault(r['name'],r)
mods=read(BOOK/'audit/module_sources.json');seen_sources=set();edges=[]
for n,r in di.items():
 need(n in ba and all(r.get(k)==v for k,v in ba[n].items()),'changed compiler record '+n)
 for k in ['type_project_dependencies','value_project_dependencies','structural_project_dependencies']:
  for dep in r[k]:
   need(dep in di,'missing indexed project dependency '+dep);edges.append((n,dep))
 m=mods[r['module']];src=REPO/m['source'];need(sha(src)==m['sha256'],'source inventory hash')
 need(r['source_path']==m['source'] and (BOOK/r['source_href']).resolve()==src.resolve(),'source hyperlink differs')
 seen_sources.add(src)
 if r.get('source_excerpt') is not None:
  q=r['source_range'];start=q['start_line'];stop=q['end_line']-(q['end_column']==0)
  need(r['source_excerpt']=='\n'.join(src.read_text().splitlines()[start-1:min(stop,start+239)]),'source excerpt differs')
closure=set(needed);old_size=-1
while old_size!=len(closure):
 old_size=len(closure)
 closure.update(b for a,b in edges if a in closure)
need(set(di)==closure,'indexed dependency closure differs')
inputs=[BOOK/'CLAIMS.json',BOOK/'SOURCE_MAP.json',BOOK/'BUILD_INPUTS.json',BOOK/'STATUS.json',BOOK/'authoring/frontmatter.tex',BOOK/'authoring/extra_span_exports.json',PROJECT/'scripts/build_rigorous_master_report.py',*(BOOK/'edits').glob('*.json'),*(BOOK/'latex').rglob('*.tex')]
inputs.extend(REPO/m['original'] for m in sm['modules'])
inputs.extend([BOOK/'PROOF_INDEX.html',BOOK/'DECLARATION_INDEX.json',BOOK/'audit/main/all_safe_declarations.json',BOOK/'audit/supplemental/all_safe_declarations.json',BOOK/'audit/module_sources.json',*seen_sources])
(HERE/'generated_source_hashes.json').write_text(json.dumps({str(p.relative_to(REPO)):sha(p) for p in sorted(set(inputs))},indent=2)+'\n')
result={'status':'PASS_DRAFT_SOURCE_REVIEW','timestamp':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewed_edits_exact':len(reviewed),'whole_ledger_edits':len(edits),'original_modules':14,'original_spans':172,'original_lines':linecount,'classifications':dict(collections.Counter(c['classification'] for c in cs)),'cited_declarations':len(needed),'html_declarations_exact':len(di),'indexed_project_dependency_edges':len(edges),'indexed_lean_source_files':len(seen_sources),'no_export_spans':[c['id'] for c in cs if not c['exports']],'scope':'Generated-source/statement correspondence. Not a new compiler, typesetting, PDF visual, or final release gate.'}
(HERE/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
