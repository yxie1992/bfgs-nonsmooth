#!/usr/bin/env python3
"""Independent read-only edition/actual-proof-index checks; no Lean or document writes."""
import collections,datetime,hashlib,json,re,os
from pathlib import Path
ROOT=next(p for p in Path(__file__).resolve().parents if (p/'lean-toolchain').is_file() and (p/'lakefile.toml').is_file());REPO=ROOT.parent;HERE=ROOT/'master_report'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(p,m):
 if not p:raise AssertionError(m)
keys=('type_project_dependencies','value_project_dependencies','structural_project_dependencies')
audit_dir=HERE/'audit';manifest=read(audit_dir/'MANIFEST.json')
require(manifest['status']=='PASS','audit manifest not passed')
for key,value in {'main_safe':9672,'main_theorems':7874,'unified_safe':9781,'unified_theorems':7954,'prior_exact_theorems':7813,'additional_generated_main_theorems':61,'additional_private_main_theorems':59,'additional_supplemental_safe_names':109}.items():require(manifest[key]==value,'manifest count '+key)
def package_path(name):
 p=Path(name);require(not p.is_absolute() and '..' not in p.parts,'non-package evidence path '+name);return audit_dir/p
for name,h in manifest['files'].items():require(sha(package_path(name))==h,'audit manifest hash mismatch '+name)
aliases=read(audit_dir/'output_aliases.json');require(set(aliases)=={'main/all_safe_declarations.json','main/compiler_implementation_declarations.json','main/statistics.json','supplemental/all_safe_declarations.json','supplemental/compiler_implementation_declarations.json','supplemental/statistics.json'},'alias inventory')
summary=read(audit_dir/'fresh/SUMMARY.json');require(summary['status']=='PASS','actual audit run did not pass')
for name,row in aliases.items():
 p=package_path(name);q=package_path(row['actual_output']);require(row['actual_output'].startswith('fresh/'),'alias does not name actual fresh output')
 require(p.read_bytes()==q.read_bytes() and sha(p)==row['sha256'],'alias differs from compiler output '+name)
 require(manifest['files'][name]==row['sha256'] and manifest['files'][row['actual_output']]==row['sha256'],'alias/manifest binding '+name)
 require(summary['outputs'][row['actual_output'][6:]]==row['sha256'],'alias/actual-run binding '+name)
module_sources=read(audit_dir/'module_sources.json');stats=read(audit_dir/'supplemental/statistics.json')
require(set(module_sources)==set(stats['module_names']),'module/source coverage')
for n,row in module_sources.items():
 q=Path(row['source']);require(not q.is_absolute() and '..' not in q.parts,'non-repository module source '+n)
 require(sha(REPO/q)==row['sha256'],'module proof-source hash '+n)
base=read(HERE/'audit/main/all_safe_declarations.json');unified=read(HERE/'audit/supplemental/all_safe_declarations.json')
require(len(base)==9672 and len(unified)==9781,'safe inventory counts')
def census(rows):
 names=[r['name'] for r in rows];require(len(names)==len(set(names)),'duplicate audited names')
 for r in rows:
  require(not r['unsafe'] and not r['partial'],'unsafe/partial mathematical row '+r['name'])
  require(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'},'nonstandard axiom '+r['name'])
 return {r['name']:r for r in rows}
main=census(base);allrows=census(unified)
require(set(main)<=set(allrows),'unified omitted main name')
for n,r in main.items():
 for k in ('signature','kind','level_params','axioms',*keys):
  a,b=r[k],allrows[n][k]
  require((set(a)==set(b) if isinstance(a,list) else a==b),'main/unified mismatch '+n+' '+k)
# Match builder's stable main-first attribution, without ignoring absent edges.
audit={**allrows,**main}
missing=sorted({d for r in audit.values() for k in keys for d in r.get(k,[]) if d not in audit})
require(not missing,'missing actual project dependencies: '+repr(missing))
source_map=read(HERE/'SOURCE_MAP.json');claims=read(HERE/'CLAIMS.json')['claims'];ledger=source_map['edits']
register=read(ROOT/'audit/REPORT_STATUS.json');original_claims={s['id']:s for m in register['modules'] for s in m['coverage_spans']};additions=read(HERE/'authoring/extra_span_exports.json')
require({c['id'] for c in claims}==set(original_claims),'claim ID correspondence')
require(len(source_map['modules'])==14 and len(claims)==172,'module/span counts')
require(len({e['id'] for e in ledger})==len(ledger),'duplicate edit IDs')
used=[];original_lines=0
for m in source_map['modules']:
 src=REPO/m['original'];raw=src.read_text();require(sha(src)==m['original_sha256'],'original changed '+str(src))
 own=[e for e in ledger if e['source']==m['original']];locations=[]
 for e in own:
  require(raw.count(e['old'])==1,'nonunique original anchor '+e['id']);a=raw.index(e['old']);b=a+len(e['old'])
  require(raw[:a].count('\n')+1==e['start_line'],'start line '+e['id'])
  require(raw[:b].count('\n')+(not e['old'].endswith('\n'))==e['end_line'],'end line '+e['id'])
  locations.append((a,b,e));used.append(e['id'])
 locations.sort(key=lambda z:z[0]);require(all(x[1]<=y[0] for x,y in zip(locations,locations[1:])),'overlap '+m['module'])
 expected=raw
 for a,b,e in reversed(locations):expected=expected[:a]+e['new']+expected[b:]
 corrected=HERE/m['corrected'];require(corrected.read_text()==expected,'corrected text mismatch '+m['module']);require(sha(corrected)==m['corrected_sha256'],'corrected hash '+m['module'])
 old_cursor=new_cursor=0
 for segment in m['character_map']:
  oa,ob=segment['old'];na,nb=segment['new'];require(oa==old_cursor and na==new_cursor and oa<ob and na<=nb,'character-map partition '+m['module'])
  if segment['edit'] is None:require(raw[oa:ob]==expected[na:nb],'unchanged character-map span')
  else:
   e=next(e for e in own if e['id']==segment['edit']);require(raw[oa:ob]==e['old'] and expected[na:nb]==e['new'],'edited character-map span')
  old_cursor=ob;new_cursor=nb
 require(old_cursor==len(raw) and new_cursor==len(expected),'character-map endpoint')
 previous=0
 for c in [c for c in claims if c['module']==m['module']]:
  a,b=c['original_lines'];require(a==previous+1,'original partition gap '+c['id']);previous=b
  orig=original_claims[c['id']];require([orig['start_line'],orig['end_line']]==[a,b],'original claim correspondence '+c['id'])
  lines=raw.splitlines(keepends=True);lo=sum(map(len,lines[:a-1]));hi=sum(map(len,lines[:b]));mapped=[];applied=[]
  for seg in m['character_map']:
   x=max(lo,seg['old'][0]);y=min(hi,seg['old'][1])
   if x>=y:continue
   if seg['edit'] is None:u=seg['new'][0]+x-seg['old'][0];v=u+y-x
   else:u,v=seg['new'];applied.append(seg['edit'])
   mapped.append([expected[:u].count('\n')+1,expected[:v].count('\n')+(not expected[:v].endswith('\n'))])
  merged=[]
  for u,v in sorted(mapped):
   if merged and u<=merged[-1][1]+1:merged[-1][1]=max(merged[-1][1],v)
   else:merged.append([u,v])
  require(merged==c['corrected_line_ranges'],'incorrect original-to-corrected mapping '+c['id'])
  require(list(dict.fromkeys(applied))==c['edits'],'claim edit association '+c['id'])
  expected_exports=list(dict.fromkeys(orig['verified_exports']+additions['exports'].get(c['id'],[])+[n for e in own if e['id'] in applied for n in e['lean_exports']]))
  require(expected_exports==c['exports'],'reviewed export correspondence '+c['id'])
  require(c['original_sha256']==m['original_sha256'],'claim source hash '+c['id'])
  excerpt='\n'.join('\n'.join(expected.splitlines()[a-1:b]) for a,b in c['corrected_line_ranges']);require(excerpt==c['corrected_excerpt'],'excerpt mismatch '+c['id'])
  require(all(n in audit for n in c['exports']),'unaudited export '+c['id'])
  if c['classification']=='proved_mathematics':require(bool(c['exports']),'unlinked proved span '+c['id'])
  if c['module']=='E':require(c['classification'] in ['execution_evidence_or_scope','mathematics_and_evidence_scope'],'E evidence mislabeled '+c['id'])
 require(previous==len(raw.splitlines()),'original tail '+m['module']);original_lines+=previous
require(original_lines==4323,'original line count');require(sorted(used)==sorted(e['id'] for e in ledger),'unused edits')
html=(HERE/'PROOF_INDEX.html').read_text();start=html.index('const DATA=')+len('const DATA=');data,end=json.JSONDecoder().raw_decode(html[start:]);require(data['claims']==claims,'HTML and JSON claims differ')
needed=set();todo=[n for c in claims for n in c['exports']]
while todo:
 n=todo.pop()
 if n in needed:continue
 needed.add(n)
 for k in keys:todo.extend(audit[n].get(k,[]))
require(set(data['declarations'])==needed,'HTML dependency closure incomplete or contains unreviewed extras')
for n in needed:
 for k in ('signature','kind','level_params','axioms',*keys):
  require(data['declarations'][n].get(k)==audit[n].get(k),'HTML audited declaration differs '+n+' '+k)
require(read(HERE/'DECLARATION_INDEX.json')==data['declarations'],'HTML and full declaration JSON differ')
source_cache={}
for n,row in data['declarations'].items():
 spec=module_sources[row['module']];p=REPO/spec['source']
 require(row['source_path']==spec['source'] and (HERE/row['source_href']).resolve()==p.resolve(),'source link '+n)
 if p not in source_cache:source_cache[p]=p.read_text().splitlines()
 r=row.get('source_range')
 if r and r['start_line']>0:
  a=r['start_line'];b=r['end_line']-(r['end_column']==0)
  require(1<=a<=b<=len(source_cache[p]),'actual source range '+n)
  require(row['source_excerpt']=='\n'.join(source_cache[p][a-1:min(b,a+239)]),'source excerpt '+n)
  require(row['source_excerpt_truncated']==(b-a+1>240),'source excerpt truncation '+n)
build=read(HERE/'BUILD_INPUTS.json');require(build['path_base']=='repository','input path base')
for p,h in build['sha256'].items():require(sha(REPO/p)==h,'build input mutated '+p)
required=[HERE/'audit/main/all_safe_declarations.json',HERE/'audit/supplemental/all_safe_declarations.json',HERE/'STATUS.json',REPO/'BFGS_MASTER_REPORT_LaTeX/report/master.tex']
require(all(str(p.relative_to(REPO)) in build['sha256'] for p in required),'missing output-affecting input')
print(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','source_modules':14,'original_spans':172,'original_lines':4323,'unique_edits':len(ledger),'main_safe':len(main),'combined_safe':len(audit),'unique_claim_exports':len({n for c in claims for n in c['exports']}),'indexed_dependency_closure':len(needed),'missing_project_dependencies':missing,'module_source_files':len(module_sources),'audit_package_files_hashed':len(manifest['files']),'alias_bindings_checked':len(aliases),'edition_status':read(HERE/'STATUS.json')['status'],'input_sha256':{str(p.relative_to(ROOT)):sha(p) for p in [Path(__file__).resolve(),HERE/'SOURCE_MAP.json',HERE/'CLAIMS.json',HERE/'PROOF_INDEX.html',HERE/'BUILD_INPUTS.json',audit_dir/'MANIFEST.json',audit_dir/'output_aliases.json',audit_dir/'module_sources.json',*required[:-1]]}},indent=2))
