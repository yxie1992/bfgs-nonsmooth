#!/usr/bin/env python3
"""Meaningful corruption regressions using a read overlay; never mutate actual artifacts."""
from pathlib import Path
import contextlib,datetime,hashlib,io,json,runpy
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'lean-toolchain').is_file() and (p/'lakefile.toml').is_file())
PACKAGE=ROOT/'master_report/audit';CHECKER=HERE/'check_source_proof_index.py'
read_bytes=Path.read_bytes;read_text=Path.read_text
sha=lambda b:hashlib.sha256(b).hexdigest()
def data(rel):return json.loads(read_text(PACKAGE/rel))
def blob(r):return (json.dumps(r,ensure_ascii=False,indent=2)+'\n').encode()
def evaluate(overlay):
 def rb(p):return overlay.get(p.resolve(),read_bytes(p))
 def rt(p,*a,**kw):return overlay[p.resolve()].decode(kw.get('encoding') or 'utf-8') if p.resolve() in overlay else read_text(p,*a,**kw)
 try:
  with patch.object(Path,'read_bytes',rb),patch.object(Path,'read_text',rt),contextlib.redirect_stdout(io.StringIO()):runpy.run_path(str(CHECKER),run_name='__main__')
 except AssertionError as e:return str(e)
 return None
results=[]
def check(label,overlay,expected):
 reason=evaluate(overlay);assert reason and expected in reason,(label,reason,expected);results.append({'case':label,'rejected':True,'reason':reason})
main=PACKAGE/'main/all_safe_declarations.json';changed=read_bytes(main)+b'\n'
check('alias byte corruption',{main:changed},'audit manifest hash mismatch')
manifest=data('MANIFEST.json');aliases=data('output_aliases.json');manifest['files']['main/all_safe_declarations.json']=sha(changed);aliases['main/all_safe_declarations.json']['sha256']=sha(changed);ab=blob(aliases);manifest['files']['output_aliases.json']=sha(ab)
check('coordinated alias/manifest corruption still differs from actual compiler output',{main:changed,PACKAGE/'output_aliases.json':ab,PACKAGE/'MANIFEST.json':blob(manifest)},'alias differs from compiler output')
# Keep all alias/manifest/SUMMARY hashes internally consistent, but remove closure.
overlay={};manifest=data('MANIFEST.json');aliases=data('output_aliases.json');summary=data('fresh/SUMMARY.json')
first=data('main/all_safe_declarations.json')[0]['name']
for rel in ['main/all_safe_declarations.json','supplemental/all_safe_declarations.json']:
 rows=data(rel);row=next(r for r in rows if r['name']==first);row['value_project_dependencies'].append('MissingProjectDependency_IndependentNegative')
 b=blob(rows);actual=aliases[rel]['actual_output'];overlay[PACKAGE/rel]=b;overlay[PACKAGE/actual]=b
 aliases[rel]['sha256']=sha(b);manifest['files'][rel]=sha(b);manifest['files'][actual]=sha(b);summary['outputs'][actual[6:]]=sha(b)
for rel,value in [('output_aliases.json',aliases),('fresh/SUMMARY.json',summary)]:overlay[PACKAGE/rel]=blob(value);manifest['files'][rel]=sha(overlay[PACKAGE/rel])
overlay[PACKAGE/'MANIFEST.json']=blob(manifest)
check('internally rehashed missing project dependency',overlay,'missing actual project dependencies')
module=data('module_sources.json');module[next(iter(module))]['source']='/not/a/repository/path.lean';b=blob(module);manifest=data('MANIFEST.json');manifest['files']['module_sources.json']=sha(b)
check('rehashed absolute module source path',{PACKAGE/'module_sources.json':b,PACKAGE/'MANIFEST.json':blob(manifest)},'non-repository module source')
htmlfile=ROOT/'master_report/PROOF_INDEX.html';html=read_text(htmlfile);offset=html.index('const DATA=')+len('const DATA=');index,end=json.JSONDecoder().raw_decode(html[offset:]);name=next(iter(index['declarations']));index['declarations'][name]['signature']+=' independently corrupted';bad=html[:offset]+json.dumps(index,ensure_ascii=False).replace('<','\\u003c')+html[offset+end:]
check('changed indexed formal statement',{htmlfile:bad.encode()},'HTML audited declaration differs')
index,end=json.JSONDecoder().raw_decode(html[offset:]);name=next(n for n,r in index['declarations'].items() if r.get('source_excerpt'));index['declarations'][name]['source_excerpt']+='\n-- fabricated excerpt';bad=html[:offset]+json.dumps(index,ensure_ascii=False).replace('<','\\u003c')+html[offset+end:]
check('coordinated HTML/JSON fabricated source excerpt',{htmlfile:bad.encode(),ROOT/'master_report/DECLARATION_INDEX.json':blob(index['declarations'])},'source excerpt')
claimsfile=ROOT/'master_report/CLAIMS.json';claims=json.loads(read_text(claimsfile));claims['claims'][0]['corrected_line_ranges'][0][1]+=1
check('incorrect original-to-corrected source mapping',{claimsfile:blob(claims)},'incorrect original-to-corrected mapping')
assert evaluate({}) is None,'positive replay failed'
print(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','script_sha256':sha(read_bytes(Path(__file__))), 'checker_sha256':sha(read_bytes(CHECKER)),'positive_actual_artifact_check':'PASS','negative_cases':results,'method':'Read-only Python pathlib overlay; no source, output, log or manifest was changed.'},indent=2))
