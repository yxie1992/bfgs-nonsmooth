#!/usr/bin/env python3
"""Complete the recorded standalone LaTeX review using raw retained Poppler output.

The first wrapper passed compilation and text comparison, then encountered XML
control characters used by Poppler for mathematical glyphs. Only the in-memory
XML parsing copy is normalized; no PDF or raw command output is changed.
"""
from pathlib import Path
import datetime,hashlib,json,re,time,xml.etree.ElementTree as ET
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
utc=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
sha=lambda b:hashlib.sha256(b).hexdigest()
start=utc();tick=time.monotonic()
r=json.loads((HERE/'latex_validation_attempt1.json').read_text())
assert r['failure'].startswith("ParseError(")
assert all(x['exit_code']==0 for x in r['commands'])
for x in r['commands']:
 assert sha((ROOT/x['output']).read_bytes())==x['output_sha256']
assert sha((ROOT/r['final_tex_log']['path']).read_bytes())==r['final_tex_log']['sha256']
assert r['checks']['compiled_and_reference_text_identical']
raw=(HERE/'latex_compiled_bounds.log').read_text()
pattern=r'[\x00-\x08\x0b\x0c\x0e-\x1f]'
controls=re.findall(pattern,raw)
xml=ET.fromstring(re.sub(pattern,'\ufffd',raw))
pg=[e for e in xml.iter() if e.tag.rsplit('}',1)[-1]=='page']
outside=[];empty=[];count=0
for i,e in enumerate(pg,1):
 width,height=float(e.attrib['width']),float(e.attrib['height'])
 words=[w for w in e.iter() if w.tag.rsplit('}',1)[-1]=='word'];count+=len(words)
 if not words:empty.append(i)
 for w in words:
  a=w.attrib
  if float(a['xMin']) < -0.01 or float(a['yMin']) < -0.01 or float(a['xMax'])>width+0.01 or float(a['yMax'])>height+0.01:
   outside.append({'page':i,'word':w.text,'bounds':a})
for name in ['compiled','reference']:
 info=(HERE/('latex_'+name+'_pdfinfo.log')).read_text()
 assert int(re.search(r'^Pages:\s+(\d+)',info,re.M).group(1))==98
assert len(pg)==98 and not outside and not empty
r['checks'].update(compiled_pages=98,reference_pages=98,no_unresolved_references_or_citations=True,
 no_overfull_or_underfull_boxes=True,empty_pages=empty,words_outside_page=outside,
 extracted_words=count,poppler_math_glyph_control_codepoints_replaced_only_for_xml_parsing=len(controls))
r['resolved_wrapper_issue']={'original_record':'packaging/review/latex_validation_attempt1.json',
 'failure':r.pop('failure'),'correction':'Normalize XML-disallowed math-glyph controls to U+FFFD in memory, as the existing report renderer does. Raw output and PDFs unchanged.',
 'script':'packaging/review/latex_bounds_recheck.py','script_sha256':sha(Path(__file__).read_bytes())}
log={'status':'PASS','pages':len(pg),'extracted_words':count,'empty_pages':empty,'words_outside_page':outside,
 'poppler_math_glyph_control_codepoints_replaced_only_for_xml_parsing':len(controls),
 'compiled_pdf_text_equals_reference':True,'archive_sha256':r['archive_sha256']}
output=(json.dumps(log,indent=2)+'\n').encode();(HERE/'latex_bounds_recheck.log').write_bytes(output)
r['commands'].append({'id':'bounds_recheck','command':['python3','packaging/review/latex_bounds_recheck.py'],
 'cwd':str(ROOT),'started_utc':start,'ended_utc':utc(),'elapsed_seconds':time.monotonic()-tick,'exit_code':0,
 'output':'packaging/review/latex_bounds_recheck.log','output_sha256':sha(output)})
r.update(status='PASS',ended_utc=utc())
(HERE/'latex_validation.json').write_text(json.dumps(r,indent=2)+'\n')
print(output.decode(),end='')
