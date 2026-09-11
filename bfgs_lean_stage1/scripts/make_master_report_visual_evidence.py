#!/usr/bin/env python3
"""Prepare page contact sheets and enlarged samples; does not certify inspection.

Requires Pillow and pdftoppm. Every source/output remains in the Lean project.
"""
from pathlib import Path
import datetime as dt
import hashlib
import json
import subprocess
from PIL import Image, ImageDraw

ROOT=Path(__file__).resolve().parents[1]
HERE=ROOT/'master_report'
record=json.loads((HERE/'render/SUMMARY.json').read_text())
if record['status']!='PASS' or record['draft']:
    raise RuntimeError('A successful final PDF render is required.')
pdf=ROOT/record['pdf']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if sha(pdf)!=record['pdf_sha256']:
    raise RuntimeError('The rendered PDF changed.')
pages=sorted((ROOT/'tmp/pdfs/master21/pages').glob('page-*.png'))
if len(pages)!=record['pages']:
    raise RuntimeError('Raster page count differs.')
out=HERE/'render/visual';out.mkdir(exist_ok=True)
sheets=[]
for start in range(0,len(pages),16):
    canvas=Image.new('RGB',(1560,2240),'#dde4e8');draw=ImageDraw.Draw(canvas)
    for k,p in enumerate(pages[start:start+16]):
        im=Image.open(p).convert('RGB');im.thumbnail((370,515))
        x=(k%4)*390+(390-im.width)//2;y=(k//4)*560+26
        canvas.paste(im,(x,y));draw.text(((k%4)*390+12,(k//4)*560+7),f'PDF page {start+k+1}',fill='black')
    p=out/f'contact-{start//16+1}.jpg';canvas.save(p,quality=88)
    sheets.append({'path':str(p.relative_to(ROOT)),'pages':list(range(start+1,min(start+16,len(pages))+1))})
focus=[];commands=[]
for page in [1,15,26,37,46,60,70,75,86]:
    prefix=out/f'page-{page}'
    argv=['pdftoppm','-f',str(page),'-l',str(page),'-scale-to','1800','-singlefile','-png',str(pdf),str(prefix)]
    result=subprocess.run(argv,capture_output=True,text=True)
    commands.append({'command':argv,'exit_code':result.returncode,'output':result.stdout+result.stderr})
    if result.returncode:raise RuntimeError(result.stderr)
    focus.append({'page':page,'path':str(prefix.with_suffix('.png').relative_to(ROOT))})
data={'status':'PREPARED_FOR_INSPECTION','utc':dt.datetime.now(dt.timezone.utc).isoformat(),
    'pdf_sha256':sha(pdf),'pages':record['pages'],'contact_sheets':sheets,
    'enlarged_pages':focus,'commands':commands,'preparer_sha256':sha(Path(__file__).resolve()),
    'raster_source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in pages},
    'evidence_sha256':{r['path']:sha(ROOT/r['path']) for r in sheets+focus}}
(out/'SOURCES.json').write_text(json.dumps(data,indent=2)+'\n')
print('Prepared all',record['pages'],'pages in',len(sheets),'contact sheets and',len(focus),'enlarged samples. Inspection is a separate step.')
