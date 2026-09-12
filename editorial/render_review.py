#!/usr/bin/env python3
"""Render every page and produce four-page inspection sheets, with page hashes."""
from pathlib import Path
import hashlib,json,subprocess
from PIL import Image,ImageOps,ImageDraw
ROOT=Path(__file__).resolve().parents[1]
previous=ROOT/'editorial/reviews/render_manifest.json'
if previous.exists():
 history=ROOT/'editorial/reviews/render_history';history.mkdir(exist_ok=True)
 (history/(hashlib.sha256(previous.read_bytes()).hexdigest()[:16]+'.json')).write_bytes(previous.read_bytes())
manifest=[]
for name in ['paper','companion']:
 pdf=ROOT/name/'build/master.pdf'
 out=ROOT/'editorial/reviews/rendered'/name;out.mkdir(parents=True,exist_ok=True)
 for old in out.glob('page-*.png'):old.unlink()
 subprocess.run(['pdftoppm','-r','100','-png',str(pdf),str(out/'page')],check=True,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE)
 pages=sorted(out.glob('page-*.png'))
 count=int(__import__('re').search(r'^Pages:\s+(\d+)',subprocess.check_output(['pdfinfo',str(pdf)],text=True),__import__('re').M)[1]);assert len(pages)==count
 sheets=ROOT/'editorial/reviews/contact_sheets'/name;sheets.mkdir(parents=True,exist_ok=True)
 for old in sheets.glob('sheet-*.jpg'):old.unlink()
 for first in range(0,len(pages),4):
  canvas=Image.new('RGB',(1300,1890),'#d8d8d8');draw=ImageDraw.Draw(canvas)
  for k,p in enumerate(pages[first:first+4]):
   im=Image.open(p).convert('RGB');im.thumbnail((630,910))
   x=10+650*(k%2);y=25+945*(k//2);canvas.paste(im,(x,y))
   draw.text((x,y-19),f'{name} | PDF page {first+k+1}',fill='black')
  canvas.save(sheets/f'sheet-{first//4+1:02}.jpg',quality=90)
 manifest.append({'document':name,'pdf_sha256':hashlib.sha256(pdf.read_bytes()).hexdigest(),'page_count':count,'dpi':100,'pages':[{'page':i+1,'file':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for i,p in enumerate(pages)],'inspection_status':'PENDING_VISUAL_REVIEW'})
(ROOT/'editorial/reviews/render_manifest.json').write_text(json.dumps({'documents':manifest},indent=2)+'\n')
print('Rendered all pages:',[(x['document'],x['page_count']) for x in manifest])
