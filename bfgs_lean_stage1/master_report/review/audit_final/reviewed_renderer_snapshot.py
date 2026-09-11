#!/usr/bin/env python3
"""Build the edition PDF and record actual LaTeX/layout checks.

Requires latexmk, pdflatex, pdfinfo, pdftotext and pdftoppm on PATH.
This document tool performs no computation used in a Lean proof.
"""
from pathlib import Path
import argparse
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / 'master_report'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--draft', action='store_true')
    parser.add_argument('--raster', action='store_true', help='Render every page for visual inspection.')
    args = parser.parse_args()
    status = json.loads((HERE/'STATUS.json').read_text())
    assert args.draft or status['complete'], 'Release rendering requires the completed mathematical gates.'
    build = ROOT/'tmp/pdfs/master21'
    evidence = HERE/'render'
    output = ROOT/'output/pdf/Rigorous_BFGS_Master_Report.pdf'
    for p in (build, evidence, output.parent):
        p.mkdir(parents=True, exist_ok=True)
    started = dt.datetime.now(dt.timezone.utc).isoformat()
    commands = []

    def run(argv, log, cwd=ROOT, env=None):
        begin = dt.datetime.now(dt.timezone.utc).isoformat()
        p = subprocess.run(argv, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (evidence/log).write_bytes(p.stdout)
        commands.append({'command':argv, 'cwd':str(cwd.relative_to(ROOT)),
            'started_utc':begin, 'exit_code':p.returncode, 'log':log})
        assert p.returncode == 0, f'{argv[0]} failed; see {evidence/log}'
        return p.stdout.decode(errors='replace')

    env = dict(os.environ)
    # Fixed publication timestamp makes the PDF metadata reproducible. Actual
    # execution times are recorded independently above and in SUMMARY.json.
    epoch = int(dt.datetime(2026,9,11,tzinfo=dt.timezone.utc).timestamp())
    env.update(SOURCE_DATE_EPOCH=str(epoch), FORCE_SOURCE_DATE='1', TZ='UTC')
    run(['latexmk','-g','-pdf','-interaction=nonstopmode','-halt-on-error',
         '-outdir=../../tmp/pdfs/master21','master.tex'],
        'latexmk.log', HERE/'latex',env)
    log = (build/'master.log').read_text(errors='replace')
    (evidence/'master.log').write_text(log)
    forbidden = [line for line in log.splitlines() if re.search(
        r'Overfull|Underfull|LaTeX Warning|Package .* Warning|Missing character|undefined references',line)]
    assert not forbidden, forbidden
    shutil.copyfile(build/'master.pdf',output)
    info = run(['pdfinfo',str(output)],'pdfinfo.txt')
    run(['pdftotext','-bbox-layout',str(output),str(evidence/'text-bounds.html')],'pdftotext.log')
    # Poppler can emit XML-forbidden control codepoints for TeX math glyphs.
    # Preserve its raw output, replace only those codepoints for XML parsing,
    # and report the count; glyph appearance is checked in the rendered PDF.
    raw_xml = (evidence/'text-bounds.html').read_text()
    controls = re.findall(r'[\x00-\x08\x0b\x0c\x0e-\x1f]',raw_xml)
    xml = ET.fromstring(re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f]', '\ufffd',raw_xml))
    pages = [p for p in xml.iter() if p.tag.endswith('}page')]
    outside = []; empty = []; words = 0
    for i,page in enumerate(pages,1):
        w=float(page.attrib['width']);h=float(page.attrib['height'])
        ws=[n for n in page.iter() if n.tag.endswith('}word')]
        words += len(ws)
        if not ws:empty.append(i)
        for word in ws:
            a=word.attrib
            if float(a['xMin']) < 0 or float(a['yMin']) < 0 or float(a['xMax']) > w+0.5 or float(a['yMax']) > h+0.5:
                outside.append({'page':i,'word':word.text,'bounds':a})
    assert pages and not outside and not empty, (len(pages),outside,empty)
    if args.raster:
        (build/'pages').mkdir(exist_ok=True)
        run(['pdftoppm','-scale-to','1000','-png',str(output),str(build/'pages/page')],'raster.log')
    sources = [Path(__file__).resolve(),HERE/'BUILD_INPUTS.json',HERE/'STATUS.json',
        *sorted((HERE/'latex').rglob('*.tex'))]
    summary = {'schema_version':1,'status':'PASS','draft':args.draft,
        'started_utc':started,'finished_utc':dt.datetime.now(dt.timezone.utc).isoformat(),
        'commands':commands,'fixed_publication_epoch':epoch,
        'pdf':str(output.relative_to(ROOT)),'pdf_sha256':sha(output),
        'pages':len(pages),'extracted_words':words,'tex_warning_lines':forbidden,
        'poppler_math_glyph_control_codepoints_replaced_only_for_xml_parsing':len(controls),
        'words_outside_page':outside,'empty_pages':empty,'all_pages_rasterized':args.raster,
        'visual_review':'Recorded separately after inspection; compiler and text bounds do not substitute for it.',
        'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in sources},
        'evidence_sha256':{str(p.relative_to(ROOT)):sha(p) for p in evidence.iterdir()
            if p.is_file() and p.name not in {'SUMMARY.json','VISUAL_REVIEW.json'}}}
    (evidence/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(f'PASS: {len(pages)} pages, {words} extracted words; no TeX warnings, empty pages or out-of-page words.')


if __name__ == '__main__':
    main()
