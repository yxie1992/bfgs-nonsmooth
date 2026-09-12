#!/usr/bin/env python3
"""Read-only final gate for the corrected report, actual proof audit and PDF.

This validates delivered proof evidence; use master_report/audit/run.py --run
for a fresh Lean build. No Python computation is used as a mathematical proof.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import re

ROOT=Path(__file__).resolve().parents[1]
HERE=ROOT/'master_report'


def read(p):
    return json.loads(p.read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    if not __debug__:
        raise RuntimeError('Run without Python optimization; assertion checks must be enabled.')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--before-seal',action='store_true',help='Authoring check before creating the final artifact manifest.')
    p.add_argument('--node',default=os.environ.get('BFGS_NODE') or shutil.which('node'))
    args=p.parse_args()
    status=read(HERE/'STATUS.json')
    assert status['complete'] and status['status']=='VERIFIED_CORRECTED_EDITION'
    assert status['retained_mathematical_obligations']==[]
    assert not read(HERE/'BUILD_INPUTS.json')['draft']
    assert args.node, 'Node.js is required for the index functional check; pass --node or BFGS_NODE.'
    checks=[]

    def command(argv,label):
        result=subprocess.run(argv,cwd=ROOT,capture_output=True,text=True)
        if result.returncode:
            print(result.stdout,end='');print(result.stderr,end='',file=sys.stderr)
        assert result.returncode==0, label
        checks.append(label)

    command([sys.executable,'scripts/build_rigorous_master_report.py','--check'],'exact textual regeneration')
    command([sys.executable,'master_report/audit/run.py','--check'],'actual pinned compiler/axiom evidence')
    command([sys.executable,'scripts/verify_report_attributions.py'],'citation revision preserves mathematics and classifies attribution separately')
    command([sys.executable,'master_report/review/check_source_proof_index.py'],'independent complete source/index/alias correspondence')
    command([sys.executable,'master_report/review/check_negative_guards.py'],'seven meaningful corruption-rejection tests')
    command([args.node,'master_report/review/check_index_ui.cjs'],'index functional navigation with actual dependencies')
    render=read(HERE/'render/SUMMARY.json')
    assert render['status']=='PASS' and render['draft'] is False
    assert render['pdf']=='output/pdf/Rigorous_BFGS_Master_Report.pdf'
    assert render['tex_warning_lines']==render['words_outside_page']==render['empty_pages']==[]
    assert render['all_pages_rasterized'] is True
    assert isinstance(render['pages'],int) and render['pages']>0
    assert len(render['commands'])==8
    recorded_pdf=Path(render['commands'][5]['command'][1])
    assert recorded_pdf.is_absolute() and recorded_pdf.parts[-3:]==('output','pdf','Rigorous_BFGS_Master_Report.pdf')
    recorded_root=recorded_pdf.parents[2]
    expected=[
        (['python3','scripts/build_rigorous_master_report.py','--check'],'.','assembly-check.log'),
        (['pdflatex','--version'],'.','pdflatex-version.txt'),
        (['latexmk','-v'],'.','latexmk-version.txt'),
        (['pdfinfo','-v'],'.','poppler-version.txt'),
        (['latexmk','-g','-pdf','-interaction=nonstopmode','-halt-on-error','-outdir=../../tmp/pdfs/master21','master.tex'],'master_report/latex','latexmk.log'),
        (['pdfinfo',str(recorded_pdf)],'.','pdfinfo.txt'),
        (['pdftotext','-bbox-layout',str(recorded_pdf),str(recorded_root/'master_report/render/text-bounds.html')],'.','pdftotext.log'),
        (['pdftoppm','-scale-to','1000','-png',str(recorded_pdf),str(recorded_root/'tmp/pdfs/master21/pages/page')],'.','raster.log')]
    assert [(r['command'],r['cwd'],r['log']) for r in render['commands']]==expected, 'render command record differs'
    expected_sources={str(p.relative_to(ROOT)) for p in [ROOT/'scripts/render_rigorous_master_report.py',
        HERE/'BUILD_INPUTS.json',HERE/'STATUS.json',*sorted((HERE/'latex').rglob('*.tex'))]}
    assert set(render['source_sha256'])==expected_sources, 'render source inventory differs'
    expected_evidence={'master_report/render/'+r[2] for r in expected}
    expected_evidence.update({'master_report/render/master.log','master_report/render/text-bounds.html'})
    assert set(render['evidence_sha256'])==expected_evidence, 'render evidence inventory differs'
    for record in render['commands']:
        assert record['exit_code']==0 and (HERE/'render'/record['log']).is_file()
    for field in ['source_sha256','evidence_sha256']:
        for name,h in render[field].items():
            assert sha(ROOT/name)==h, ('render input/evidence changed',name)
    pdf=ROOT/render['pdf'];assert sha(pdf)==render['pdf_sha256']
    actual_pages=re.search(r'^Pages:\s+(\d+)\s*$',(HERE/'render/pdfinfo.txt').read_text(),re.M)
    assert actual_pages and int(actual_pages[1])==render['pages']
    visual=read(HERE/'render/VISUAL_REVIEW.json')
    assert visual['status']=='PASS' and visual['pdf_sha256']==sha(pdf)
    assert visual['pages']==render['pages']
    assert visual['contact_sheet_pages_reviewed']==list(range(1,render['pages']+1))
    assert visual['contact_sheets'] and visual['enlarged_pages_reviewed'] and visual['evidence_sha256']
    assert [n for sheet in visual['contact_sheets'] for n in sheet['pages']]==visual['contact_sheet_pages_reviewed']
    assert all(sheet['path'] in visual['evidence_sha256'] for sheet in visual['contact_sheets'])
    assert all(r['path'] in visual['evidence_sha256'] and 1<=r['page']<=render['pages'] for r in visual['enlarged_pages_reviewed'])
    for name,h in visual['evidence_sha256'].items():
        assert sha(ROOT/name)==h, ('visual evidence changed',name)
    checks.append('final PDF compiler/text bounds and separately recorded visual review')
    if not args.before_seal:
        manifest=read(HERE/'MANIFEST.json')
        assert manifest['status']=='PASS' and manifest['pdf_sha256']==sha(pdf)
        assert manifest['excluded_basenames']==['.DS_Store'], 'unexpected artifact exclusions'
        assert all(Path(name).name!='.DS_Store' for name in manifest['files']), 'OS metadata is not a release artifact'
        for name,h in manifest['files'].items():
            assert sha(ROOT/name)==h, ('sealed artifact changed',name)
        actual={str(f.relative_to(ROOT)) for f in HERE.rglob('*') if f.is_file()
            and '__pycache__' not in f.parts and f.name!='.DS_Store' and f!=HERE/'MANIFEST.json'}
        actual.update(manifest['outside_master_report'])
        assert set(manifest['files'])==actual, 'artifact inventory differs'
        checks.append('complete exact artifact manifest')
    print(json.dumps({'status':'PASS','scope':'Reviewed corrected mathematical edition; explicit open questions and historical exclusions retained',
        'checks':checks,'safe_declarations':9781,'theorems':7954,'source_modules':14,
        'source_spans':172,'source_lines':4323,'pdf_pages':render['pages'],
        'pdf_sha256':sha(pdf),'before_seal':args.before_seal},indent=2))


if __name__=='__main__':
    main()
