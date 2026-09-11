#!/usr/bin/env python3
"""Assemble the reviewed corrected edition without changing its original sources.

This is document/provenance tooling. It performs no mathematical computation
for Lean. Exact Lean statements and dependencies come from compiler audits.
"""
from __future__ import annotations
import argparse
import hashlib
import html
import json
import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
HERE = ROOT / 'master_report'
ORIGINAL = REPO / 'BFGS_MASTER_REPORT_LaTeX/report'


def read(p):
    return json.loads(p.read_text())


def digest(data):
    return hashlib.sha256(data).hexdigest()


def tex(s):
    table = {'\\': r'\textbackslash{}', '&': r'\&', '%': r'\%', '$': r'\$',
             '#': r'\#', '_': r'\_', '{': r'\{', '}': r'\}',
             '~': r'\textasciitilde{}', '^': r'\textasciicircum{}'}
    return ''.join(table.get(c, c) for c in str(s))


def edited_source(source, edits):
    """Return corrected text and a complete character-origin map."""
    located = []
    for e in edits:
        assert source.count(e['old']) == 1, ('anchor not unique', e['id'])
        start = source.index(e['old']); end = start + len(e['old'])
        assert source[:start].count('\n') + 1 == e['start_line'], e['id']
        # An anchor may be a substring within its final source line.
        assert source[:end].count('\n') + (not e['old'].endswith('\n')) == e['end_line'], e['id']
        located.append((start, end, e))
    located.sort(key=lambda x: x[0])
    for left, right in zip(located, located[1:]):
        assert left[1] <= right[0], ('overlapping edits', left[2]['id'], right[2]['id'])
    chunks = []; mapping = []; oldpos = 0; newpos = 0
    for start, end, e in located:
        if oldpos < start:
            body = source[oldpos:start]; chunks.append(body)
            mapping.append({'old': [oldpos, start], 'new': [newpos, newpos+len(body)], 'edit': None})
            newpos += len(body)
        chunks.append(e['new'])
        mapping.append({'old': [start, end], 'new': [newpos, newpos+len(e['new'])], 'edit': e['id']})
        newpos += len(e['new']); oldpos = end
    if oldpos < len(source):
        body = source[oldpos:]; chunks.append(body)
        mapping.append({'old': [oldpos, len(source)], 'new': [newpos, newpos+len(body)], 'edit': None})
    result = ''.join(chunks)
    assert sum(c['new'][1]-c['new'][0] for c in mapping) == len(result)
    return result, mapping


def mapped_span(source, corrected, mapping, start, end):
    lines = source.splitlines(keepends=True)
    a = sum(map(len, lines[:start-1])); b = sum(map(len, lines[:end]))
    ranges=[]; changes=[]
    for m in mapping:
        lo=max(a,m['old'][0]); hi=min(b,m['old'][1])
        if lo >= hi:
            continue
        if m['edit'] is None:
            x=m['new'][0]+lo-m['old'][0]; y=x+hi-lo
        else:
            x,y=m['new'];changes.append(m['edit'])
        ranges.append([corrected[:x].count('\n')+1,
                       corrected[:y].count('\n')+(not corrected[:y].endswith('\n'))])
    merged=[]
    for a,b in sorted(ranges):
        if merged and a<=merged[-1][1]+1:
            merged[-1][1]=max(merged[-1][1],b)
        else:
            merged.append([a,b])
    return merged, list(dict.fromkeys(changes))


def declarations(draft):
    path = HERE/'audit/main/all_safe_declarations.json'
    if not path.exists():
        assert draft, 'The module-wide audit must be completed before a release build.'
        base = {r['theorem']: {'name': r['theorem'], 'signature': r['signature'],
                'axioms': r['axioms'], 'kind':'theorem', 'module':None,
                'type_project_dependencies':[], 'value_project_dependencies':[]}
                for r in read(ROOT/'audit/declarations.json')}
    else:
        base = {r['name']:r for r in read(path)}
    # The old ordinary reports are a readable fallback only for draft assembly.
    for file in (sorted((ROOT/'audit/claim_review20/fresh').glob('*/REPORTS.json')) if draft else []):
        for r in read(file):
            if r['name'] not in base:
                base[r['name']]={'name':r['name'],'signature':r.get('type','See the checked source and compiler log.'),
                    'axioms':r['axioms'],'module':'supplemental20','kind':'review declaration',
                    'type_project_dependencies':[], 'value_project_dependencies':[]}
    extra = HERE/'audit/supplemental/all_safe_declarations.json'
    assert draft or extra.is_file(), 'Release requires the unified supplemental audit.'
    if extra.exists():
        for r in read(extra):
            if r['name'] in base and base[r['name']]['module'] != 'supplemental20':
                continue
            base[r['name']]=r
    for row in base.values():
        assert set(row['axioms']) <= {'propext','Classical.choice','Quot.sound'}, row['name']
        if not draft:
            assert row['module'] != 'supplemental20', row['name']
        for key in ['type_project_dependencies','value_project_dependencies','structural_project_dependencies']:
            assert all(n in base for n in row.get(key,[])), ('missing audited project dependency',row['name'],key)
    return base


def classification(span, exports):
    state=span['claim_review']
    if 'conjecture' in state or 'open_question' in state:
        return 'open_question'
    if span['id'].startswith('E.'):
        return 'mathematics_and_evidence_scope' if exports else 'execution_evidence_or_scope'
    if exports:
        return 'proved_mathematics'
    if 'evidence' in state or 'reconstruction' in state:
        return 'execution_evidence_or_scope'
    return 'notation_or_scope'


def html_index(claims, decls, complete):
    data=json.dumps({'claims':claims,'declarations':decls}, ensure_ascii=False).replace('<', '\\u003c')
    state='Verified edition' if complete else 'Draft edition - verification gates pending'
    return '''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>BFGS claim and Lean proof index</title><style>
:root{color-scheme:light;--ink:#172c45;--accent:#14686b}*{box-sizing:border-box}
body{margin:0;color:var(--ink);font:16px/1.55 system-ui;background:#f7f9fa}
header{padding:30px 5%;background:white;border-bottom:1px solid #dbe1e7}h1{font-size:28px;margin:0 0 8px}
header p{max-width:1000px;margin:8px 0}main{display:grid;grid-template-columns:330px minmax(0,1fr);max-width:1550px;margin:auto}
nav{padding:24px;position:sticky;top:0;height:100vh;overflow:auto}article{padding:30px;background:white;min-height:90vh}
input,select{width:100%;padding:10px;border:1px solid #b4c3cd;border-radius:5px;margin:4px 0 12px;font:inherit}
button{font:inherit;cursor:pointer;color:var(--accent);background:white;border:1px solid #c9d6dc;border-radius:5px;text-align:left;padding:8px 12px;overflow-wrap:anywhere}
nav button{display:block;width:100%;margin:7px 0}button:hover,button:focus{background:#e5f2f1}
.tag{font-size:12px;border:1px solid #bed4d6;border-radius:3px;padding:3px 6px;display:inline-block;margin:3px}
pre{white-space:pre-wrap;overflow-wrap:anywhere;font:13px/1.65 ui-monospace,monospace;background:#f2f5f7;padding:16px;border-radius:5px}
details{border-top:1px solid #dde4e8;padding:12px 0}summary{cursor:pointer;overflow-wrap:anywhere}small{color:#526777}
.deps{display:flex;flex-wrap:wrap;gap:5px}.deps button{font-size:12px}a{color:var(--accent)}
@media(max-width:800px){main{display:block}nav{position:static;height:auto;max-height:450px}article{padding:20px}}
</style><header><h1>Full BFGS: claim and Lean proof index</h1><p>'''+html.escape(state)+'''</p>
<p>Search original claim spans, exact formal statements and proof dependencies. A reviewed correspondence is an English-to-formal statement review; it is not a claim that Lean parses or proves the English text. Open questions and process evidence are classified separately.</p>
<p><a href="../output/pdf/Rigorous_BFGS_Master_Report.pdf">Master report PDF</a> · <a href="CLAIMS.json">Machine-readable claim register</a> · <a href="STATUS.json">Status</a></p></header>
<main><nav><label>Module<select id="module"><option value="">All modules</option></select></label>
<label>Search<input id="search" placeholder="Claim, theorem or hypothesis"></label><div id="list"></div></nav>
<article id="detail"><h2>Select a claim</h2></article></main><script>
const DATA='''+data+''';const $=x=>document.getElementById(x);
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
for(const m of [...new Set(DATA.claims.map(x=>x.module))]){const o=document.createElement('option');o.value=m;o.textContent=m;$('module').append(o)}
function dependencies(r){return [...new Set([...(r.type_project_dependencies||[]),...(r.value_project_dependencies||[]),...(r.structural_project_dependencies||[])])].filter(n=>DATA.declarations[n])}
function theorem(n){const r=DATA.declarations[n];if(!r)return '<p>Unknown declaration</p>';return '<h3>'+esc(n)+'</h3><p>'+esc(r.kind)+' · '+esc(r.module||'source module')+'</p><p>Universe parameters: '+esc((r.level_params||[]).join(', ')||'none')+'</p><pre>'+esc(r.signature)+'</pre><p>Axioms: '+esc(r.axioms.join(', ')||'none')+'</p>'+(r.source_href?'<p><a href="'+esc(r.source_href)+'">Lean source: '+esc(r.source_path)+'</a></p>':'')+(r.source_excerpt?'<details><summary>Compiler-reported source range'+(r.source_excerpt_truncated?' (excerpt; full source linked above)':'')+'</summary><pre>'+esc(r.source_excerpt)+'</pre><small>Generated declarations may refer to the source that produced them; the range is compiler metadata.</small></details>':'')+'<details><summary>Direct project proof/type dependencies ('+dependencies(r).length+')</summary><div class="deps">'+dependencies(r).map(d=>'<button data-theorem="'+esc(d)+'">'+esc(d)+'</button>').join('')+'</div></details>'}
function select(c){location.hash=c.id;$('detail').innerHTML='<h2>'+esc(c.id)+' · Module '+esc(c.module)+'</h2><span class="tag">'+esc(c.classification)+'</span><p>Original lines '+c.original_lines.join('-')+'; corrected source '+esc(c.corrected_source)+'</p><p>'+esc(c.review_note||'See the source correspondence and exact Lean declarations below.')+'</p><details><summary>Corrected source passage</summary><pre>'+esc(c.corrected_excerpt)+'</pre></details><p>Reviewed exports: '+c.exports.length+'</p>'+c.exports.map(n=>'<details><summary>'+esc(n)+'</summary>'+theorem(n)+'</details>').join('');window.scrollTo(0,0)}
for(const c of DATA.claims)c.searchText=[c.id,c.review_note,c.corrected_excerpt,...c.exports,...c.exports.map(n=>DATA.declarations[n].signature)].join(' ').toLowerCase();
function list(){const q=$('search').value.toLowerCase(),m=$('module').value;const xs=DATA.claims.filter(c=>(!m||c.module===m)&&(!q||c.searchText.includes(q)));$('list').innerHTML='<small>'+xs.length+' source spans</small>';for(const c of xs){const b=document.createElement('button');b.textContent=c.id+' · '+c.classification.replaceAll('_',' ');b.onclick=()=>select(c);$('list').append(b)}}
document.addEventListener('click',e=>{const b=e.target.closest('[data-theorem]');if(b){$('detail').innerHTML='<button id="back">Back to source claim</button>'+theorem(b.dataset.theorem);$('back').onclick=()=>{const c=DATA.claims.find(x=>x.id===location.hash.slice(1));if(c)select(c)};window.scrollTo(0,0)}});
$('module').onchange=list;$('search').oninput=list;list();select(DATA.claims.find(c=>c.id===location.hash.slice(1))||DATA.claims[0]);
</script></html>'''


def assemble(draft):
    register=read(ROOT/'audit/REPORT_STATUS.json'); decls=declarations(draft)
    changes=[e for p in sorted((HERE/'edits').glob('*.json')) for e in read(p)]
    assert len({e['id'] for e in changes})==len(changes)
    assert all(e['source'] in {m['source'] for m in register['modules']} for e in changes), 'orphan edit source'
    additions=read(HERE/'authoring/extra_span_exports.json')
    extras=additions['exports']; overrides=additions.get('classification_overrides',{})
    outputs={}; claims=[]; module_records=[]
    for mod in register['modules']:
        sourcepath=REPO/mod['source']; source=sourcepath.read_text()
        assert digest(sourcepath.read_bytes())==mod['source_sha256']
        edits=[e for e in changes if e['source']==mod['source']]
        corrected,mapping=edited_source(source,edits)
        stem=sourcepath.stem
        generated='latex/chapters/'+stem+'.tex';outputs[generated]=corrected
        module_records.append({'module':mod['module'],'original':mod['source'],
            'original_sha256':mod['source_sha256'],'corrected':generated,
            'corrected_sha256':digest(corrected.encode()),'character_map':mapping,
            'edits':[e['id'] for e in edits]})
        previous=0
        for span in mod['coverage_spans']:
            assert span['start_line']==previous+1;previous=span['end_line']
            ranges,ids=mapped_span(source,corrected,mapping,span['start_line'],span['end_line'])
            exports=list(dict.fromkeys(span['verified_exports']+extras.get(span['id'],[])+
                [n for e in edits if e['id'] in ids for n in e['lean_exports']]))
            assert all(n in decls for n in exports), (span['id'],[n for n in exports if n not in decls])
            text='\n'.join('\n'.join(corrected.splitlines()[a-1:b]) for a,b in ranges)
            claims.append({'id':span['id'],'module':mod['module'],'original_source':mod['source'],
                'original_lines':[span['start_line'],span['end_line']],
                'original_sha256':mod['source_sha256'],'corrected_source':generated,
                'corrected_line_ranges':ranges,'corrected_excerpt':text,'edits':ids,
                'classification':overrides.get(span['id'],classification(span,exports)),'exports':exports,
                'review_note':span.get('review_note',''), 'inherited_review':mod['detailed_inventory']})
        assert previous==len(source.splitlines()), mod['module']
        own=[c for c in claims if c['module']==mod['module']]
        rows=[]
        for c in own:
            if c['classification']=='notation_or_scope' and not c['exports']:
                continue
            note=tex(c['classification'].replace('_',' '))
            sample=''
            if c['exports']:
                sample='\\newline {\\scriptsize\\path{'+c['exports'][0]+'}}'
                if len(c['exports'])>1:sample+=r'\newline '+str(len(c['exports']))+' reviewed exports in the full index.'
            rows.append(tex(c['id'])+' & '+str(c['original_lines'][0])+'--'+str(c['original_lines'][1])+' & '+note+sample+r' \\')
        outputs['latex/coverage/'+stem+'.tex']=r'''
\section*{Formal proof correspondence}
\noindent The entries below identify the reviewed source spans. The searchable
claim index supplies every linked declaration's exact statement, axiom set and
project proof dependencies. A sample export is shown here; it is not a claim
that this export alone proves every sentence in the span. Process evidence and
open questions are distinct from mathematical theorems.
\begin{small}\begin{longtable}{@{}p{.16\textwidth}p{.12\textwidth}p{.66\textwidth}@{}}
\toprule Claim & Original lines & Formal correspondence \\
\midrule\endhead
'''+ '\n'.join(rows)+r'''
\bottomrule\end{longtable}\end{small}
'''
    assert len(claims)==172 and len(module_records)==14
    assert {e['id'] for e in changes}=={i for m in module_records for i in m['edits']}, 'unapplied edit'
    outputs['CLAIMS.json']=json.dumps({'schema_version':1,'claims':claims},indent=2,ensure_ascii=False)+'\n'
    outputs['SOURCE_MAP.json']=json.dumps({'schema_version':1,'modules':module_records,'edits':changes},indent=2,ensure_ascii=False)+'\n'
    # Retain direct dependencies of every claim export in the searchable index.
    needed={n for c in claims for n in c['exports']};todo=list(needed)
    while todo:
        r=decls[todo.pop()]
        for key in ['type_project_dependencies','value_project_dependencies','structural_project_dependencies']:
            for n in r.get(key,[]):
                if n in decls and n not in needed:needed.add(n);todo.append(n)
    relevant={n:decls[n] for n in sorted(needed)}
    source_map_path=HERE/'audit/module_sources.json'
    source_inputs=[]
    if source_map_path.is_file():
        source_modules=read(source_map_path); cache={}
        source_inputs.append(source_map_path)
        for row in relevant.values():
            assert row['module'] in source_modules, ('no module source',row['name'])
            source=source_modules[row['module']]; p=REPO/source['source']
            if p not in cache:
                assert digest(p.read_bytes())==source['sha256'], p
                cache[p]=p.read_text().splitlines();source_inputs.append(p)
            row['source_path']=source['source']
            row['source_href']=os.path.relpath(p,HERE)
            r=row.get('source_range')
            if r and r['start_line']>0:
                a=r['start_line'];b=r['end_line']-(r['end_column']==0)
                assert a<=b<=len(cache[p]), ('invalid source range',row['name'],a,b)
                row['source_excerpt']='\n'.join(cache[p][a-1:min(b,a+239)])
                row['source_excerpt_truncated']=b-a+1>240
        outputs['DECLARATION_INDEX.json']=json.dumps(relevant,ensure_ascii=False,indent=2)+'\n'
    else:
        assert draft, 'Release requires module/source provenance.'
    complete=read(HERE/'STATUS.json')['complete'] and not draft
    outputs['PROOF_INDEX.html']=html_index(claims,relevant,complete)
    original_master=(ORIGINAL/'master.tex').read_text()
    preamble=original_master.split(r'\begin{document}')[0]
    preamble=preamble.replace('Working proof record','Corrected Lean edition').replace('10 September 2026','11 September 2026')
    preamble=preamble.replace('Consolidated Proofs and Verification','Corrected Mathematics and Lean Proofs')
    body=original_master.split(r'\mainmatter')[1].split(r'\backmatter')[0]
    body=body.replace('New isolated reruns of the preserved source scripts. The status of finite algebra, rigorous intervals, numerical experiments and analytic proof steps is separated explicitly.',
        'Actual pinned Lean compiler and axiom evidence. Unsupported historical executions are excluded from the operative record.')
    body=re.sub(r'(\\input\{chapters/([^}]+)\})',lambda m:m[1]+'\n'+r'\input{coverage/'+m[2]+'}',body)
    front=(HERE/'authoring/frontmatter.tex').read_text()
    front=front.replace('@@STATUS@@','Verified corrected edition' if complete else 'Draft: final verification gates pending')
    outputs['latex/master.tex']=preamble+r'\begin{document}'+'\n'+front+'\n'+r'\tableofcontents\mainmatter'+'\n'+body+'\n'+r'\backmatter\renewcommand{\ModuleTag}{B}\input{bibliography}\end{document}'+'\n'
    outputs['latex/bibliography.tex']=(HERE/'authoring/bibliography.tex').read_text()
    inputs=[Path(__file__).resolve(), ROOT/'audit/REPORT_STATUS.json', HERE/'STATUS.json',
        HERE/'authoring/extra_span_exports.json',HERE/'authoring/frontmatter.tex',
        HERE/'authoring/bibliography.tex',ORIGINAL/'master.tex',
        *[REPO/m['source'] for m in register['modules']],*sorted((HERE/'edits').glob('*.json')),*source_inputs]
    for p in [HERE/'audit/main/all_safe_declarations.json',HERE/'audit/supplemental/all_safe_declarations.json']:
        if p.is_file():inputs.append(p)
    if draft:
        inputs += [ROOT/'audit/declarations.json',*sorted((ROOT/'audit/claim_review20/fresh').glob('*/REPORTS.json'))]
    outputs['BUILD_INPUTS.json']=json.dumps({'schema_version':1,'draft':draft,'path_base':'repository',
        'sha256':{str(p.relative_to(REPO)):digest(p.read_bytes()) for p in inputs}},indent=2)+'\n'
    return outputs


def main():
    if not __debug__:
        raise RuntimeError('Run without Python optimization; assertion checks must be enabled.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--draft',action='store_true')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args();outputs=assemble(args.draft)
    for name,content in outputs.items():
        p=HERE/name
        if args.check:
            assert p.is_file() and p.read_text()==content, 'generated output differs: '+name
        else:
            p.parent.mkdir(parents=True,exist_ok=True);p.write_text(content)
    print(('Checked' if args.check else 'Generated'),len(outputs),'edition artifacts; 14 modules and 172 source spans.')


if __name__=='__main__':
    main()
