#!/usr/bin/env python3
"""Read-only final source, contract, build and audit integrity gate."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
def read(p):return json.loads((ROOT/p).read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
results=[]
def record(name,condition,details=None):
 results.append({'check':name,'status':'PASS' if condition else 'FAIL','details':details})
base=read('editorial/BASELINE.json')
changed=[p for p,h in base['files'].items() if sha(ROOT/p)!=h]
record('Original research, corrected edition and dependencies unchanged',not changed,changed)
inputs=read('editorial/formal_audit/runs/20260912_narrative/INPUTS.json')
changed=[]
for p,h in inputs.items():
 path=ROOT/'editorial/formal_audit'/p[7:] if p.startswith('@audit/') else ROOT/'bfgs_lean_stage1'/p
 if sha(path)!=h:changed.append(p)
record('Every input to the fresh main audit retains its hash',not changed,{'inputs':len(inputs),'changed':changed})
main=read('editorial/formal_audit/runs/20260912_narrative/SUMMARY.json')
record('Fresh pinned main and correction audit',main['status']=='PASS' and not main['changed_inputs'])
root=read('editorial/root_contract_review.json');supp=root['supplemental_audit']
changed=[p for p,h in supp['source_sha256'].items() if sha(ROOT/p)!=h]
record('Fresh article-only audit and its exact mathematical inputs',supp['status']=='PASS' and not changed and not supp['unchecked_missing_unsafe_partial'],{'module_owned_declarations':supp['module_owned_declarations'],'transitive_dependencies':supp['transitive_checked_declarations'],'changed':changed})
allowed={'propext','Classical.choice','Quot.sound'}
record('Article-only transitive axiom policy',set(supp['axioms'])<=allowed,supp['axioms'])

# Supplemental proof reports are authenticated as retained evidence here.
# Compilation is replayed by the separate fresh-extraction validation.
def checked_path(relative):
    path=Path(relative)
    if path.is_absolute() or '..' in path.parts:
        raise ValueError('Audit artifact must use a repository-relative path: '+str(relative))
    resolved=(ROOT/path).resolve()
    if not resolved.is_relative_to(ROOT.resolve()):
        raise ValueError('Audit artifact escapes the repository: '+str(relative))
    return resolved

def require_hash(relative,expected):
    if not isinstance(expected,str) or not re.fullmatch(r'[0-9a-f]{64}',expected):
        raise ValueError('Invalid SHA256 for '+str(relative))
    path=checked_path(relative)
    if not path.is_file() or sha(path)!=expected:
        raise ValueError('Missing or changed audit artifact: '+str(relative))
    return path

def hash_map(mapping):
    if not isinstance(mapping,dict) or not mapping:
        raise ValueError('Empty or invalid audit hash manifest')
    for path,digest in mapping.items():
        require_hash(path,digest)

def verify_supplement(entry,expected):
    expected_run,module,expected_roots=expected
    run=Path(expected_run)
    if entry['summary']!=str(run/'SUMMARY.json') or entry['declarations']!=str(run/'declarations.json'):
        raise ValueError('Unexpected supplement run or declaration artifact')
    summary_path=require_hash(entry['summary'],entry['summary_sha256'])
    require_hash(entry['declarations'],entry['declarations_sha256'])
    summary=json.loads(summary_path.read_text())
    if summary.get('run_directory')!=expected_run or summary.get('status')!='PASS':
        raise ValueError('Supplement summary is not the required successful run')
    pinned=(ROOT/'bfgs_lean_stage1/lean-toolchain').read_text().strip().rsplit(':v',1)[-1]
    if not summary.get('lean_version','').startswith('Lean (version '+pinned+','):
        raise ValueError('Supplement compiler differs from the pinned toolchain')
    if summary.get('unchecked_missing_unsafe_partial')!=[]:
        raise ValueError('Supplement records unchecked, missing, unsafe or partial dependencies')
    if summary.get('kernel_root_type_and_value_agreement') is not True:
        raise ValueError('Supplement lacks exact checked root type/value agreement')
    if 'agrees per root with independent ordinary traversal' not in summary.get('collector',''):
        raise ValueError('Supplement lacks independent ordinary collector agreement')
    if not set(summary.get('axioms',[]))<=allowed:
        raise ValueError('Supplement exceeds the standard axiom policy')

    cache_status='No compiled object hash is part of this retained manifest'
    if entry['name']=='positive_formal':
        hash_map(summary['source_sha256'])
        inputs_path=require_hash(str(run/'INPUTS.json'),summary['input_hashes_sha256'])
        retained_inputs=json.loads(inputs_path.read_text())
        hash_map(retained_inputs)
        frozen=read('bfgs_lean_stage1/master_report/audit/fresh/INPUTS.json')
        if len(frozen)!=summary['frozen_original_audit_inputs_unchanged']:
            raise ValueError('Frozen input count disagrees with the positive audit')
        for name,digest in frozen.items():
            relative='bfgs_lean_stage1/'+('master_report/audit/'+name[len('@audit/'):] if name.startswith('@audit/') else name)
            if retained_inputs.get(relative)!=digest:
                raise ValueError('Positive supplement loses or changes a frozen input: '+name)
        for name,key in [('declarations.json','declarations_sha256'),
                         ('dependency_graph.json','dependency_graph_sha256'),
                         ('commands.json','commands_sha256')]:
            require_hash(str(run/name),summary[key])
        # Source archives intentionally omit compiled caches. An absent cache
        # is reported, never represented as a successful compilation replay.
        compiled=run/'build/MixedBenchmark.olean'
        digest=summary['compiled_olean_sha256']
        if not isinstance(digest,str) or not re.fullmatch(r'[0-9a-f]{64}',digest):
            raise ValueError('Invalid recorded compiled-object hash')
        if checked_path(compiled).exists():
            require_hash(compiled,digest)
            cache_status='Present compiled cache matches its recorded hash'
        else:
            cache_status='Compiled cache omitted; retained hash only, not fresh proof evidence'
    else:
        hash_map(summary['input_sha256'])
        hash_map(summary['output_sha256'])
        required={'00_version.log','01_search_path.log','02_compile.log',
                  '03_dependency_audit.log','audit_summary.json','commands.json',
                  'declarations.json','dependency_graph.json'}
        if not {str(run/name) for name in required}<=set(summary['output_sha256']):
            raise ValueError('Negative output manifest omits required retained artifacts')

    commands=read(str(run/'commands.json'))
    if not commands or any(command.get('exit_code')!=0 for command in commands):
        raise ValueError('Supplement command evidence is absent or unsuccessful')
    command_lines=[command['command'] for command in commands]
    if not any('-o' in command and any(str(part).endswith('.lean') for part in command) for command in command_lines):
        raise ValueError('Supplement lacks an actual Lean compilation command')
    if not any(any(str(part).endswith('/DependencyAudit.lean') for part in command) for command in command_lines):
        raise ValueError('Supplement lacks an actual dependency audit command')
    audit_text=''
    version_evidence=[]
    for command in commands:
        is_version=command['command'][-2:]==['lean','--version']
        is_audit=any(str(part).endswith('/DependencyAudit.lean') for part in command['command'])
        if entry['name']=='positive_formal':
            for stream in ('stdout','stderr'):
                path=require_hash(command[stream],command[stream+'_sha256'])
                if is_audit:
                    audit_text+=path.read_text()
                if is_version and stream=='stdout':
                    version_evidence.append(path.read_text().strip())
        else:
            path=command['log']
            require_hash(path,summary['output_sha256'][path])
            if is_audit:
                audit_text+=checked_path(path).read_text()
            if is_version:
                version_evidence.append(checked_path(path).read_text().strip())
    if version_evidence!=[summary['lean_version']]:
        raise ValueError('Actual compiler version log disagrees with the summary')
    audit=read(str(run/'audit_summary.json'))
    pattern=r'(?:ARTICLE_POSITIVE_AUDIT|NEGATIVE_COVARIANCE_AUDIT) (\{.*\})'
    matches=re.findall(pattern,audit_text)
    if len(matches)!=1 or json.loads(matches[0])!=audit:
        raise ValueError('Actual audit log does not match the retained audit summary')
    for key,value in audit.items():
        if summary.get(key)!=value:
            raise ValueError('Final and raw supplement summaries disagree: '+key)

    declarations=read(str(run/'declarations.json'))
    graph_rows=read(str(run/'dependency_graph.json'))
    graph={row['name']:row for row in graph_rows}
    roots={row['name']:row for row in declarations}
    graph_names=set(graph)
    if len(graph)!=len(graph_rows) or len(roots)!=len(declarations):
        raise ValueError('Duplicate declaration names in audit artifacts')
    if len(roots)!=expected_roots or len(roots)!=summary['module_owned_declarations']:
        raise ValueError('Supplement root coverage count disagrees')
    if len(graph)!=summary['transitive_checked_declarations']:
        raise ValueError('Supplement structural dependency count disagrees')
    owned={name for name,row in graph.items() if row['module']==module}
    if owned!=set(roots):
        raise ValueError('Module-owned declarations or helpers are missing')
    axioms=set()
    for name,row in graph.items():
        if row.get('unsafe') is not False or row.get('partial') is not False:
            raise ValueError('Unsafe/partial or unclassified graph node: '+name)
        if not set(row['dependencies'])<=graph_names:
            raise ValueError('Unresolved structural graph edge: '+name)
        if row['kind']=='axiom':
            axioms.add(name)
            if name not in allowed:
                raise ValueError('Unapproved transitive axiom: '+name)
        if entry['name']=='positive_formal':
            split=set(row['type_dependencies'])|set(row['value_dependencies'])|set(row['structural_dependencies'])
            if split!=set(row['dependencies']):
                raise ValueError('Type/value/structural edge partition disagrees: '+name)
    if axioms!=set(summary['axioms']):
        raise ValueError('Graph and summary axiom sets disagree')
    all_reached=set()
    for name,row in roots.items():
        if row.get('ordinary_collector_agrees') is not True:
            raise ValueError('No ordinary collector agreement for '+name)
        if row.get('unsafe') is not False or row.get('partial') is not False or not row.get('signature'):
            raise ValueError('Invalid checked root contract: '+name)
        edges=row['structural_dependencies'] if entry['name']=='negative_formal' else row['dependencies']
        if set(edges)!=set(graph[name]['dependencies']):
            raise ValueError('Root and graph dependencies disagree: '+name)
        if not set(row['dependencies'])<=set(edges):
            raise ValueError('Structural graph loses ordinary root dependencies: '+name)
        pending=[name]
        reached=set()
        while pending:
            current=pending.pop()
            if current not in reached:
                reached.add(current)
                pending.extend(graph[current]['dependencies'])
        all_reached.update(reached)
        reachable_axioms=axioms&reached
        if reachable_axioms!=set(row['axioms']) or not reachable_axioms<=allowed:
            raise ValueError('Full graph and per-root collector axiom sets disagree: '+name)
    if all_reached!=graph_names:
        raise ValueError('Supplement graph contains disconnected or unaudited rows')
    return {'run':expected_run,'module_owned_declarations':len(roots),
            'transitive_checked_declarations':len(graph),'axioms':sorted(axioms),
            'source_and_retained_artifact_hashes':'verified','compiled_cache':cache_status,
            'type_value_agreement':'recorded by hashed kernel audit; actual log agrees',
            'collector_agreement':'per-root flag and independent retained full-graph axiom reachability agree'}

expected_supplements={
    'positive_formal':('editorial/narrative_rebuild/positive_formal/runs/20260912_mixed_benchmark_02','MixedBenchmark',3),
    'negative_formal':('editorial/narrative_rebuild/negative_formal/runs/20260912_covariance_01','negative_scaling',11),
}
try:
    manifest=read('editorial/narrative_rebuild/FORMAL_SUPPLEMENTS.json')
    entries=manifest['supplements']
    names=[entry['name'] for entry in entries]
    if len(names)!=len(expected_supplements) or set(names)!=set(expected_supplements):
        raise ValueError('Formal supplement manifest must contain exactly the required positive02 and negative01 runs')
    for entry in entries:
        details=verify_supplement(entry,expected_supplements[entry['name']])
        record('Narrative formal supplement integrity: '+entry['name'],True,details)
except (KeyError,TypeError,ValueError,OSError) as error:
    record('Narrative formal supplement integrity',False,str(error))

for file,key in [('positive_contract_review.json','article_sha256'),('negative_contract_review.json','article_file_sha256'),('root_contract_review.json','article_file_sha256')]:
 d=read('editorial/'+file);changed=[p for p,h in d[key].items() if sha(ROOT/p)!=h]
 record('Reviewed source contracts: '+file,not changed,changed)
ledger=read('editorial/CLAIM_LEDGER.json')
record('All named article statements mapped',not ledger['unmapped_named_article_statements'])
record('Complete companion source and export preservation',len(ledger['companion_source_span_records'])==172 and len({n for r in ledger['companion_source_span_records'] for n in r['full_formal_exports']})==3087)
record('Root mathematical deductions have no remaining obligations',not root['remaining_math_obligations'])
for d in read('editorial/logs/document_checks.json')['documents']:
 record(d['document']+' PDF matches successful resolved, overflow-free build',sha(ROOT/d['pdf'])==d['sha256'] and not d['errors'] and not d['overfull_warnings'],{'pages':d['pages'],'sha256':d['sha256']})
for p in [ROOT/'paper/sections',ROOT/'paper/appendices',ROOT/'paper/statements']:
 todo=[]
 for f in p.glob('*.tex'):
  if re.search(r'\b(TODO|TBD|FIXME|placeholder)\b',f.read_text()):todo.append(str(f.relative_to(ROOT)))
 record('No substantive authoring placeholders in '+p.name,not todo,todo)
out={'status':'PASS' if all(r['status']=='PASS' for r in results) else 'FAIL','scope':'Read-only release inputs; fresh compilation is evidenced by separate hashed logs. Page-level visual approval is recorded separately.','checks':results}
(ROOT/'editorial/logs/release_integrity.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
if out['status']!='PASS':raise SystemExit(1)
