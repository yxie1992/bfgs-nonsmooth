#!/usr/bin/env python3
"""Read-only final source, contract, build and audit integrity gate.

Release tooling T3 (October 2026 edition) adds two checks after the 21 existing
ones, which are unchanged; the gate has 23 checks:
- "October Lean evidence bound to the frozen sources": bfgs_lean_article/AXIOM_AUDIT.json
  and KERNEL_REPLAY.json report PASS, no missing name, nonstandard axiom or replay
  failure, a clean source tree and the pinned Lean version, and the replay names
  lean4checker at the tag of that version with a passing self-test; the commit each
  one audited is an ancestor of HEAD, and no Lean file, Lake configuration, script
  of bfgs_lean_article/scripts, claim ledger or coverage register (for the replay:
  no Lean file, Lake configuration or script) differs between that commit, HEAD and
  the working tree. The reports must also cover what their scripts would collect
  now: the audit's name counts (axiom_audit.ledger_names, coverage_names,
  PACKAGE_PRINCIPAL) and the replay's module closure (kernel_replay.project_modules)
  are recomputed without Lean and compared; and companion/current_verification.tex
  must state the bound counts ("checked <N> Lean names", "(<M> modules;"). It needs
  git history. Any malformed report is recorded as a FAIL of this check.
- "Lean coverage register strict check": editorial/lean_coverage/check_coverage.py
  --strict exits 0.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
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
    expected_run,modules,expected_roots=expected
    modules={modules} if isinstance(modules,str) else set(modules)
    split_schema=entry['name'] in {'positive_formal','geometry_formal','branch_regularity_formal'}
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
    if split_schema:
        hash_map(summary['source_sha256'])
        inputs_path=require_hash(str(run/'INPUTS.json'),summary['input_hashes_sha256'])
        retained_inputs=json.loads(inputs_path.read_text())
        hash_map(retained_inputs)
        frozen=read('bfgs_lean_stage1/master_report/audit/fresh/INPUTS.json')
        if len(frozen)!=summary['frozen_original_audit_inputs_unchanged']:
            raise ValueError('Frozen input count disagrees with the supplement audit')
        for name,digest in frozen.items():
            relative='bfgs_lean_stage1/'+('master_report/audit/'+name[len('@audit/'):] if name.startswith('@audit/') else name)
            if retained_inputs.get(relative)!=digest:
                raise ValueError('Supplement loses or changes a frozen input: '+name)
        if entry['name'] in {'geometry_formal','branch_regularity_formal'}:
            proof_directory=Path('editorial/article_formal') if entry['name']=='geometry_formal' else run.parents[1]
            source_paths={str(proof_directory/(module+'.lean')) for module in modules}|{
                str(run.parents[1]/'DependencyAudit.lean'),str(run.parents[1]/'verify.py')}
            if set(summary['source_sha256'])!=source_paths:
                raise ValueError('Satisfaction audit source manifest must cover every proof module and its complete auditor')
            expected_inputs={
                'bfgs_lean_stage1/'+('master_report/audit/'+name[len('@audit/'):] if name.startswith('@audit/') else name)
                for name in frozen
            }|source_paths|{'bfgs_lean_stage1/master_report/audit/fresh/INPUTS.json',
                            'bfgs_lean_stage1/master_report/DECLARATION_INDEX.json','editorial/BASELINE.json'}
            if set(retained_inputs)!=expected_inputs:
                raise ValueError('Satisfaction input manifest omits or adds unexpected inputs')
        for name,key in [('declarations.json','declarations_sha256'),
                         ('dependency_graph.json','dependency_graph_sha256'),
                         ('commands.json','commands_sha256')]:
            require_hash(str(run/name),summary[key])
        # Source archives intentionally omit compiled caches. An absent cache
        # is reported, never represented as a successful compilation replay.
        if entry['name']=='geometry_formal':
            compiled_hashes=summary['compiled_olean_sha256']
        else:
            if len(modules)!=1:
                raise ValueError('Single-module supplement has unexpected module coverage')
            compiled_hashes={next(iter(modules)):summary['compiled_olean_sha256']}
        if not isinstance(compiled_hashes,dict) or set(compiled_hashes)!=modules:
            raise ValueError('Compiled-object hash manifest differs from the audited modules')
        cache_records={}
        for module,digest in compiled_hashes.items():
            compiled=run/'build'/(module+'.olean')
            if not isinstance(digest,str) or not re.fullmatch(r'[0-9a-f]{64}',digest):
                raise ValueError('Invalid recorded compiled-object hash')
            if checked_path(compiled).exists():
                require_hash(compiled,digest)
                cache_records[module]='Present compiled cache matches its recorded hash'
            else:
                cache_records[module]='Compiled cache omitted; retained hash only, not fresh proof evidence'
        cache_status=cache_records if entry['name']=='geometry_formal' else cache_records[next(iter(modules))]
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
    if entry['name'] in {'geometry_formal','branch_regularity_formal'}:
        compiles=[command for command in command_lines if '-o' in command]
        if len(compiles)!=len(modules) or {Path(command[-1]).stem for command in compiles}!=modules:
            raise ValueError('Satisfaction audit must actually compile every owned proof module')
        for command in compiles:
            module=Path(command[-1]).stem
            if not command[-1].endswith('/'+str(proof_directory/(module+'.lean'))) or not command[command.index('-o')+1].endswith('/'+str(run/'build'/(module+'.olean'))):
                raise ValueError('Satisfaction compile source or output path differs from its recorded run')
    audit_text=''
    version_evidence=[]
    for command in commands:
        is_version=command['command'][-2:]==['lean','--version']
        is_audit=any(str(part).endswith('/DependencyAudit.lean') for part in command['command'])
        if split_schema:
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
    marker={'positive_formal':'ARTICLE_POSITIVE_AUDIT','negative_formal':'NEGATIVE_COVARIANCE_AUDIT',
            'geometry_formal':'ARTICLE_GEOMETRY_STRUCTURAL_AUDIT',
            'branch_regularity_formal':'ARTICLE_BRANCH_REGULARITY_AUDIT'}[entry['name']]
    pattern=re.escape(marker)+r' (\{.*\})'
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
    owned={name for name,row in graph.items() if row['module'] in modules}
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
        if split_schema:
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

try:
    geometry=root['supplemental_structural_audit']
    if geometry['name']!='geometry_formal':
        raise ValueError('Missing dedicated geometry structural audit registration')
    details=verify_supplement(geometry,('editorial/satisfaction_review/formal/runs/geometry_structural_01',
                                        {'ArticleGeometry','ConvexBalance'},14))
    old_run='editorial/article_formal/runs/20260912_article_geometry_04'
    if supp['run_directory']!=old_run or read(old_run+'/SUMMARY.json')!=supp:
        raise ValueError('Historical geometry summary no longer matches its retained provenance')
    old_declarations=read(old_run+'/declarations.json')
    if old_declarations!=root['supplemental_declarations']:
        raise ValueError('Historical geometry declarations no longer match the retained root contracts')
    def exact_contracts(rows):
        fields=['name','module','kind','signature','axioms','unsafe','partial']
        if len({row['name'] for row in rows})!=len(rows):
            raise ValueError('Duplicate geometry declarations in a correspondence comparison')
        return sorted(({key:row[key] for key in fields} for row in rows),key=lambda row:row['name'])
    if exact_contracts(old_declarations)!=exact_contracts(read(geometry['declarations'])):
        raise ValueError('Strict geometry audit changes a prior declaration name, exact type or axiom set')
    details['unchanged_prior_geometry_contracts']=14
    details['historical_run_preserved']=old_run
    record('Strict geometry structural audit and original contract agreement',True,details)
except (KeyError,TypeError,ValueError,OSError) as error:
    record('Strict geometry structural audit and original contract agreement',False,str(error))

try:
    branch=root['supplemental_branch_regularity_audit']
    if branch['name']!='branch_regularity_formal':
        raise ValueError('Missing dedicated actual-branch regularity audit registration')
    details=verify_supplement(branch,('editorial/satisfaction_review/branch_formal/runs/branch_regularity_01',
                                      'ArticleBranchRegularity',3))
    required_roots={'ArticleBranchRegularity.branch_not_twice_differentiable_zero',
                    'ArticleBranchRegularity.whitened_branch_not_twice_differentiable_zero',
                    'ArticleBranchRegularity.smoothLocalFailure_with_branch_obstruction'}
    if {row['name'] for row in read(branch['declarations'])}!=required_roots:
        raise ValueError('Actual-branch audit omits a required original, whitened or combined endpoint theorem')
    details['literal_combined_failure_endpoint']='ArticleBranchRegularity.smoothLocalFailure_with_branch_obstruction'
    record('Actual branch regularity and combined lower-failure audit',True,details)
except (KeyError,TypeError,ValueError,OSError) as error:
    record('Actual branch regularity and combined lower-failure audit',False,str(error))

try:
    binding=root['supplemental_cache_binding']
    manifest_path=require_hash(binding['manifest'],binding['manifest_sha256'])
    summary_path=require_hash(binding['summary'],binding['summary_sha256'])
    binding_run=Path(binding['manifest']).parent
    if not re.fullmatch(r'editorial/satisfaction_review/cache_binding/runs/[A-Za-z0-9_-]+',str(binding_run)) or Path(binding['manifest']).name!='MANIFEST.json' or binding['summary']!=str(binding_run/'SUMMARY.json'):
        raise ValueError('Cache receipt must identify one versioned satisfaction-review run')
    cache=json.loads(manifest_path.read_text())
    receipt=json.loads(summary_path.read_text())
    if cache.get('schema_version')!=2 or cache.get('status')!='SEALED_TRUSTED_INCREMENTAL_CACHE' or cache.get('run_directory')!=str(binding_run):
        raise ValueError('Unknown or incomplete cache-binding manifest')
    if receipt.get('status')!='PASS' or receipt.get('run_directory')!=str(binding_run) or receipt.get('manifest')!=binding['manifest'] or receipt.get('manifest_sha256')!=binding['manifest_sha256']:
        raise ValueError('Cache-binding summary disagrees with the registered manifest')
    if cache.get('build_command')!=['lake','build','BfgsVerification'] or cache.get('successful_rehash_build') is not False or cache.get('independent_cached_output_hash_validation') is not True:
        raise ValueError('Cache receipt misstates its actual build/hash-validation method')
    if any(cache.get(key) is not True for key in ['inherited_LEAN_PATH_cleared','inherited_LEAN_SRC_PATH_cleared']) or any(cache.get(key) is not False for key in ['fresh_original_library_build','fresh_mathlib_build']):
        raise ValueError('Cache receipt misstates its controlled-path or incremental-build scope')
    for group in ['pinned_input_files','evidence_files','prior_attempt_evidence']:
        if not cache.get(group):
            raise ValueError('Cache receipt lacks '+group)
        for name,data in cache[group].items():
            if require_hash(name,data['sha256']).stat().st_size!=data['bytes']:
                raise ValueError('Cache receipt artifact size differs: '+name)
    helper='editorial/satisfaction_review/cache_binding.py'
    require_hash(helper,cache['pinned_input_files'][helper]['sha256'])
    if receipt['object_count']!=len(cache['objects']) or receipt['sealed_cache_file_count']!=len(cache['cache_files']) or receipt['verification']['status']!='PASS':
        raise ValueError('Cache-binding counts or recorded verification disagree')
    details={'manifest':binding['manifest'],'manifest_sha256':binding['manifest_sha256'],
             'summary':binding['summary'],'summary_sha256':binding['summary_sha256'],
             'object_count':len(cache['objects']),'sealed_cache_file_count':len(cache['cache_files']),
             'method':'Ordinary pinned Lake build plus independent cached binary-output hash checks; no successful --rehash or clean rebuild claimed',
             'retained_source_and_execution_receipts':'authenticated'}
    cache_paths=[ROOT/'bfgs_lean_stage1'/name for name in ['.lake','.toolchain']]
    if any((path.exists() or path.is_symlink()) and not path.is_dir() for path in cache_paths):
        raise ValueError('Pinned cache/toolchain path is invalid or a broken symlink')
    cache_presence=[path.is_dir() for path in cache_paths]
    if any(cache_presence) and not all(cache_presence):
        raise ValueError('Pinned cache/toolchain is only partially available')
    if all(cache_presence):
        env=os.environ.copy()
        env.pop('LEAN_PATH',None)
        env.pop('LEAN_SRC_PATH',None)
        command=[sys.executable,helper,'--check','--manifest',binding['manifest'],'--root',str(ROOT)]
        result=subprocess.run(command,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        details['current_read_only_check']={'command':command,'exit_code':result.returncode,
            'inherited_LEAN_PATH_cleared':True,'inherited_LEAN_SRC_PATH_cleared':True,
            'stdout':result.stdout,'stderr':result.stderr}
        if result.returncode:
            raise ValueError('Current cache-binding helper rejected the available cache bytes: '+json.dumps(details))
        actual=json.loads(result.stdout)
        if actual.get('status')!='PASS' or actual.get('read_only_check') is not True or actual.get('manifest_sha256')!=binding['manifest_sha256'] or actual.get('object_count')!=len(cache['objects']) or actual.get('sealed_cache_file_count')!=len(cache['cache_files']):
            raise ValueError('Current cache helper result disagrees with its receipt')
        details['current_cache_bytes_verified']=True
    else:
        details['current_cache_bytes_verified']=False
        details['source_only_scope']='Pinned caches are absent. Retained receipts are authenticated; present cache bytes and fresh compilation are not checked. Archive replay requires successful before/after cache checks.'
    record('Reused Lean cache binding and controlled-path receipts',True,details)
except (KeyError,TypeError,ValueError,OSError) as error:
    record('Reused Lean cache binding and controlled-path receipts',False,str(error))

for file,key in [('positive_contract_review.json','article_sha256'),('negative_contract_review.json','article_file_sha256'),('root_contract_review.json','article_file_sha256')]:
 d=read('editorial/'+file);changed=[p for p,h in d[key].items() if sha(ROOT/p)!=h]
 record('Reviewed source contracts: '+file,not changed,changed)
ledger=read('editorial/CLAIM_LEDGER.json')
record('All named article statements mapped',not ledger['unmapped_named_article_statements'])
record('Complete companion source and export preservation',len(ledger['companion_source_span_records'])==172 and len({n for r in ledger['companion_source_span_records'] for n in r['full_formal_exports']})==3087)
record('Root mathematical deductions have no remaining obligations',not root['remaining_math_obligations'])
for d in read('editorial/logs/document_checks.json')['documents']:
 details={'pages':d['pages'],'sha256':d['sha256']}
 try:matches=sha(ROOT/d['pdf'])==d['sha256']
 except OSError as error:matches=False;details['error']=type(error).__name__+': '+str(error)
 record(d['document']+' PDF matches successful resolved, overflow-free build',matches and not d['errors'] and not d['overfull_warnings'],details)
for p in [ROOT/'paper/sections',ROOT/'paper/appendices',ROOT/'paper/statements']:
 todo=[]
 for f in p.glob('*.tex'):
  if re.search(r'\b(TODO|TBD|FIXME|placeholder)\b',f.read_text()):todo.append(str(f.relative_to(ROOT)))
 record('No substantive authoring placeholders in '+p.name,not todo,todo)

# T3 (October 2026): bind the October Lean evidence to these sources; it is not re-run here.
LEAN_INPUTS=['*.lean','*lean-toolchain','*lakefile.toml','*lake-manifest.json','bfgs_lean_article/scripts']
def load_script(name):
    import importlib.util
    sys.dont_write_bytecode=True
    spec=importlib.util.spec_from_file_location('release_'+name,ROOT/'bfgs_lean_article/scripts'/(name+'.py'))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
def expected_audit():
    # The audit's own name collection, recomputed from the current ledger and registers (no Lean).
    a=load_script('axiom_audit');principal,article,companion,private=a.ledger_names();coverage=a.coverage_names()
    return {'declarations_checked':len(set(article)|set(companion)|set(coverage)|set(a.PACKAGE_PRINCIPAL)),
            'ledger_principal_exports':len(principal),'ledger_cited_exports':len(article),
            'ledger_companion_exports':len(companion),'coverage_register_names':len(coverage),
            'private_names_not_referable':private}
def expected_replay():
    # The replay's module closure, recomputed from the current lakefiles and imports (no Lean).
    k=load_script('kernel_replay');modules=k.project_modules();names=sorted(modules)
    prefixes={m for m in names if any(o.startswith(m+'.') for o in names)}
    imports_only=sorted(m for m in prefixes if all(l.startswith('import ') for l in k.code_lines(modules[m])))
    roots={}
    for m in names:roots[m.split('.')[0]]=roots.get(m.split('.')[0],0)+1
    return {'modules_in_closure':len(names),'modules_replayed':len(names)-len(imports_only),
            'imports_only_modules_not_replayed':imports_only,'modules_by_root':roots}
def git_output(*argv):
    result=subprocess.run(['git',*argv],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    if result.returncode:
        raise ValueError('git '+' '.join(argv)+' failed (git history is required): '+result.stderr.strip())
    return result.stdout
try:
    pinned=(ROOT/'bfgs_lean_article/lean-toolchain').read_text().strip().rsplit(':v',1)[-1]
    if pinned!=(ROOT/'bfgs_lean_stage1/lean-toolchain').read_text().strip().rsplit(':v',1)[-1]:
        raise ValueError('The October package and the main library pin different Lean versions')
    head=git_output('rev-parse','HEAD').strip()
    evidence={}
    for name,paths in [('AXIOM_AUDIT.json',LEAN_INPUTS+['editorial/CLAIM_LEDGER.json','editorial/lean_coverage/register']),
                       ('KERNEL_REPLAY.json',LEAN_INPUTS)]:
        relative='bfgs_lean_article/'+name
        report=read(relative)
        if report.get('status')!='PASS' or report.get('source_tree_clean') is not True:
            raise ValueError(name+' is not a PASS on a clean source tree')
        if not report.get('lean_version','').startswith('Lean (version '+pinned+','):
            raise ValueError(name+' was not produced with the pinned Lean '+pinned)
        if name=='AXIOM_AUDIT.json' and (report.get('missing_or_unresolved')!=[] or report.get('nonstandard_axioms')!={} or not report.get('declarations_checked')):
            raise ValueError('Axiom audit reports missing names or nonstandard axioms')
        if name=='KERNEL_REPLAY.json' and (report.get('failures')!=[] or not report.get('modules_replayed') or report.get('checker',{}).get('self_test')!='PASS'):
            raise ValueError('Kernel replay reports failures or lacks its checker self-test')
        if name=='KERNEL_REPLAY.json' and report['checker'].get('tag')!='v'+pinned:
            raise ValueError('Kernel replay used lean4checker '+str(report['checker'].get('tag'))+', not v'+pinned)
        commit=report.get('source_commit','')
        if not re.fullmatch(r'[0-9a-f]{40}',commit):
            raise ValueError(name+' lacks its audited commit')
        if subprocess.run(['git','merge-base','--is-ancestor',commit,head],cwd=ROOT).returncode:
            raise ValueError(name+' audited '+commit+', which is not an ancestor of HEAD '+head)
        since=git_output('diff','--name-only',commit,head,'--',*paths).split()
        if since:
            raise ValueError(name+' audited '+commit+'; Lean or ledger inputs changed since: '+', '.join(since[:20]))
        uncommitted=git_output('status','--porcelain','--untracked-files=all','--',*paths).splitlines()
        if uncommitted:
            raise ValueError(name+': the working tree changes Lean or ledger inputs: '+', '.join(uncommitted[:20]))
        # The bound sources equal those of the audited commit, so the scripts' own collection must match the report.
        expected=expected_audit() if name=='AXIOM_AUDIT.json' else expected_replay()
        wrong={key:[report.get(key),value] for key,value in expected.items() if report.get(key)!=value}
        if wrong:
            raise ValueError(name+' does not cover the names or modules recomputed from the sources: '+json.dumps(wrong)[:600])
        evidence[name]={'sha256':sha(ROOT/relative),'audited_commit':commit,'lean_version':report['lean_version'],
                        'bound_paths':paths,'unchanged_since_audited_commit':True,
                        'recomputed_from_sources':{key:value for key,value in expected.items() if not isinstance(value,(list,dict))},
                        **({'declarations_checked':report['declarations_checked']} if name=='AXIOM_AUDIT.json' else
                           {'modules_replayed':report['modules_replayed'],'checker':report['checker']})}
    text=(ROOT/'companion/current_verification.tex').read_text()
    stated=['checked '+str(evidence['AXIOM_AUDIT.json']['declarations_checked'])+' Lean names','('+str(evidence['KERNEL_REPLAY.json']['modules_replayed'])+' modules;']
    if not all(phrase in re.sub(r'\s+',' ',text) for phrase in stated):
        raise ValueError('companion/current_verification.tex does not state the counts of the bound reports: '+json.dumps(stated))
    record('October Lean evidence bound to the frozen sources',True,{'head':head,'reports':evidence,'companion_states':stated,
           'scope':'Recorded October axiom audit and kernel replay, bound by git history; not re-run here.'})
except Exception as error:
    record('October Lean evidence bound to the frozen sources',False,type(error).__name__+': '+str(error))
coverage=subprocess.run([sys.executable,'editorial/lean_coverage/check_coverage.py','--strict'],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
coverage_lines=coverage.stdout.splitlines()
record('Lean coverage register strict check',coverage.returncode==0,{'command':['python3','editorial/lean_coverage/check_coverage.py','--strict'],
       'exit_code':coverage.returncode,'total':next((l for l in coverage_lines if l.startswith('TOTAL: ')),None),
       'open_discrepancies':sum(1 for l in coverage_lines if l.startswith('DISCREPANCY ')),
       'problems':[l for l in coverage_lines if l.startswith('PROBLEM ')][:20],'stderr':coverage.stderr[-2000:]})
out={'status':'PASS' if all(r['status']=='PASS' for r in results) else 'FAIL','scope':'Read-only release inputs; fresh compilation is evidenced by separate hashed logs. Page-level visual approval is recorded separately. The October axiom audit and kernel replay are bound to the sources by git history, not re-run.','checks':results}
(ROOT/'editorial/logs/release_integrity.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
if out['status']!='PASS':raise SystemExit(1)
