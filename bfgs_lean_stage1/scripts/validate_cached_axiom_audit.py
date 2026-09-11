#!/usr/bin/env python3
"""Validate public cached-collector evidence; no historical scratch path is read."""
from pathlib import Path
import argparse,hashlib,json,re,runpy
ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'audit/cached_axiom_evidence'
MARKER=b'\n#print axioms BfgsVerification.CompressionAlgebra.gram_numerator_identity'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def read(path):return json.loads(path.read_text())
def sha(data):return hashlib.sha256(data).hexdigest()
def index(items):
 result={x['theorem']:x for x in items}
 assert len(result)==len(items),'duplicate actual declaration'
 return result

def same_items(old,new):
 for name,item in old.items():
  assert name in new,('missing declaration',name)
  assert item['signature']==new[name]['signature'],('type mismatch',name)
  assert set(item['axioms'])==set(new[name]['axioms']),('axiom mismatch',name)

def standard_scope(log,names):
 assert 'error:' not in log
 reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log)
 assert len(reports)==len(names)==len(set(names))
 result={n:set(a.replace(',',' ').split()) for n,a in reports}
 assert set(result)==set(names)
 assert all(a<=ALLOWED for a in result.values())
 return result

def check_static():
 manifest=read(BASE/'evidence_manifest.json')
 for path,expected in manifest['static_hashes'].items():
  assert sha((ROOT/path).read_bytes())==expected,path
 assert manifest['baseline_release17']=='1f8208745a50b721c4a12a39dc0bd8b5445fff1b'
 standard=index(read(BASE/'standard17_declarations.json'))
 assert len(standard)==7684
 log=(BASE/'standard17_axioms.log').read_text()
 records=[json.loads(l[len('BFGS_AUDIT '):]) for l in log.splitlines() if l.startswith('BFGS_AUDIT ')]
 assert re.findall(r'^BFGS_AUDIT_COUNT (\d+)$',log,re.M)==['7684']
 assert 'error:' not in log and 'exit_code=0' in log
 assert index(records)==standard
 cached=index(read(BASE/'cached17_reports.json'))
 assert len(cached)==7721
 assert {n for n,x in cached.items() if x['isTheorem']}==set(standard)
 same_items(standard,cached)
 prior=index(read(BASE/'standard16_declarations.json'))
 assert len(prior)==7486
 same_items(prior,standard)
 scope=read(BASE/'scope17_manifest.json')
 names=scope['declarations'];assert len(names)==152
 values=standard_scope((BASE/'scope17_axioms_contracts.log').read_text(),names)
 for name in names:assert set(cached[name]['axioms'])==values[name],name
 stats=read(BASE/'cached17_stats.json')
 assert stats['missing']==[] and stats['actualTheorems']==7684
 assert set(stats['axiomSeeds'])==ALLOWED
 assert (BASE/'cycle_checks.log').read_text().count('GRAPH_CASE_OK ')==7
 assert all(set(x['axioms'])<=ALLOWED for x in cached.values())
 return standard,cached

def checked_scope18():
 actual=read(ROOT/'audit/module_m_literal_completion_declarations.json')
 expected=read(BASE/'expected_scope18_manifest.json')
 assert actual['declarations']==expected['declarations'] and len(actual['declarations'])==18
 assert actual['targets']==expected['targets'] and len(actual['targets'])==2
 sources=[x for s in actual['scopes'] for x in s['sources']]
 originals=[x for s in expected['scopes'] for x in s['sources']]
 assert [(s['path'],s['sha256']) for s in sources]==[(s['path'],s['sha256']) for s in originals]
 assert len(sources)==3
 for source in sources:assert sha((ROOT/source['path']).read_bytes())==source['sha256'],source['path']
 return actual

def check_adoption(scope18):
 original=(BASE/'OriginalAudit17.lean.txt').read_bytes()
 reviewed=(BASE/'ReviewedProposedAudit17.lean.txt').read_bytes()
 before=(BASE/'OriginalAuditBeforeCache.lean.txt').read_bytes()
 candidate=(BASE/'ProposedCurrentAudit.lean').read_bytes()
 actual=(ROOT/'Audit.lean').read_bytes()
 record=read(BASE/'adoption_provenance.json')
 old_prefix=original[:original.index(MARKER)];new_prefix=reviewed[:reviewed.index(MARKER)]
 before_tail=before[before.index(MARKER):]
 assert before.startswith(old_prefix)
 assert before_tail.startswith(original[original.index(MARKER):])
 assert candidate==new_prefix+before_tail
 assert actual==candidate,'actual Audit differs from reviewed prefix/current-tail proposal'
 assert sha(before)==record['before_sha256']
 assert sha(candidate)==record['candidate_sha256']
 assert sha(before_tail)==record['preserved_tail_sha256']
 assert sha(new_prefix)==record['reviewed_cached_prefix_sha256']
 assert record['registered_targets']==251
 for declaration,target in scope18['targets']:
  for line in [f'#print {target}',f'example : {target} := {declaration}',f'#print axioms {declaration}']:
   assert ('\n'+line+'\n').encode() in before_tail,line
 return record

def check_current(standard,cached17,central_path):
 scope=checked_scope18()
 check_adoption(scope)
 cached=index(read(BASE/'current_cached_reports.json'))
 same_items(cached17,cached)
 central=index(read(central_path))
 assert len(central)>=len(standard)==7684
 same_items(standard,central)
 assert {n for n,x in cached.items() if x['isTheorem']}==set(central)
 same_items(central,cached)
 actual_scoped=standard_scope((ROOT/f"audit/{scope['log_prefix']}_axioms_contracts.log").read_text(),scope['declarations'])
 for name in scope['declarations']:
  assert name in cached and set(cached[name]['axioms'])==actual_scoped[name],name
 config=runpy.run_path(str(ROOT/'scripts/check.py'))
 assert len(config['ALL_TARGETS'])==251
 for name,signature in config['ALL_TARGETS'].values():assert central[name]['signature']==signature,name
 stats=read(BASE/'current_cached_stats.json')
 assert stats['missing']==[] and stats['actualTheorems']==len(central)
 assert stats['roots']==len(cached) and set(stats['axiomSeeds'])==ALLOWED
 assert all(set(x['axioms'])<=ALLOWED for x in cached.values())
 return len(central)

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--baseline-only',action='store_true',help='check frozen closed17 evidence without current18 adoption')
 parser.add_argument('--central',type=Path,default=ROOT/'audit/declarations.json')
 args=parser.parse_args()
 standard,cached=check_static()
 text='PASS:all7684 frozen ordinary-collector17 actual theorem types/axiom sets exactly match cached17;all7486 prior types/sets and152 scoped sets match;seven cycle cases;public frozen evidence hashes.\n'
 if not args.baseline_only:
  count=check_current(standard,cached,args.central)
  text+=f'PASS:all{count} current central theorem types/sets match fresh cached extraction;all7684 old theorem types/sets unchanged;all18 ordinary-scoped declaration sets match;three new proof hashes;all251 target signatures;exact reviewed prefix and byte-preserved current Audit tail.\n'
 text+='Historical source paths are provenance labels only;no scratch input was read.\n'
 (BASE/('baseline_validation.log' if args.baseline_only else 'current_validation.log')).write_text(text)
 print(text,end='')
if __name__=='__main__':main()
