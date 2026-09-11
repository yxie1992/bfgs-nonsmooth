#!/usr/bin/env python3
"""Promote the literal M supplement only after the complete frozen gate."""
import hashlib,json,re
from pathlib import Path
ROOT=next(p for p in Path(__file__).resolve().parents if (p/'lakefile.toml').is_file())
s=json.loads((ROOT/'audit/STATUS.json').read_text())
assert s['status']=='MODULE_M_AND_REPORT_LITERAL_FOUNDATION_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports'] and not s['remaining_target_obligations']
hashes=json.loads((ROOT/'audit/report_literal_foundation_source_hashes.json').read_text())
assert len(hashes)==729
for f,h in hashes.items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,f
p=ROOT/'audit/REPORT_STATUS.json';r=json.loads(p.read_text())
assert not any(m['id']=='report_literal_foundation_18' for m in r['milestones'])
mods={m['module']:m for m in r['modules']}
review='audit/REPORT_LITERAL_FOUNDATION_STATEMENT_REVIEW.md'
mods['M'].update(status='all_retained_mathematical_claims_and_literal_intermediate_assertions_verified',
 remaining_claims=[],statement_review=review)
def exports(files):
 names=[]
 for f in files:
  ns=[d['theorem'] for d in s['verified_declarations'] if d['source'].endswith('/'+f+'.lean')]
  assert ns,f
  names+=ns
 return sorted(set(names))
for i,files,note in [
 (2,['PrincipalCombinatorialIdentity'],'The literal eigenbasis Gram-sum equality is now independently proved by insertion/erasure and actual Gram determinants. The SPD eigenbasis is constructed before all vectors/degrees. The original principal-minor hierarchy proof remains unchanged and has no hierarchy/convergence assumption.'),
 (3,['SharpPotentialDegree','SharpPotentialTargets'],'The optimized actual principal potential is represented by a constructed polynomial of degree at most n−1. Its sharp fixed-tail bound and actual horizon-m root limit are proved for actual FullBFGSRun and actual summable predicted-decrease tail. No uniform tail-matrix bound or assumed polynomial/root limit is added. All earlier finite-horizon and reciprocal-growth conclusions remain proved.')]:
 row=next(x for x in mods['M']['coverage_spans'] if x['id']==f'M.span.{i}')
 row.update(claim_review='reviewed_all_retained_literal_mathematical_claims_audited',review_note=note,
  verified_exports=sorted(set(row.get('verified_exports',[])+exports(files))))
e=len(s['verified_declarations']);a=s['audited_declaration_count']
m=json.loads((ROOT/'audit/module_m_literal_completion_declarations.json').read_text())
assert len(m['declarations'])==18 and len(m['targets'])==2
r['milestones'].append(dict(id='report_literal_foundation_18',status='verified',
 targets=[b for _,b in m['targets']],audit='audit/STATUS.json',statement_review=review,
 explicit_theorems=e,audited_theorems=a,exact_targets=251,
 conditional_infrastructure=['Source criteria retain their stated hypotheses; actual applications discharge reusable proof infrastructure as reviewed.',
 'R182–187 unidentified older numerical objective and E historical execution/archive identities remain unresolved.']))
r['entire_report_verified']=False
p.write_text(json.dumps(r,indent=2)+'\n')
marker='## Eighteenth milestone: literal M identities and complete shared-graph audit'
record=f'''\n\n{marker}

The pinned complete build and transitive audit passed {e:,} explicit theorems,
{a:,} total theorem declarations, 251 exact targets and 729 frozen Lean files.
Only propext, Classical.choice and Quot.sound occur. Actual complete evidence
is in report_literal_foundation_check.log, STATUS.json and their companions.

The exact actual-SPD eigenbasis Gram-sum equality closes foundation94–99.
The constructed optimized principal-potential polynomial, sharp degree n−1
bound and actual horizon root limit close foundation151–155. The earlier
principal-matrix and reciprocal-growth proofs remain unchanged.

The shared dependency-graph collector preserves Lean4.19's exact checked
constant cases and handles cycles by reverse reachability. Every milestone17
theorem's type/axiom set was compared with its complete ordinary audit; all
new scoped declarations also passed ordinary collector checks. All original
trailing axiom/target commands remain. This tooling change supplies no proof
premise and changes no mathematical theorem or pinned dependency.

R's unidentified older four-piece numerical objective and E's absent original
19-job archive remain source-resolution obligations. Neither current D nor
current Lean executions establishes those missing original inputs. The entire
original report remains unverified pending their explicit resolution. All
research originals, documented corrections and explicit questions are preserved.
'''
for name in ['ENTIRE_REPORT_PLAN.md','MATHEMATICAL_REVIEW.md','PROOF_OBLIGATIONS.md']:
 p=ROOT/name;old=p.read_text();assert marker not in old;p.write_text(old+record)
p=ROOT/'PROOF_OBLIGATIONS.md';old=p.read_text()
anchor="The source's combinatorial equality is not separately exported. The proof checks\nthe needed inequality directly by inserting a missing index into a coordinate\nsubset and bounding nonnegative omitted terms. This changes the proof route,\nnot the hierarchy's statement or constants."
assert anchor in old
old=old.replace(anchor,"The original hierarchy proof establishes the needed inequality directly by\ninserting a missing index and bounding nonnegative omitted terms. Its statement\nand constants remain unchanged. The source's literal combinatorial equality is\nnow separately proved by `principalGramSumIdentity`, including the constructed\nactual-SPD eigenbasis and actual augmented Gram determinants.")
p.write_text(old)
p=ROOT/'README.md';old=p.read_text()
old,n=re.subn(r'all [0-9,]+ explicit\ntheorems and [0-9,]+ theorem declarations including generated auxiliaries. All 249',
 f'all {e:,} explicit\ntheorems and {a:,} theorem declarations including generated auxiliaries. All 251',old,count=1)
assert n==1
old=old.replace('audit/report_semialgebraic_path_check.log','audit/report_literal_foundation_check.log',1)
anchor='Historical execution/source-attribution exceptions remain unverified.'
assert anchor in old
old=old.replace(anchor,"The eighteenth tranche closes M's literal Gram-sum identity and sharp potential\ndegree/root limit. The complete audit uses the independently checked shared\ndependency graph and preserves the ordinary target/axiom checks. See\n[audit/REPORT_LITERAL_FOUNDATION_STATEMENT_REVIEW.md](audit/REPORT_LITERAL_FOUNDATION_STATEMENT_REVIEW.md).\n"+anchor,1)
old=old.replace('The checker allows up to 7,200 seconds per build or audit command. The\ncomplete inventory takes substantially longer than the former ten-minute\ndefault; use `--timeout SECONDS` to change the limit.',
 'The checker allows up to 7,200 seconds per build or audit command; use\n`--timeout SECONDS` to change the limit. The shared dependency graph avoids\nrepeated full traversal of the same proof dependencies. Complete ordinary\naudit comparisons and source checks are preserved as implementation evidence.')
p.write_text(old)
p=ROOT/'audit/REPORT_VERIFICATION_OVERVIEW.md';old=p.read_text()
old=old.replace('seventeenth','eighteenth').replace('249 exact targets','251 exact targets').replace('726 frozen Lean files','729 frozen Lean files')
old=re.sub(r'\*\*[0-9,]+ explicit theorems, [0-9,]+ total theorem declarations,',f'**{e:,} explicit theorems, {a:,} total theorem declarations,',old,count=1)
old=old.replace("M's additional literal Gram-sum identity and sharp potential-degree\nexport are also in a separate active scope; its principal theorem chain is proved.","M's additional literal Gram-sum identity and sharp potential-degree/root-limit\nexports are now also proved; the original principal theorem chain is preserved.")
old=old.replace('Literal Gram-sum equality and sharp potential degree remain separately active.','Literal Gram-sum equality, sharp potential degree and actual root limit are also proved.')
old=old.replace("The remaining Lean work is M's literal Gram-sum identity and sharp potential\ndegree export. To finish",'To finish')
old=old.replace('report_semialgebraic_path_check.log','report_literal_foundation_check.log')
old=old.replace('[the statement review](REPORT_SEMIALGEBRAIC_PATH_STATEMENT_REVIEW.md)',
 '[the geometric statement review](REPORT_SEMIALGEBRAIC_PATH_STATEMENT_REVIEW.md) and [the literal M/audit review](REPORT_LITERAL_FOUNDATION_STATEMENT_REVIEW.md)')
p.write_text(old)
print(f'Updated18 register/docs:{e} explicit/{a} total/251 targets;Mliteralclaimsclosed;R/Esourceexceptionsremain;entire_report_verified=false.')
