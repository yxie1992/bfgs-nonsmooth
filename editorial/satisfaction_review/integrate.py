#!/usr/bin/env python3
"""Refresh correspondence after the skeptical review, preserving prior evidence."""
from pathlib import Path
import hashlib, json, re, subprocess

ROOT = Path(__file__).resolve().parents[2]
BASE = 'dbe14e9aacacd72d84a4bd9a457bb503e1aee4bc'

def read(path):
    return json.loads((ROOT / path).read_text())

def sha(path):
    return hashlib.sha256((ROOT / path).read_bytes()).hexdigest()

def save(path, data):
    (ROOT / path).write_text(json.dumps(data, indent=2) + '\n')

# Review changes may clarify proofs and summaries; no theorem contract changed.
pattern = re.compile(r'\\begin\{(theorem|lemma|proposition|corollary|definition)\}.*?\\end\{\1\}', re.S)
contracts = []
for path in sorted((ROOT / 'paper').rglob('*.tex')):
    if 'build' in path.parts:
        continue
    rel = str(path.relative_to(ROOT))
    old = subprocess.check_output(['git', 'show', BASE + ':' + rel], cwd=ROOT, text=True)
    previous = [m.group(0) for m in pattern.finditer(old)]
    current = [m.group(0) for m in pattern.finditer(path.read_text())]
    assert previous == current, 'Changed theorem contract: ' + rel
    contracts.append({'path': rel, 'statement_blocks': len(current), 'unchanged': True,
                      'source_sha256': sha(rel)})

for script in ['positive_mapping.py', 'negative_record.py', 'integrate_reviews.py']:
    subprocess.run(['python3', 'editorial/narrative_rebuild/' + script], cwd=ROOT, check=True)

root = read('editorial/root_contract_review.json')
run = 'editorial/satisfaction_review/formal/runs/geometry_structural_01/'
summary = read(run + 'SUMMARY.json')
new = read(run + 'declarations.json')
old = root['supplemental_declarations']
keys = ['name', 'kind', 'signature', 'axioms', 'unsafe', 'partial']
assert [{k: d[k] for k in keys} for d in new] == [{k: d[k] for k in keys} for d in old]
assert summary['status'] == 'PASS'
root['supplemental_structural_audit'] = {
    'name': 'geometry_formal', 'summary': run + 'SUMMARY.json',
    'summary_sha256': sha(run + 'SUMMARY.json'),
    'declarations': run + 'declarations.json',
    'declarations_sha256': sha(run + 'declarations.json'),
}
branch_run = 'editorial/satisfaction_review/branch_formal/runs/branch_regularity_01/'
branch_summary = read(branch_run + 'SUMMARY.json')
branch_declarations = read(branch_run + 'declarations.json')
assert branch_summary['status'] == 'PASS'
assert branch_summary['module_owned_declarations'] == 3
assert branch_summary['kernel_root_type_and_value_agreement']
assert all(d['ordinary_collector_agrees'] and not d['unsafe'] and not d['partial']
           and set(d['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
           for d in branch_declarations)
root['supplemental_branch_regularity_audit'] = {
    'name': 'branch_regularity_formal', 'summary': branch_run + 'SUMMARY.json',
    'summary_sha256': sha(branch_run + 'SUMMARY.json'),
    'declarations': branch_run + 'declarations.json',
    'declarations_sha256': sha(branch_run + 'declarations.json'),
    'scope': 'Actual unwhitened and whitened branches fail second Frechet differentiability; combined literal lower local failure contract.'
}
negative = read('editorial/negative_contract_review.json')
names = [d['name'] for d in branch_declarations]
for row in negative['article_labels']:
    if row['label'] in {'art:local-failure-lower', 'art:lower_objective', 'art:lower_curvature', 'art:regularity-map'}:
        row['canonical_exports'] = sorted(set(row['canonical_exports']) | set(names))
        row['branch_regularity_correspondence'] = (
            'The literal combined endpoint includes the unchanged SmoothLocalFailureTarget and '
            'non-differentiability of fderiv for each of the first three actual whitened branches. '
            'The supporting theorem proves the same obstruction for the actual unwhitened branches '
            'by extracting the scalar derivative along a line and applying the existing scalar obstruction. '
            'The classical Hessian convention is unchanged; this is not merely failure of a second-order expansion.')
negative['supplemental_branch_regularity_audit'] = root['supplemental_branch_regularity_audit']
for d in branch_declarations:
    negative['canonical_contracts'][d['name']] = {
        **{k: d[k] for k in ['signature', 'source_range', 'axioms', 'unsafe', 'partial']},
        'source_path': 'editorial/satisfaction_review/branch_formal/ArticleBranchRegularity.lean',
    }
save('editorial/negative_contract_review.json', negative)
root['status'] = 'SKEPTICAL_REVIEW_COMPLETE; unchanged theorem contracts and fresh full structural geometry audit'
root['satisfaction_review'] = {
    'baseline_commit': BASE,
    'review_records': ['editorial/satisfaction_review/' + name + '_critique.json'
                       for name in ['core', 'positive', 'negative', 'narrative']],
    'scope': 'New proof and scope reread; summary hypotheses clarified, repeated prose cut, proof exposition and citation locators clarified. Theorem statements unchanged.',
}
save('editorial/root_contract_review.json', root)
save('editorial/satisfaction_review/statement_preservation.json', {
    'status': 'PASS', 'baseline_commit': BASE, 'files': contracts,
    'statement_blocks': sum(row['statement_blocks'] for row in contracts),
    'scope': 'Every theorem/lemma/proposition/corollary/definition environment in active and canonical paper TeX is byte-identical to the reviewed baseline; proof prose and informal summaries reviewed separately.',
})
print('Skeptical-review integration PASS; original geometry root types and all paper statement blocks unchanged.')
