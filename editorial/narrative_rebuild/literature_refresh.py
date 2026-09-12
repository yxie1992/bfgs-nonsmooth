#!/usr/bin/env python3
"""Refresh citation contexts from the actual input graph, retaining prior access."""
from pathlib import Path
import copy
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'editorial'))
from active_tex_sources import sources


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


path = ROOT / 'editorial/LITERATURE_LEDGER.json'
prior_path = ROOT / 'editorial/narrative_rebuild/prior_records/LITERATURE_LEDGER.json'
if not prior_path.is_file():
    raise RuntimeError('Preserved prior ledger is required before refresh')
prior = json.loads(prior_path.read_text())
data = json.loads(path.read_text())
fresh_path = ROOT / 'editorial/narrative_rebuild/literature_primary_review.json'
fresh = json.loads(fresh_path.read_text())
fresh_by = {x['key']: x for x in fresh['primary_sources'] + fresh['additional_planar_tool_checks']}
previous_comparisons = {}
for claim in prior['paper_literature_claims']:
    for comparison in claim['source_comparisons']:
        previous_comparisons.setdefault(comparison['key'], comparison)

for source in data['sources']:
    key = source['key']
    if key in fresh_by:
        old = next(s for s in prior['sources'] if s['key'] == key)
        source['earlier_article_authoring_access'] = copy.deepcopy(old['current_run'])
        f = fresh_by[key]
        source['current_run'] = {
            'date': '2026-09-12',
            'read_level': 'fresh relevant primary statement/proof or algorithm passages; see detailed record',
            'primary_url': f.get('url', f.get('proof_version_url')),
            'version': f['version'] if 'version' in f else 'Published metadata plus explicitly numbered 2022 preprint v1',
            'locators': f.get('claim_locators', f.get('locator', f.get('theorem_locator', f.get('fresh_read')))),
            'caveat': f.get('access_limit', f.get('limit')),
            'detailed_record': str(fresh_path.relative_to(ROOT)) + f' (key {key})',
            'fresh_scope': f['fresh_read'],
        }

aliases = {'Bog22': 'geom_Bogosel2023', 'WW22': 'WW', 'LL18': 'LL', 'JM25v2': 'FND_JM25'}
source_by = {s['key']: s for s in data['sources']}
files = sources(ROOT)
pattern = re.compile(r'\\(cite|preprintcite)(?:\[([^\]]*)\])?\{([^}]+)\}')
claims, sites = [], []
for file in files:
    text = file.read_text()
    for match in pattern.finditer(text):
        keys = [k.strip() for k in match[3].split(',')]
        line = text[:match.start()].count('\n') + 1
        start = text.rfind('\n\n', 0, match.start()) + 2
        if start == 1:
            start = 0
        end = text.find('\n\n', match.end())
        end = len(text) if end < 0 else end
        context = text[start:end].strip()
        comparisons = []
        for text_key in keys:
            key = aliases.get(text_key, text_key)
            if key not in source_by:
                raise RuntimeError('Missing canonical source: ' + key)
            if key in fresh_by:
                f = fresh_by[key]
                comparison = {
                    'key': key, 'text_key': text_key,
                    'source_conclusion_or_technique': f.get('comparison', f.get('fresh_read')),
                    'relevant_assumptions': f.get('common_assumptions', f.get('algorithm_assumptions', f.get('challenge_assumptions', f.get('B1', f.get('fresh_read'))))),
                    'difference_or_scope_limit': f.get('important_scope_difference', f.get('comparison', f.get('limit', f.get('access_limit')))),
                    'exact_version_and_locator_record': str(fresh_path.relative_to(ROOT)) + f' (key {key})',
                }
            else:
                comparison = copy.deepcopy(previous_comparisons.get(key, {}))
                if not comparison:
                    raise RuntimeError('New source needs scholarly review: ' + key)
                comparison['text_key'] = text_key
            comparison['access_record'] = f'sources[key={key}].current_run'
            comparisons.append(comparison)
        sites.append({'file': str(file.relative_to(ROOT)), 'line': line,
                      'command': match[1], 'locator': match[2], 'keys': keys})
        claims.append({'id': f'ART-NARR-LIT-{len(claims)+1:02d}',
                       'manuscript_file': str(file.relative_to(ROOT)),
                       'manuscript_line': line, 'exact_manuscript_context': context,
                       'citation': match[0], 'source_keys': keys,
                       'point_of_use_locator': match[2], 'source_comparisons': comparisons,
                       'review_date': '2026-09-12',
                       'review_scope': 'Scholarly attribution and precise source-version comparison; not priority or independent correctness certification'})

published = sorted({k for site in sites if site['command'] == 'cite' for k in site['keys']})
entries = sorted(re.findall(r'\\bibitem\{([^}]+)\}', (ROOT / 'paper/bibliography.tex').read_text()))
if published != entries:
    raise RuntimeError('Published article bibliography must equal active cited keys')
data.update({
    'review_date': '2026-09-12',
    'paper_literature_claims': claims,
    'citation_sites_at_snapshot': sites,
    'snapshot_note': f'Current narrative revision: exact paragraph contexts for all {len(sites)} active citation sites, from the recursive input graph. Historical article contexts remain in the preserved prior ledger.',
    'assembled_article_inputs': [str(p.relative_to(ROOT)) for p in files],
    'assembled_article_sha256': {str(p.relative_to(ROOT)): digest(p) for p in files},
    'published_keys_in_article': published,
    'bibliography_pruning': {
        'removed_in_this_revision': ['BDLS', 'LL', 'geom_Lewis2002', 'Rockafellar70'],
        'added_in_this_revision': ['geom_Bogosel2023'],
        'retained_count': len(entries),
        'basis': 'Actual recursive article graph; inactive proposals and companion-only works excluded',
    },
    'active_article_citation_review': {
        'status': 'PASS_SOURCE_SCOPE; final rendered review is separate',
        'reviewed_citation_sites': len(sites),
        'cited_published_references': len(published),
        'publication_versions': 'BG published Theorem3.1/B1; GL18 author version; XW2017v1; Bog22/WW22 explicit preprint numbered locators; LW pinned2019v1',
        'source_access_limits': fresh['classical_background']['qualification'],
        'limits': 'No novelty/priority certification, complete audit of external proofs, new independent Lean build, or human approval',
    },
    'assembled_article_reconciliation': {
        'date': '2026-09-12',
        'exact_contexts_present': all(c['exact_manuscript_context'] in (ROOT/c['manuscript_file']).read_text() for c in claims),
        'citation_site_count': len(sites),
        'scope': 'Current text contexts and source hashes; scientific/proof/visual release passes remain distinct',
    },
    'narrative_revision': {
        'prior_ledger': str(prior_path.relative_to(ROOT)),
        'prior_ledger_sha256': digest(prior_path),
        'primary_review': str(fresh_path.relative_to(ROOT)),
        'primary_review_sha256': digest(fresh_path),
        'prior_current_comparison': 'editorial/narrative_rebuild/literature_comparison.json',
        'scientific_significance_review': 'editorial/narrative_rebuild/scientific_significance_review.json',
        'positive_mathematical_review': 'editorial/narrative_rebuild/narrative_positive_review.json',
        'formal_claim_ledger': 'editorial/CLAIM_LEDGER.json',
        'no_third_party_papers_downloaded': True,
    },
})
data['publication_policy']['earlier_version_text_aliases'] = aliases
data['publication_policy']['fresh_MP_policy_access'] = {
    'date': '2026-09-12', 'url': 'https://link.springer.com/journal/10107/submission-guidelines',
    'record': 'editorial/JOURNAL_FIT.md',
}
data['companion_version_review']['historical_scope_note'] = 'Preserved exact-version bibliography and chapter review from prior authoring release; the new research-story prose is linked by narrative_revision rather than relabeled as the old all-site review.'
path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'citation_sites': len(sites), 'published_entries': len(entries),
                  'all_exact_contexts_present': data['assembled_article_reconciliation']['exact_contexts_present'],
                  'ledger_sha256': digest(path)}, indent=2))
