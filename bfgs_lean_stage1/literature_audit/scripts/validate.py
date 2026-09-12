#!/usr/bin/env python3
"""Validate this literature supplement; no mathematical proof or priority oracle."""
import argparse
import hashlib
import json
import pathlib
import re
from urllib.parse import unquote, urlparse
from baseline_io import baseline_bytes, baseline_json, LOCATIONS

BASE = pathlib.Path(__file__).resolve().parents[1]
REPO = BASE.parents[1]
EXCLUDED = {'MANIFEST.json', 'review/validation.log'}

def read(p):
    return json.loads(p.read_text())

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def files():
    return {str(p.relative_to(BASE)):sha(p) for p in sorted(BASE.rglob('*'))
            if p.is_file() and '__pycache__' not in p.parts
            and str(p.relative_to(BASE)) not in EXCLUDED}

def main():
    if not __debug__:
        raise RuntimeError('Run without -O; validation assertions must be enabled.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-manifest',action='store_true')
    args=parser.parse_args()
    baseline=read(BASE/'BASELINE.json')
    for p,h in baseline['files'].items():
        assert hashlib.sha256(baseline_bytes(p)).hexdigest()==h, ('Frozen report input changed',p)
    d=read(BASE/'CLAIMS.json')
    sources=read(BASE/'SOURCES.json')['sources']
    claims={c['id']:c for c in d['claims']}
    source_ids={s['id'] for s in sources}
    assert len(claims)==len(d['claims']) and len(source_ids)==len(sources)
    allowed={'existing_result','known_special_case','standard_deduction',
             'possible_extension','no_exact_match_found','unresolved'}
    for c in claims.values():
        assert c['classification'] in allowed, c['id']
        assert set(c['closest_sources'])<=source_ids, c['id']
        assert c['covered_span_ids'] and c['statement'] and c['comparison']
        assert c['confidence'] and c['open_search_limits']
    for s in sources:
        assert urlparse(s['url']).scheme in ('http','https'),s['id']
        assert s['title'] and s['authors'] and s['access'] and s['locators'],s['id']
    original=baseline_json('bfgs_lean_stage1/master_report/CLAIMS.json')['claims']
    original_by_id={s['id']:s for s in original}
    coverage=d['span_coverage']
    assert [s['span_id'] for s in coverage]==[s['id'] for s in original]
    for s in coverage:
        original_s=original_by_id[s['span_id']]
        assert s['corrected_line_ranges']==original_s['corrected_line_ranges']
        assert s['edition_classification']==original_s['classification']
        assert set(s['research_claim_ids'])<=set(claims)
        path=REPO/s['corrected_source']
        n=len(baseline_bytes(s['corrected_source']).decode().splitlines())
        assert all(1<=a<=b<=n for a,b in s['corrected_line_ranges'])
        if not s['research_claim_ids']:
            assert s['edition_classification'] in ('notation_or_scope','execution_evidence_or_scope')
    for p in d['packets']:
        assert sha(BASE/p['path'])==p['sha256'],p['path']
    assert d['publication_priority_certified'] is False
    assert d['causal_ai_provenance_established'] is False
    status=read(BASE/'STATUS.json')
    assert status['completed'] is True and status['status']=='COMPLETE_BOUNDED_LITERATURE_AUDIT'
    assert status['publication_priority_certified'] is False
    assert status['causal_authorship_provenance_established'] is False
    summary=read(BASE/'REGISTER_SUMMARY.json')
    assert summary['research_claim_groups']==len(claims)
    assert summary['source_records']==len(sources)
    assert summary['edition_spans']==len(coverage)==172
    assert summary['queries_logged']==len(read(BASE/'SEARCH_LOG.json')['searches'])
    assert set(re.findall(r'@misc\{([^,]+),',(BASE/'references.bib').read_text()))==source_ids
    if args.write_manifest:
        (BASE/'MANIFEST.json').write_text(json.dumps({'schema_version':1,
            'scope':'Literature supplement only; its integrity check is distinct from mathematical verification.',
            'exclusions':sorted(EXCLUDED),'files':files()},indent=2,ensure_ascii=False)+'\n')
    for p in BASE.rglob('*.md'):
        for target in re.findall(r'\]\(([^)]+)\)',p.read_text()):
            target=target.strip('<>')
            if urlparse(target).scheme or target.startswith('#'):
                continue
            local=unquote(target.split('#',1)[0])
            assert (p.parent/local).exists(),('Broken local Markdown link',str(p),target)
    required_reviews=['negative_peer_review.md','geometry_peer_review.md','positive_peer_review.md',
                      'foundation_peer_review.md','synthesis_peer_review.md']
    for p in required_reviews:
        assert (BASE/'review'/p).is_file(),p
    gate=read(BASE/'review/edition_integrity.json')
    assert gate['status']=='PASS' and gate['source_spans']==172
    manifest=read(BASE/'MANIFEST.json')
    assert manifest['files']==files(),'Supplement manifest differs; review intentional edits before regenerating.'
    print(json.dumps({'status':'PASS','baseline_files_verified':len(baseline['files']),'baseline_read_locations':LOCATIONS,
        'packet_count':len(d['packets']),'research_claim_groups':len(claims),
        'source_records':len(sources),'queries_logged':summary['queries_logged'],
        'edition_spans':len(coverage),'spans_with_research_comparisons':summary['spans_with_research_comparisons'],
        'scope_or_execution_spans':summary['scope_or_execution_spans'],
        'independent_review_files':len(required_reviews),'manifest_files':len(manifest['files']),
        'checks':['frozen report hashes','valid source/claim links and classifications',
                  'all 172 exact span locations accounted for','reviewed packet hashes',
                  'bibliography key coverage','local Markdown links','edition integrity gate evidence',
                  'complete supplement manifest'],
        'limits':'No automatic judgment of mathematical truth, causal provenance, or publication priority.'},indent=2))

if __name__=='__main__':
    main()
