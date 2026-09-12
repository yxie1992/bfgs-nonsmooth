#!/usr/bin/env python3
"""Rebuild the literature registers from reviewed packets and frozen report spans."""
import collections
import hashlib
import json
import pathlib
import re
import unicodedata

BASE = pathlib.Path(__file__).resolve().parents[1]
REPO = BASE.parents[1]
EDITION = BASE.parent / 'master_report'

def read(p):
    return json.loads(p.read_text())

def write(name, data):
    (BASE / name).write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')

packets = []
claims, sources, searches = [], [], []
for p in sorted((BASE / 'packets').glob('*.json')):
    d = read(p)
    packet = p.stem
    packets.append({'packet': packet, 'path': str(p.relative_to(BASE)),
                    'sha256': hashlib.sha256(p.read_bytes()).hexdigest()})
    for c in d['claims']:
        c = dict(c)
        c['packet'] = packet
        claims.append(c)
    for s in d['sources']:
        s = dict(s)
        s['packet'] = packet
        sources.append(s)
    for s in d['searches']:
        searches.append(dict(s, packet=packet))

claim_by_id = {c['id']: c for c in claims}
source_by_id = {s['id']: s for s in sources}
assert len(claim_by_id) == len(claims), 'Duplicate claim IDs'
assert len(source_by_id) == len(sources), 'Duplicate source IDs'
for c in claims:
    assert set(c['closest_sources']) <= set(source_by_id), c['id']

# Cross-references consolidate repeated inventory/evidence statements. They are
# explicit editorial routing, not automated assertions of mathematical equivalence.
routing = {}
def route(module, spans, ids):
    for n in spans:
        routing[f'{module}.span.{n}'] = ids.split()
route('I',[5],'N1')
route('I',[6],'N2_C11 N2_COUNTABLE')
route('I',[7],'N3_POLYHEDRAL N3_QUADRATIC')
route('I',[13],'POS-R-RS-IR POS-R-PLQ POS-R-GAUGES POS-R-RESIDUALS POS-F-CENTERED POS-F-TRANSFORM POS-F-BASIN POS-F-LIFT')
route('I',[14,15],'geom_C_cluster geom_C_local_convergence')
route('I',[16],'geom_Q_family geom_Q_RS_separation')
route('I',[17],'geom_U_single_interface geom_U_composite geom_U_parallel_interfaces geom_U_spikes')
route('I',[18],'POS-G-SCALAR-CONV POS-G-ACCUMULATING')
route('I',[19],'POS-H-VALUE POS-H-AFFINE POS-H-PLANAR POS-H-FLAT')
route('I',[20],'FND_SUPERQUAD POS-F-RATES')
route('I',[21],'geom_A_equal_rate geom_A_rank_loss geom_A_local_correctness geom_A_finite_values FND_NORMALIZE FND_POINTWISE FND_OBSTRUCTION POS-G-ACCUMULATING')
route('I',[22],'N1 N2_C11 geom_C_transport_warning POS-R-SPECTRAL-OBSTRUCTION POS-F-LINE-OBSTRUCTION POS-H-PLANAR geom_A_conjecture')
route('I',[23],'POS-R-GAUGES POS-R-PLQ POS-F-BASIN POS-F-RATES geom_C_cluster geom_C_local_convergence geom_Q_family geom_U_single_interface FND_CERTIFICATE FND_RECIPROCAL FND_SUPERQUAD FND_RESIDUAL')
route('T',[7],'FND_CERTIFICATE POS-R-RS-IR geom_Q_certificate geom_Q_RS_separation')
route('H',[2,6],'POS-H-VALUE POS-H-PLANAR POS-H-FLAT')
route('H',[7],'FND_BASIC')
route('D',[2],'N1 TECH_LINE_SEARCH')
route('D',[3],'N3_POLYHEDRAL TECH_SEED TECH_ROOT')
route('D',[4],'N3_POLYHEDRAL TECH_SEED FND_BASIC')
route('D',[5],'N3_POLYHEDRAL TECH_LINE_SEARCH')
route('D',[6],'N3_POLYHEDRAL')
route('D',[7,8],'N1 TECH_SEED')
route('D',[9],'N1 TECH_LINE_SEARCH')
route('L',[2],'N2_C11 N2_COUNTABLE N3_QUADRATIC')
route('L',[3],'TECH_SEED TECH_ROOT')
route('L',[4,5],'N3_QUADRATIC TECH_STABLE TECH_SEED TECH_ROOT')
route('L',[6],'N2_C11')
route('L',[7],'N2_C11 TECH_AFFINE')
route('L',[8],'N2_COUNTABLE')
route('E',[5],'N1 TECH_ROOT TECH_SEED')
route('E',[6],'N1 FND_BASIC TECH_SEED')
route('E',[7],'N1 TECH_LINE_SEARCH')
route('E',[8],'N3_QUADRATIC TECH_STABLE TECH_ROOT')
route('E',[9],'N2_C11 N2_COUNTABLE')
route('E',[10],'FND_MINORS')
route('E',[11],'POS-F-LIFT POS-H-PLANAR POS-H-FLAT')
route('E',[12],'FND_MINORS FND_RECIPROCAL FND_SUPERQUAD POS-F-CENTERED POS-F-RATES')
route('E',[13],'POS-R-PLQ POS-F-CENTERED POS-F-LIFT POS-F-BASIN')
route('E',[14],'POS-R-GAUGES POS-R-RS-IR POS-F-TRANSFORM')
route('E',[15],'POS-R-SP POS-R-RS-IR POS-R-PARABOLA POS-R-SPECTRAL-OBSTRUCTION')
route('E',[16],'FND_POINTWISE FND_OBSTRUCTION POS-G-ACCUMULATING')
route('E',[17],'FND_FRAME geom_C_local_convergence')
route('E',[18],'FND_CERTIFICATE FND_NORMALIZE')
route('E',[19],'geom_C_cluster geom_C_field geom_C_quadratic_basin geom_C_RS_separation geom_C_transport_warning')
route('E',[20],'FND_RESIDUAL geom_U_single_interface geom_U_composite geom_U_parallel_interfaces')
route('E',[21],'geom_C_quadratic_basin geom_C_local_convergence')
route('E',[22],'geom_U_spikes geom_U_nonsplitting')
route('E',[23],'POS-G-ACCUMULATING POS-G-FINITE')

span_claims = collections.defaultdict(set)
for c in claims:
    for loc in c['report_locations']:
        spans = [loc['span']] if isinstance(loc,dict) else re.findall(r'[A-Z]\.span\.\d+', loc)
        for s in spans:
            span_claims[s].add(c['id'])
for s, ids in routing.items():
    assert set(ids) <= set(claim_by_id), s
    span_claims[s].update(ids)

original = read(EDITION / 'CLAIMS.json')['claims']
original_ids = {s['id'] for s in original}
assert set(span_claims) <= original_ids
coverage = []
for s in original:
    ids = sorted(span_claims[s['id']])
    kind = 'research_comparison' if ids else 'scope_or_execution_record'
    if not ids:
        assert s['classification'] in ('notation_or_scope','execution_evidence_or_scope'), s['id']
    coverage.append(dict(span_id=s['id'], module=s['module'],
                         corrected_source='bfgs_lean_stage1/master_report/'+s['corrected_source'],
                         corrected_line_ranges=s['corrected_line_ranges'],
                         edition_classification=s['classification'], coverage_kind=kind,
                         research_claim_ids=ids,
                         note=('Substantive content routed to result/technique groups; any explicit open question remains open.' if ids else 'Definition/heading/editorial or execution scope; not a separate publication-priority claim.')))

for c in claims:
    c['covered_span_ids'] = [s['span_id'] for s in coverage if c['id'] in s['research_claim_ids']]
    # Technique records can have descriptive locators in packets, but each is
    # additionally connected to a report span in the consolidated register.
    assert c['covered_span_ids'], c['id']

# Preserve independently inspected version records. DOI groups are finding aids;
# merging would lose theorem numbering and differing access records.
by_doi = collections.defaultdict(list)
for s in sources:
    if s.get('doi'):
        by_doi[s['doi'].lower()].append(s['id'])
write('CLAIMS.json', {'schema_version':1, 'scope':'Research-priority and technique comparisons, separate from Lean verification statuses.',
                     'publication_priority_certified':False,'causal_ai_provenance_established':False,
                     'packets':packets,'claims':claims,'span_coverage':coverage})
write('SOURCES.json', {'schema_version':1,'note':'Version/access-specific source records may represent the same work. A metadata-only source is not a full theorem reading.',
                      'sources':sources,'same_doi_groups':{k:v for k,v in by_doi.items() if len(v)>1}})
write('SEARCH_LOG.json', {'schema_version':1,'cutoff_local':'2026-09-11 America/Los_Angeles',
                         'note':'Executed query ledger and primary-source locators, not archived search-engine result pages; ranking and accessibility are not reproducible guarantees.',
                         'searches':searches})

# BibTeX deliberately retains packet IDs for exact register references. Duplicate
# DOI entries identify inspected versions; a publication bibliography may merge them.
def tex(s):
    return str(s).replace('\\',r'\textbackslash{}').replace('{',r'\{').replace('}',r'\}').replace('&',r'\&').replace('%',r'\%').replace('_',r'\_').replace('#',r'\#')
lines=['% Literature-audit bibliography; source IDs match SOURCES.json.',
       '% Version-specific duplicates are intentional. Access qualifications are in SOURCES.json.',
       '% A metadata-only pointer is not evidence that the original proof was read.','']
for s in sources:
    fields={'title':'{'+tex(s['title'])+'}', 'author':' and '.join(tex(a) for a in s['authors']),
            'year':s.get('year'), 'url':s['url'], 'doi':s.get('doi')}
    if s.get('journal_date'):
        fields['note']=tex(s['journal_date'])
    lines.append('@misc{'+s['id']+',')
    for k,v in fields.items():
        if v is not None:
            lines.append('  '+k+' = {'+str(v)+'},')
    lines.extend(['}',''])
(BASE/'references.bib').write_text('\n'.join(lines))

summary={'packets':len(packets),'research_claim_groups':len(claims),'source_records':len(sources),
         'queries_logged':len(searches),'edition_spans':len(coverage),
         'spans_with_research_comparisons':sum(bool(s['research_claim_ids']) for s in coverage),
         'scope_or_execution_spans':sum(not s['research_claim_ids'] for s in coverage),
         'classifications':dict(sorted(collections.Counter(c['classification'] for c in claims).items())),
         'unresolved_claim_ids':[c['id'] for c in claims if c['classification']=='unresolved']}
write('REGISTER_SUMMARY.json',summary)
print(json.dumps(summary,indent=2))
