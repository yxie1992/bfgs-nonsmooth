#!/usr/bin/env python3
"""Bounded September 13 editorial refresh; retained proof evidence is immutable.

--write updates only the three component reviews and this revision's receipt.
--check reproduces them in memory and compares bytes; it does not compile Lean,
assemble the ledger, generate documents, or modify the historical integration.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import json
import re
import sys

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are required.')

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
PRIOR = HERE / 'prior_mapping'
BASE = '91d30dadcfd0980472c3896be0c9fd83fc7d4db1'
sys.path.insert(0, str(ROOT / 'editorial'))
from active_tex_sources import sources

def digest(data):
    return hashlib.sha256(data).hexdigest()

def load(path):
    return json.loads(path.read_text())

def encoded(data):
    return (json.dumps(data, indent=2, ensure_ascii=True) + '\n').encode()

def sha(path):
    return digest(path.read_bytes())

def line(text, offset):
    return text[:offset].count('\n') + 1

def unique(text, anchor):
    assert text.count(anchor) == 1, ('Anchor must occur exactly once', anchor, text.count(anchor))
    return text.index(anchor)

def current(path):
    return (ROOT / path).read_text()

def location(path, anchor):
    return {'path': path, 'line': line(current(path), unique(current(path), anchor))}

STATEMENT = re.compile(r'\\begin\{(theorem|lemma|proposition|corollary|definition)\}.*?\\end\{\1\}', re.S)
MATH = re.compile(r'\\begin\{(equation|align|gather)\}.*?\\end\{\1\}', re.S)
LABEL = re.compile(r'\\label\{([^}]+)\}')
PROOF = re.compile(r'\\begin\{proof\}.*?\\end\{proof\}', re.S)

# Inverse substitutions apply only in the listed scopes. They are notation
# checks, not a general equivalence prover and not a Lean kernel claim.
ALIASES = [
    {'scope': ['paper/sections/energy.tex', 'paper/sections/local.tex'],
     'role': 'PSD remainder after the negative rank-one Hessian update',
     'old': 'M_k', 'new': r'\widehat B_k',
     'contract': 'BfgsVerification.AdmissibleBFGSRun.hessian_update; same displayed PSD remainder'},
    {'scope': ['paper/sections/energy.tex'], 'role': 'positive weak-Wolfe margin 1-c_2',
     'old': 'c', 'new': r'\omega', 'contract': 'BfgsVerification.AdmissibleBFGSRun.curvature_lower_bound'},
    {'scope': ['paper/sections/failure.tex', 'paper/sections/geometry.tex',
               'paper/appendices/seed_certificate.tex', 'paper/appendices/lower_curvature.tex'],
     'role': 'two fixed algebraic coordinates of the third seed slope',
     'old': '(c,d)', 'new': r'(c_\circ,d_\circ)', 'contract': 'fixed AlgebraicSeedData root; no parameter change'},
    {'scope': ['paper/sections/failure.tex', 'paper/appendices/lower_curvature.tex',
               'paper/statements/negative_upper.tex', 'paper/statements/negative_lower.tex'],
     'role': 'shrinking-copy index and nonoptimal limiting center, not ambient dimension',
     'old': r'n; p_n', 'new': r'\ell; \bar x_\ell',
     'contract': 'unchanged DEmbedding/LEmbedding copy index and centers'},
    {'scope': ['paper/sections/failure.tex'], 'role': 'generic translated local-model center',
     'old': 'p', 'new': r'\bar x', 'contract': 'NarrativeNegativeScaling local identity; translation only'},
    {'scope': ['paper/sections/failure.tex'], 'role': 'second coordinate of a generic query vector',
     'old': 'z_2 with explicit coordinate clarification', 'new': '[z]_2',
     'contract': 'same second coordinate; seed point z_2 remains unchanged'},
    {'scope': ['paper/sections/failure.tex:line-search paragraph'],
     'role': 'lower and upper line-search brackets', 'old': r'\ell,h',
     'new': r'\alpha_{\rm lo},\alpha_{\rm hi}', 'contract': 'same deterministic bracketing implementation'},
    {'scope': ['paper/appendices/lower_curvature.tex:copying subsection'],
     'role': 'one entire perturbed seed orbit and its fixed initial metric',
     'old': r'\bar x_k,\bar H_k', 'new': r'x_k^{\rm seed},H_k^{\rm seed}',
     'contract': 'unchanged perturbed orbit; one fixed whitening A=(H_0 seed)^(1/2)'},
]

def normalize(text, path, algorithm=False):
    if algorithm:
        text = text.replace(r'\alpha_{\rm lo}', r'\ell').replace(r'\alpha_{\rm hi}', 'h')
    else:
        if path in ALIASES[0]['scope']:
            text = text.replace(r'\widehat B_k', 'M_k')
        if path in ALIASES[1]['scope']:
            text = text.replace(r'\omega', 'c')
        if path in ALIASES[2]['scope']:
            text = text.replace(r'c_\circ', 'c').replace(r'd_\circ', 'd')
        if path in ALIASES[3]['scope']:
            # Apply the center before the index. Generic centers are separate.
            text = text.replace(r'\bar x_\ell', 'p_n').replace(r'\ell', 'n')
        if path == 'paper/sections/failure.tex':
            text = text.replace(r'F(\bar x+\lambda z)', r'F(p+\lambda z)')
            text = text.replace('[z]_2', 'z_2')
            text = text.replace('Here $z_2$ in the middle inequality denotes the second coordinate.', '')
        if path == 'paper/appendices/lower_curvature.tex':
            text = re.sub(r'([xH])_([k0])\^\{\\rm seed\}', r'\\bar \1_\2', text)
            text = text.replace(r'x^{\rm seed}', r'\bar x')
            text = text.replace(r'(\bar H_0)^{1/2}', r'\bar H_0^{1/2}')
    text = re.sub(r'\\(?:qquad|quad)\b', '', text)
    return re.sub(r'\s+', '', text)

def blocks(text, regex):
    out = {}
    for match in regex.finditer(text):
        labels = LABEL.findall(match.group())
        assert labels, ('Unlabeled mathematical block', match.group()[:120])
        for label in labels if regex is MATH else labels[:1]:
            assert label not in out, label
            out[label] = (match.group(1), match.group(), match.start(), match.end())
    return out

def proof_after(text, start):
    match = PROOF.search(text, start)
    assert match, ('No proof after offset', start)
    intervening = STATEMENT.search(text, start)
    assert not intervening or match.start() < intervening.start(), 'A different statement intervenes before proof'
    return match

def main(write):
    manifest = load(PRIOR / 'MANIFEST.json')
    assert manifest['baseline_commit'] == BASE
    for path, expected in manifest['files'].items():
        assert sha(PRIOR / path) == expected, ('Changed historical snapshot', path)
    old = {name: load(PRIOR / f'editorial/{name}_contract_review.json') for name in ['positive', 'negative', 'root']}
    out = copy.deepcopy(old)
    pos, neg, root = (out[n] for n in ['positive', 'negative', 'root'])
    paths = [str(p.relative_to(ROOT)) for p in sources(ROOT)]
    named = {}; label_places = {}; preservation = []; equation_preservation = []
    prior_math_labels = set(); new_math_labels = set()
    for path in paths:
        text = current(path)
        for m in LABEL.finditer(text):
            assert m[1] not in label_places, ('Duplicate label', m[1])
            label_places[m[1]] = {'path': path, 'line': line(text, m.start())}
        prior_path = PRIOR / path
        assert prior_path.exists(), ('Unreviewed new active TeX input', path)
        previous = prior_path.read_text()
        before = blocks(previous, STATEMENT); after = blocks(text, STATEMENT)
        assert before.keys() == after.keys(), ('Statement label set changed', path)
        for label, (kind, body, start, end) in after.items():
            assert before[label][0] == kind
            assert normalize(before[label][1], path) == normalize(body, path), ('Non-alias statement change', path, label)
            named[label] = {'path': path, 'kind': kind, 'body': body, 'start': start, 'end': end}
            preservation.append({'label': label, 'path': path, 'kind': kind,
                'before_sha256': digest(before[label][1].encode()), 'after_sha256': digest(body.encode()),
                'equal_after_scoped_notation_normalization': True})
        old_eq = blocks(previous, MATH); new_eq = blocks(text, MATH)
        prior_math_labels.update(old_eq); new_math_labels.update(new_eq)
        for label in sorted(old_eq.keys() & new_eq.keys()):
            assert normalize(old_eq[label][1], path) == normalize(new_eq[label][1], path), ('Existing mathematical display changed', path, label)
            equation_preservation.append({'label': label, 'path': path,
                'before_sha256': digest(old_eq[label][1].encode()), 'after_sha256': digest(new_eq[label][1].encode()),
                'equal_after_scoped_notation_normalization': True})
    assert prior_math_labels <= new_math_labels, ('Removed labeled mathematics', prior_math_labels-new_math_labels)
    assert new_math_labels-prior_math_labels == {'art:mixed-inward-remainder', 'art:local-l1-decomposition', 'art:jump-secant'}
    failure = 'paper/sections/failure.tex'
    def algorithm(text):
        start = unique(text, 'At a differentiable point $x$, let')
        end = unique(text, 'No resetting or rescaling of the stored matrix is performed.')
        return text[start:end+len('No resetting or rescaling of the stored matrix is performed.')]
    before_alg = algorithm((PRIOR/failure).read_text()); after_alg = algorithm(current(failure))
    assert normalize(before_alg, failure, True) == normalize(after_alg, failure, True), 'Algorithm changed beyond bracket notation'
    appendix_preservation = []
    for path in ['paper/appendices/lower_curvature.tex', 'paper/appendices/seed_certificate.tex']:
        before, after = (PRIOR/path).read_text(), current(path)
        assert normalize(before, path) == normalize(after, path), ('Appendix changed beyond reviewed notation', path)
        appendix_preservation.append({'path': path, 'before_sha256': digest(before.encode()), 'after_sha256': digest(after.encode()), 'full_text_equal_after_scoped_notation_normalization': True})

    for row in pos['statements']:
        block = named[row['label']]; path = block['path']; text = current(path)
        row['article_location'] = {'path': path, 'line': line(text, block['start'])}
        row['article_statement'] = block['body']
        if row['kind'] == 'definition':
            row['proof_location'] = {'kind': 'definition_not_a_proved_claim', **row['article_location']}
        else:
            if row['label'] == 'art:polyhedral':
                path = 'paper/sections/local.tex'; text = current(path)
                start = unique(text, r'\input{statements/positive_partition}') + len(r'\input{statements/positive_partition}')
            else:
                start = block['end']
            proof = proof_after(text, start)
            row['proof_location'] = {'path': path, 'line': line(text, proof.start()), 'end_line': line(text, proof.end()),
                'scope': row['proof_location']['scope']}
    for row in pos['equation_mappings']:
        row['article_location'] = label_places[row['label']]
    for row in pos['unnumbered_mathematical_deductions']:
        row['anchor'] = row['anchor'].replace('For example, a locally $C^{1,1}$', 'A locally $C^{1,1}$')
        row['article_location'] = location(row['article_location']['path'], row['anchor'])

    # Import reviewed N3/N4 detail, authenticating literal contracts and full
    # conservative span unions against the unchanged canonical/audit indices.
    claims = {r['id']: r for r in load(ROOT/'bfgs_lean_stage1/master_report/CLAIMS.json')['claims']}
    index = load(ROOT/'bfgs_lean_stage1/master_report/DECLARATION_INDEX.json')
    for supplement in load(ROOT/'editorial/narrative_rebuild/FORMAL_SUPPLEMENTS.json')['supplements'] + [root['supplemental_branch_regularity_audit']]:
        for decl in load(ROOT/supplement['declarations']):
            index[decl['name']] = decl
    component_index_names = set(index)
    for decl in root['supplemental_declarations']:
        index[decl['name']] = decl
    def exports(spans):
        return sorted({n for s in spans for n in claims[s]['exports']})
    n34 = load(HERE/'N3_N4_review.json')
    for row in n34['equation_mappings']:
        addition = copy.deepcopy(row)
        assert addition['all_span_exports'] == exports(addition['source_span_ids'])
        for declaration in addition.get('exact_formal_declarations', []):
            assert declaration['signature'] == index[declaration['name']]['signature']
        addition['article_location'] = label_places[addition['label']]
        addition['governing_statement'] = addition['hypothesis_and_proof_correspondence']
        if addition['label'] == 'art:mixed-inward-remainder':
            # The unchanged assembler loads the original geometry supplement
            # in its later root-prose phase. This positive equation has its
            # own literal endpoint in the already loaded positive supplement.
            assert addition['primary_declarations'] == ['ArticlePositive.mixed_inward_error', 'ArticleGeometry.mixed_ridge_inward']
            addition['primary_declarations'] = ['ArticlePositive.mixed_inward_error']
            addition['additional_root_review_support'] = {
                'record_id': 'root.geometry.mixed_ridge',
                'declaration': 'ArticleGeometry.mixed_ridge_inward',
                'audit': root['supplemental_structural_audit'],
                'scope': 'Retained alternate exact support loaded in the root-record phase; the positive equation uses its literal ArticlePositive endpoint.'}
        pos['equation_mappings'].append(addition)
    for row in n34['unnumbered_mathematical_deductions']:
        addition = copy.deepcopy(row)
        addition['anchor'] = addition['article_location']['anchor']
        addition['article_location'] = location(addition['article_location']['path'], addition['anchor'])
        for declaration in addition['exact_formal_declarations']:
            assert declaration['signature'] == index[declaration['name']]['signature']
        assert all(n in index for n in addition['primary_declarations'])
        addition['status'] = 'REVIEWED_EXPLANATION_OR_ELEMENTARY_SPECIALIZATION_OF_EXISTING_CHECKED_CONTRACTS; no new Lean endpoint'
        pos['unnumbered_mathematical_deductions'].append(addition)
    existing_spans = {row['id']: row for row in pos['full_source_span_register']}
    added_spans = []
    for key, span in n34['source_span_register'].items():
        assert span['exports'] == claims[key]['exports']
        if key not in existing_spans:
            pos['full_source_span_register'].append(copy.deepcopy(span)); added_spans.append(key)
    pos['article_files'] = sorted(set(pos['article_files']) | {r['article_location']['path'] for r in pos['equation_mappings']+pos['unnumbered_mathematical_deductions']})
    pos['article_sha256'] = {p: sha(ROOT/p) for p in pos['article_files']}

    # Explicit boundaries for non-environment proof passages; every anchor is
    # unique and both endpoints are checked. Never infer an appendix proof
    # from the location of its statement in a canonical input file.
    ends = {
        'objective_regularity_and_local_model_before_the_main_induction': r'\begin{proof}[Theorem~\ref{art:local-failure}]',
        'scalar_regularity_and_plateau_proof': 'Define\n',
        'four_branch_strong_convexity_regularity_minimizer_and_Hessian_proof': r'\subsection{Copying one entire orbit and fixing the initial matrix}',
        'all_query_copy_induction_and_one_fixed_identity_normalization': None,
        'finite_rational_query_certificate_argument': None,
        'infinite_actual_trial_tree_induction_from_the_finite_certificate': r'\begin{corollary}[Coercive polyhedral global failure]',
        'explicit_least_norm_subgradient_and_minimizer_argument': r'\begin{proposition}[A perturbed bad orbit]',
        'conditional_model_chain_rule_and_full_update_comparison_algebra': 'This is a covariance calculation, not an existence theorem',
    }
    def refresh_proof(row):
        row = copy.deepcopy(row); path = row['article_file']; text = current(path)
        if row['role'] == 'explicit_proof_environment':
            if row['start_anchor'].startswith('first proof after '):
                block = named[row['governing_label']]
                assert block['path'] == path
                match = proof_after(text, block['end'])
            else:
                start = unique(text, row['start_anchor']); match = PROOF.match(text, start)
                assert match
            start, end = match.start(), match.end()
            row['start_anchor'] = match.group().splitlines()[0]
            # Generic proof anchors are interpreted through governing label.
            row['anchor_resolution'] = 'proof following governing statement' if row['start_anchor'] == r'\begin{proof}' else 'unique literal proof opening'
        else:
            start = unique(text, row['start_anchor']); end_anchor = ends[row['role']]
            end = unique(text, end_anchor) if end_anchor else len(text)
            row['end_anchor_exclusive'] = end_anchor or 'END_OF_FILE'
        assert start < end
        row['start_line'] = line(text, start)
        row['end_line'] = line(text, end) if row['role']=='explicit_proof_environment' else line(text, end)-1
        row['passage_sha256'] = digest(text[start:end].encode())
        return row
    for row in neg['article_labels']:
        loc = label_places[row['label']]
        row['article_file'], row['line'] = loc['path'], loc['line']
        row['proof_locations'] = [refresh_proof(p) for p in row['proof_locations']]
    illustration = copy.deepcopy(next(r for r in neg['article_labels'] if r['label']=='art:upper_orbit'))
    illustration.update(label='art:shrinking-scales', kind='illustration_not_mathematical_proof',
        review_status='Schematic width/copy illustration of the already proved upper embedding; not numerical proof or a plot of the infinite objective',
        precise_review='The O(a_ell) affine neighborhood contains an O(a_ell^2) complete query copy for one fixed upper objective. The lower construction uses the different factor a_ell; not inferred from this drawing.')
    loc = label_places[illustration['label']]
    illustration['article_file'], illustration['line'] = loc['path'], loc['line']
    neg['article_labels'].append(illustration)

    root_changes = {
        'root.introduction.mechanism': 'We prove an inequality linking',
        'root.energy.nonnecessity': "The companion's scalar convergence and certificate-nonexistence results",
    }
    for row in root['records']:
        row['anchor'] = root_changes.get(row['id'], row['anchor'])
        row['article_location'] = location(row['article_location']['path'], row['anchor'])
        if row['id']=='root.energy.nonnecessity':
            row['scope_review'] = 'Companion scalar convergence and certificate-nonexistence show this sufficient comparison certificate is not necessary. The article planar example supplies a separate convergence mechanism where a radial secant certificate fails. Removed reminders concerning metric limits, finite search termination and cell identification are not represented as still present in this shortened paragraph.'
    n2 = load(HERE/'N2_review.json')
    for name, contract in n2['exact_contracts'].items():
        assert contract['signature'] == index[name]['signature'], ('Changed N2 exact contract', name)
    n2_anchors = {
        'N2.homogeneity': 'The homogeneous seed satisfies',
        'N2.partition': 'In the local embeddings, wrong vertices recur',
        'N2.active_gradients': 'There is also a direct test of the planar hypotheses.',
        'N2.secants': 'The secant calculation explains how curvature',
    }
    n2_spans = {
        'N2.homogeneity': ['D.span.3','D.span.6','H.span.9'],
        'N2.partition': ['D.span.7','D.span.8','D.span.9','L.span.6','L.span.7','R.span.8'],
        'N2.active_gradients': ['D.span.7','L.span.6','L.span.7','C.span.11'],
        'N2.secants': ['L.span.3','L.span.4','L.span.5'],
    }
    n2_names = {
        'N2.homogeneity': ['DEmbedding.seed_descent_ray','AdmissibleBFGSRun.homogeneous_coercive_iterates_zero'],
        'N2.partition': ['DEmbedding.local_cone','DEmbedding.deterministic_embedding_failure','ConvexCellRadial.finite_polyhedral_basin'],
        'N2.active_gradients': ['DEmbedding.branch_zero','DEmbedding.branch_old_hasGradient','DEmbedding.phiFirst_zero','DEmbedding.branch_last_hasGradient','LEmbedding.branch_zero','LEmbedding.branchGradient_zero','LEmbedding.branch_hasGradient','LEmbedding.objective_directional_derivative_zero','LWhitening.smoothGradient','LWhitening.coordinateMatrix_invertible','AffineWhitening.gradient_inverse','PlanarMaxRegular.finite_max_local_basin'],
        'N2.secants': ['LQuadraticSeed.branchGradient','LQuadraticSeed.branch_hasGradient'],
    }
    for deduction in n2['deductions']:
        key = deduction['id']; spans = n2_spans[key]
        names = ['BfgsVerification.'+name for name in n2_names[key]]
        assert all(name in index for name in names)
        # Selected helper declarations may occur only in the already audited
        # transitive dependency closure, not in a CLAIMS top-level export list.
        # Record that distinction rather than inventing a new span export.
        dependency_helpers = []
        for name in names:
            if name not in exports(spans):
                matching = [sid for sid,claim in claims.items() if name in claim['exports']]
                if matching:
                    spans = sorted(set(spans) | {matching[0]})
                else:
                    assert name in neg['transitive_project_dependencies'] or name in pos['formal_project_dependency_closure'], ('Unaudited support helper', name)
                    dependency_helpers.append(name)
        root['records'].append({'id': 'exposition.'+key, 'kind': 'reviewed_elementary_deduction',
            'article_location': location('paper/sections/verification.tex', n2_anchors[key]),
            'anchor': n2_anchors[key], 'source_span_ids': spans,
            'all_source_span_exports': exports(spans), 'primary_declarations': names,
            'scope_review': deduction['argument'],
            'printed_support': deduction['printed_support'],
            'selected_helpers_from_retained_dependency_closure': dependency_helpers,
            'status': 'REVIEWED_ELEMENTARY_DEDUCTION_FROM_EXISTING_CHECKED_CONTRACTS; not a new literal Lean theorem'})
    root['records'].append({'id': 'art:jump-secant', 'kind': 'reviewed_elementary_identity',
        'article_location': label_places['art:jump-secant'], 'anchor': r'\label{art:jump-secant}',
        'source_span_ids': n2_spans['N2.secants'], 'all_source_span_exports': exports(n2_spans['N2.secants']),
        'primary_declarations': ['BfgsVerification.LQuadraticSeed.branch_hasGradient'],
        'scope_review': n2['deductions'][3]['argument'],
        'status': 'REVIEWED_ELEMENTARY_SUBTRACTION_OF_CHECKED_ENDPOINT_GRADIENTS; no new Lean declaration'})
    for name in ['negative','root']:
        out[name]['article_file_sha256'] = {p: sha(ROOT/p) for p in out[name]['article_file_sha256']}

    dispositions = [
        {'id':'old.coordinate-clarification', 'path':failure,
         'old_text':'Here $z_2$ in the middle inequality denotes the second coordinate.',
         'disposition':'Redundant sentence removed after [z]_2 makes the coordinate explicit; sole non-alias statement sentence removal.'},
        {'id':'old.negative-lineage-location', 'path':failure,
         'disposition':'Historical comparisons moved to introduction under N1; source references retained. No mathematical statement removed.'},
        {'id':'old.root.energy.nonnecessity-scope',
         'old_record':next(r for r in old['root']['records'] if r['id']=='root.energy.nonnecessity'),
         'disposition':'Shortened paragraph retains certificate nonnecessity and planar radial distinction. Removed reminders are preserved in this historical row, not claimed as current paragraph text.'},
        {'id':'old.mixed-benchmark-duplicate-display',
         'path':'paper/sections/global.tex',
         'disposition':'Duplicate unlabeled inward-error display replaced by reference to the unchanged geometry identity, now art:mixed-inward-remainder.'},
        {'id':'old.scope-repetitions',
         'paths':['paper/sections/local.tex','paper/sections/energy.tex','paper/sections/failure.tex','paper/sections/verification.tex'],
         'disposition':'N6 repetition cuts are prose changes; all old component rows and source TeX remain in prior_mapping. Every named mathematical contract and existing labeled display is separately compared above.'},
    ]
    revision = {'date':'2026-09-13','baseline_commit':BASE,
        'scope':'Scientific exposition and explicitly reviewed notation; retained compiler/axiom/cache evidence is not relabeled as a new formal run.',
        'receipt':'editorial/scientific_exposition_20260913/mapping_refresh.json',
        'review_records':['editorial/scientific_exposition_20260913/'+name+'.json' for name in ['N1_review','N2_review','N3_N4_review','N5_review']]}
    for name, data in out.items():
        data['scientific_exposition_revision'] = revision
    immutable = {
        'positive': ['source_sha256','supplemental_formal_evidence','formal_project_dependency_closure','formal_dependency_audit'],
        'negative': ['canonical_contracts','canonical_declaration_index','canonical_declaration_index_sha256','claims_sha256','source_spans','all_span_exports','transitive_project_dependencies','dependency_counts','axiom_policy_check','supplemental_formal_audit','supplemental_branch_regularity_audit','companion_only_disposition'],
        'root': ['canonical_statement_reviews','legacy_formal_dependency_closure','legacy_axioms','supplemental_audit','supplemental_declarations','supplemental_audit_artifacts','mathematical_corrections','remaining_math_obligations','narrative_supplement_register','supplemental_structural_audit','supplemental_branch_regularity_audit','supplemental_cache_binding','satisfaction_review'],
    }
    retained = []
    for name, keys in immutable.items():
        for key in keys:
            assert out[name][key] == old[name][key], ('Retained evidence changed', name, key)
            retained.append({'register':name,'field':key,'unchanged_sha256':digest(encoded(out[name][key]))})
    assert pos['full_source_span_register'][:len(old['positive']['full_source_span_register'])] == old['positive']['full_source_span_register']
    # Check all copied or newly introduced anchors and referenced source exports.
    for row in root['records']+pos['unnumbered_mathematical_deductions']:
        assert row['article_location'] == location(row['article_location']['path'],row['anchor'])
        assert all(n in index for n in row.get('primary_declarations',[]))
    # Mirror the assembler's phase boundary, without changing its index or
    # weakening membership: component principal exports must be available
    # before it loads the original geometry declarations for root prose.
    for row in pos['statements']+pos['equation_mappings']:
        assert set(exports(row['source_span_ids'])) | set(row.get('primary_declarations',[])) <= component_index_names, ('Component-phase declaration missing', row['label'])
    for row in neg['article_labels']:
        assert set(exports(row['corrected_spans'])) | set(row['canonical_exports']) <= component_index_names, ('Negative component-phase declaration missing', row['label'])
    outputs = {f'editorial/{name}_contract_review.json': encoded(data) for name,data in out.items()}
    receipt = {'status':'PASS','baseline_commit':BASE,'scope':revision['scope'],
        'script_sha256':sha(Path(__file__)), 'baseline_manifest_sha256':sha(PRIOR/'MANIFEST.json'),
        'active_article_inputs':{p:sha(ROOT/p) for p in paths},
        'review_inputs':{p:sha(ROOT/p) for p in revision['review_records']},
        'aliases':ALIASES,'statement_preservation':preservation,
        'existing_labeled_display_preservation':equation_preservation,
        'new_mathematical_display_labels':sorted(new_math_labels-prior_math_labels),
        'algorithm_preservation':{'before_sha256':digest(before_alg.encode()),'after_sha256':digest(after_alg.encode()),'equal_after_bracket_alias_and_whitespace_normalization':True},
        'complete_appendix_notation_preservation':appendix_preservation,
        'immutable_evidence_subtrees':retained,'positive_additive_source_spans':added_spans,
        'historical_dispositions':dispositions,
        'component_output_sha256':{path:digest(data) for path,data in outputs.items()},
        'new_elementary_claim_scope':'N2 deductions and N3/N4 explanation/specialization records identify checked ingredients; no new Lean compilation or literal endpoint is claimed.',
        'existing_checker_sha256':{p:sha(ROOT/p) for p in ['editorial/verify_release_inputs.py','editorial/assemble_claim_ledger.py']},
        'execution':'Only component correspondence refresh and read-only source/contract checks; no document or Lean build.'}
    outputs['editorial/scientific_exposition_20260913/mapping_refresh.json'] = encoded(receipt)
    for path,data in outputs.items():
        if write:
            (ROOT/path).write_bytes(data)
        else:
            assert (ROOT/path).read_bytes()==data, ('Correspondence refresh is stale',path)
    print('PASS:',len(preservation),'named contracts;',len(equation_preservation),'existing labeled displays; exact algorithm; immutable evidence;', 'written' if write else 'current bytes match')

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true');mode.add_argument('--check',action='store_true')
    args=parser.parse_args();main(args.write)
