"""Apply the reviewed M44 prose-item decisions after the one-time resync.

Default: validate and report without writing.  --write also writes the registers
and synchronizes the coverage modules' Item/file references.  No Lean statement
or proof is changed by this script.
"""
from pathlib import Path
import argparse
import collections
import copy
import json
import re
import sys

ROOT = next(p for p in Path(__file__).resolve().parents
            if (p / 'editorial/lean_coverage/resync_register.py').is_file())
SCRATCH = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'editorial/lean_coverage'))
import extract_items as ex
import resync_register as rr
import check_coverage as cc

STAMP = 'Corrected on 18 October 2026 (M44): '
actions = {}


def add(item, action='keep', source='coordinator', **fields):
    entry = actions.setdefault(item, {'item': item, 'action': 'keep', 'sources': [], 'notes': []})
    if source not in entry['sources']:
        entry['sources'].append(source)
    if action != 'keep':
        entry['action'] = action
    note = fields.pop('note_append', None)
    if note and note not in entry['notes']:
        entry['notes'].append(note)
    entry.update(fields)


for group in 'ABCDEF':
    for proposal in json.loads((SCRATCH / f'companion/proposals_{group}.json').read_text())['proposals']:
        for record in proposal.get('register', []):
            fields = {'expected_status': record['status']}
            if record.get('anchor'):
                fields['anchor'] = record['anchor']
            if record['action'] == 'reanchor':
                fields['note_append'] = record['note']
            add(record['item'], record['action'], proposal['id'], **fields)


def retire(prefix, numbers):
    for number in numbers.split():
        add(f'{prefix}/prose/{number}', 'retire')


def anchor(item, text, **fields):
    fields.setdefault('note_append', 'Wording revised; mathematical content and quantifiers are unchanged.')
    add(item, 'reanchor', anchor=text, **fields)


# Article: the statements and proved negative facts are retained.  Items whose
# complete sentences were removed are retired; their Lean declarations remain.
for prefix, numbers in {
    'A/energy': '009 023 035',
    'A/failure': '009 035 064 069',
    'A/geometry': '007 011 024 026 032 039 059',
    'A/global': '005 023 028 036',
    'A/hypothesis_examples': '005 006 007',
    'A/introduction': '013 017 020 030 047',
    'A/local': '011 015 036 043',
    'A/planar_geometry': '003',
    'A/seed_certificate': '015 022',
    'A/verification': '022 024 029',
}.items():
    retire(prefix, numbers)

anchor('A/energy/prose/007', 'These are the usual full-BFGS conventions')
anchor('A/energy/prose/027', 'packages one or several comparison directions.',
       reason='Explanation of the comparison frame as a proof device that packages comparison directions.')
anchor('A/energy/prose/036', 'The planar application below shows that moving geometry can prove')
anchor('A/failure/prose/001', 'We construct a counterexample to each assertion')
anchor('A/failure/prose/010', r'Theorem~\ref{art:local-failure-lower} below gives a version with uniform positive lower curvature.',
       status='SAME_AS', of=['A/negative_lower/theorem/art:local-failure-lower'],
       remove=['lean'],
       note='Theorem art:local-failure-lower supplies the positive-lower-curvature version. ' + STAMP +
            'The former no-uniform-lower-curvature sentence is replaced by this forward reference; '
            'Failure.no_uniform_lower_curvature remains proved and covered by C/12_D/prose/047.')
anchor('A/failure/prose/013', 'The strict trial certificate below proves that the algorithm accepts them')
anchor('A/failure/prose/018', 'All displayed intervals are rational enclosures.')
anchor('A/failure/prose/036', 'To transfer a particular run with this calculation, the local model must cover the')
anchor('A/geometry/prose/008', 'without any description of the eventual eigenvalues or eigenvectors of the matrices')
anchor('A/geometry/prose/012', 'Solid arrows indicate gradients and the dashed arrow a common descent direction.')
anchor('A/geometry/prose/025', 'In every row the guarantee covers every infinite admissible run')
anchor('A/geometry/prose/033', 'Homogeneity cannot be dropped from the second row')
anchor('A/geometry/prose/049', 'For the centered route one must locate a minimizer and')
anchor('A/geometry/prose/058', 'shows why the theorems quantify over runs')
anchor('A/global/prose/019', 'Convergence extends beyond this condition:')
anchor('A/global/prose/024', 'The two summands need not separately be minimized at that center.')
anchor('A/global/prose/037', "The Euclidean norm case follows from Guo--Lewis's")
anchor('A/global/prose/038', 'the scalar absolute-value model was analyzed by Lewis--Overton')
anchor('A/introduction/prose/045', 'The field, like every comparison object in the paper, is used only in the proofs.',
       reason='Remark on the role of the comparison field and of every other comparison object '
              '(certificates, energies, segments): they occur in hypotheses and proofs only; '
              'AdmissibleBFGSRun involves none of them. No mathematical content.',
       note_append='The proof-only role of comparison objects is stated once, as scope point (c).')
anchor('A/introduction/prose/048', 'The article contains complete proofs of these results.')
anchor('A/local/prose/010', 'Maxima of quadratic formulas, whose switching sets are generally curved, are treated in the plane below.',
       note=STAMP + 'Before "A finite maximum of arbitrary quadratic formulas need not admit such a '
            'polyhedral partition and is not automatically covered." "Generally curved": '
            'quadratic_max_no_polyhedral_cells (the maximum of the three quadratics of Theorem '
            'art:nonradial-example has no polyhedral-cell representation as in Theorem art:polyhedral '
            'near its minimizer); "treated in the plane below": Corollary art:planar-max and Theorem art:nonradial-example.')
anchor('A/local/prose/042', 'The proof treats the curved interfaces directly',
       reason='Description of the proof: nonradial_example is stated for AdmissibleBFGSRun 2 F '
              'of the original objective with the unmodified update; its proof works with the curved switching curves themselves.')
anchor('A/local/prose/044', r'This example lies beyond Theorem~\ref{art:polyhedral}: its objective has no polyhedral-cell representation near the minimizer.',
       note=STAMP + 'The claim is stated positively: quadratic_max_no_polyhedral_cells proves that '
            'the objective admits no polyhedral-cell representation as in Theorem art:polyhedral '
            'on any neighborhood of its minimizer, so that theorem does not apply.')
anchor('A/lower_curvature/prose/037', 'This gives exact perturbed orbits.')
anchor('A/master/prose/010', 'adjacent-degree hierarchy for the principal minors of full-BFGS matrices')
anchor('A/seed_certificate/prose/016', 'All decimals defining a box are terminating rationals.')
anchor('A/verification/prose/021', 'The stable-manifold and strict-query arguments show that the specified algorithm realizes this decomposition.')
anchor('A/verification/prose/023', 'These comparisons identify the hypotheses that separate the proved')
anchor('A/verification/prose/026', r"Lewis--Overton's Challenge~7.1~\cite{LO} concerns absolutely continuously distributed initial data",
       reason='Literature remark ([LO, Challenge 7.1]: absolutely continuously distributed initial data) '
              'and a question (a set of failing starts of positive measure for a convex objective; open, '
              'cf. C/01_I/prose/138); not used in any proof.',
       note='Corrected on 15 October 2026 (M36) and 18 October 2026 (M44): the deterministic-start '
            'scope disclaimer was replaced by the setting of the challenge and the open question.')

# Companion: the common scope restrictions are stated once in Chapter 1.
for prefix, numbers in {
    'C/01_I': '158', 'C/02_M': '029', 'C/03_T': '037', 'C/04_R': '098',
    'C/05_G': '074', 'C/06_F': '056', 'C/07_H': '069', 'C/08_A': '046',
    'C/09_C': '102', 'C/10_Q': '052', 'C/11_U': '072', 'C/12_D': '064',
    'C/13_L': '003 080', 'C/14_E': '002',
    'C/correspondence': '010 026 030', 'C/research_story': '005 018 031',
    'C/seed_certificate': '015 022',
}.items():
    retire(prefix, numbers)

anchor('C/03_T/prose/001', 'The reciprocal budget becomes a convergence theorem when geometry controls a comparison energy.',
       reason='Motivation of the chapter, about the proof method: the reciprocal budget of Chapter M '
              'becomes a convergence theorem through control of a comparison energy (theorem/001).')
anchor('C/03_T/prose/002', 'Visibility, secant control and transport are conditions on the objective, with no assumption on the BFGS matrices.')
anchor('C/05_G/prose/001', 'The certificate is a sufficient condition for convergence.')
anchor('C/05_G/prose/002', 'scalar examples show that BFGS converges where the condition fails',
       note_replace=[['The sentence does not repeat the defective claim of prose/053 (it asserts only that the condition can fail while BFGS converges): ',
                      'The sentence asserts that the condition can fail while BFGS converges: ']])
anchor('C/08_A/prose/002', r'Chapters~\ref{comp:C} and~\ref{comp:U} turn this geometry into convergence theorems.',
       reason='Pointer to the dynamical theorems of Chapters C and U that use this geometry '
              '(C:thm:cluster and C:cor:AC in Chapter 9; the forced affine-critical cluster-point theorem of Chapter 11).')
anchor('C/14_E/prose/001', 'This chapter records the formal verification: the dated authoring audit comes first, followed by the preserved release record.',
       reason='Describes the structure of the chapter: the dated October 2026 Lean review of '
              'current_verification.tex comes first, then the preserved release record.')
anchor('C/04_R/prose/053', 'In every three phases the supporting errors repeat $0,0,25/4$.')
anchor('C/05_G/prose/046', 'This limiting argument uses the stated finite-extension and accessibility hypotheses.',
       note_append='The finite-extension and accessibility hypotheses remain in the limiting argument; '
                   'the redundant disclaimer was removed.')
anchor('C/05_G/prose/047', 'gives an obstruction that needs neither continuity nor boundedness of the certificate field')
anchor('C/14_E/prose/047', 'The principal Gram-sum identity and the full-BFGS principal-minor hierarchy are also proved in arbitrary finite dimension.')
anchor('C/04_R/prose/103', 'the scalar absolute-value model was analyzed by Lewis--Overton')
anchor('C/04_R/prose/104', 'The Euclidean-norm theorem is recovered here as a special case.')
add('C/13_L/prose/001', of=['C/12_D/prose/047'],
    note_append='The motivation still points to the absence of uniform lower curvature in the first '
                'construction, now at C/12_D/prose/047; A/failure/prose/010 is a forward reference to the second construction.')
add('C/06_F/prose/040', status='SAME_AS', of=['C/06_F/prose/042'], remove=['reason'],
    note_append='The matrix-limit example is stated directly; it is covered by prose/042.')

anchor('C/correspondence/prose/002', 'It exposes whole theorem contracts and all dependencies.')
anchor('C/correspondence/prose/007', 'The revised article independently proves global centered and coercive homogeneous convergence, local finite-partition and planar results, the matrix framework and both finite-branch local counterexamples.',
       note_replace=[['the actual-matrix framework', 'the matrix framework']])
anchor('C/correspondence/prose/008', 'The noncompact homogeneous alternatives, fixed-normal geometry, flat-contour parabolic family, lifting, rates and scalar baseline are proved in this companion',
       note_replace=[['"Separate companion results": the article does not state them (editorial).',
                      '"Proved in this companion": the article does not state them.']])
anchor('C/correspondence/prose/009', r'as is the infinite constant-Hessian family of Chapter~\ref{comp:L}.',
       note='The clause "as is the infinite constant-Hessian family of Chapter 13": Theorem L:thm:global '
            '(for every μ > 0, Q_μ with constant branch Hessians μI). The article keeps the same family '
            '(Q_μ for every μ > 0 with its bad orbits near the wrong corner) as the supporting Proposition '
            'art:quadratic_failure of its appendix (A/lower_curvature/proposition/art:quadratic_failure). ' +
            STAMP + 'Before "The infinite constant-Hessian family in Chapter 13 also remains here after '
            'its removal from the article\'s main theorem selection."')
anchor('C/correspondence/prose/016', 'Preserved runner, fresh compiler and transitive audit evidence.')
anchor('C/correspondence/prose/031', 'Correspondence review links the prose to the kernel-checked statements; author approval remains necessary before submission.')
anchor('C/current_verification/prose/008', 'This was an incremental build and a fresh audit.')
anchor('C/current_verification/prose/013', 'This restriction identifies the foundations the proofs use.')
anchor('C/current_verification/prose/015', 'Per-command output, input/output hashes, elapsed times, package states and the overall PASS are in')
anchor('C/current_verification/prose/020', 'The mixed-benchmark theorem quantifies over every admissible run for $u^2+|v|$ and proves both value and whole-iterate convergence.')
anchor('C/current_verification/prose/028', 'A further review freshly compiled the unchanged fourteen article-geometry declarations')
anchor('C/current_verification/prose/031', 'The runner and the compiler/audit evidence are under')
anchor('C/current_verification/prose/032', r"each whitened branch fails differentiability of its Fr\'echet derivative at zero.",
       note_replace=[['each actual whitened branch', 'each whitened branch']])
anchor('C/current_verification/prose/035', 'The following inherited verification material describes the earlier corrected release.')
anchor('C/research_story/prose/016', 'The Euclidean norm case recovers the theorem of Guo--Lewis.')
anchor('C/research_story/prose/017', r'Chapter~\ref{comp:H} uses a different potential to prove value alternatives for noncompact homogeneous objectives.',
       status='SAME_AS', of=['C/07_H/heading/001'], remove=['reason'],
       note='Theorem 7.A (C/07_H/heading/001): value alternatives along every admissible run for '
            'noncompact homogeneous objectives, proved with a different potential. ' + STAMP +
            'RS3 replaces the former value/iterate and finite-detection scope discussion. '
            'ResearchStory.value_convergence_unbounded_iterates (F = e^x) illustrated the removed clause '
            'and stays as an example.')
anchor('C/research_story/prose/032', 'The common analytical tool is an adjacent-degree hierarchy for the principal determinants')
anchor('C/research_story/prose/036', 'The radial and moving-field arguments show how this mechanism succeeds.',
       of=['C/03_T/prose/031', 'C/09_C/theorem/C:thm:cluster'],
       note='The radial argument (RS objectives covered, C/03_T/prose/031) and the moving field of the '
            'planar theorem (C/09_C/theorem/C:thm:cluster) succeed. ' + STAMP +
            'RS7 removes the repeated scalar-nonnecessity scope clause.')
add('C/07_H/prose/072', reason='Literature attribution to Xie–Wächter, Theorem IV.1, for finite '
    'detection of unbounded descent in the two-piece model; the many-piece infinite-run theorem is covered separately.')
add('C/07_H/prose/073', reason='Literature background: the invariant-subspace argument extends '
    'the affine-invariance result of Xie–Wächter, Theorem II.1.')


def spans(text, text_anchor):
    if not text_anchor.split():
        return []
    pattern = r'\s+'.join(map(re.escape, text_anchor.split()))
    return [(m.start(), m.end()) for m in re.finditer(pattern, text)]


END = re.compile(r'[.?!](?=[\s\\}$)]|$)')


def lines_for(text, text_anchor, near):
    found = spans(text, text_anchor)
    if not found:
        return None
    start, end = min(found, key=lambda se: abs(text.count('\n', 0, se[0]) + 1 - near))
    first = text.count('\n', 0, start) + 1
    stop = end - 1
    if not text_anchor.rstrip().endswith(('.', '?', '!')):
        match = END.search(text, end)
        if match:
            stop = match.start()
    last = text.count('\n', 0, stop) + 1
    if last - first > 6:
        last = text.count('\n', 0, end - 1) + 1
    return [first, last]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    registers = {p: json.loads(p.read_text()) for p in sorted(ex.REGISTER.glob('[AC]_*.json'))}
    before = copy.deepcopy(registers)
    index = {it['id']: (p, it) for p, data in registers.items() for it in data['items']}
    missing = sorted(set(actions) - set(index))
    if missing:
        raise RuntimeError(('actions for absent items', missing))
    retired = {}
    for item_id, action in actions.items():
        path, item = index[item_id]
        if action.get('expected_status') and action['expected_status'] != item['status']:
            raise RuntimeError((item_id, 'unexpected old status', item['status'], action['expected_status']))
        if action['action'] == 'retire':
            registers[path]['items'].remove(item)
            retired[item_id] = item
            continue
        for key in ('anchor', 'status', 'of', 'lean', 'reason', 'note'):
            if key in action:
                item[key] = action[key]
        for key in action.get('remove', []):
            item.pop(key, None)
        for old, new in action.get('note_replace', []):
            if old not in item.get('note', ''):
                print('NOTE REPLACEMENT NOT FOUND', item_id, repr(old))
            item['note'] = item.get('note', '').replace(old, new)
        for note in action['notes']:
            addition = STAMP + note
            if addition not in item.get('note', ''):
                item['note'] = (item.get('note', '') + ' ' + addition).strip()

    # Re-anchor every affected prose item, including anchors which survived but
    # were moved out of their mapped range by deletion of the literature preface.
    edited = set(re.findall(r'^== (\S+) \(base HEAD\):', (SCRATCH / 'resync_dry2.txt').read_text(), re.M))
    for file in edited:
        if (ROOT / file).read_bytes() != (SCRATCH / 'snap1' / file).read_bytes():
            raise SystemExit('TeX changed after the saved resync: review the actions before applying: ' + file)
    missing_anchors, moved_lines = [], []
    for path, data in registers.items():
        if data['file'] not in edited:
            continue
        text = (ROOT / data['file']).read_text()
        for item in data['items']:
            if item['kind'] != 'prose':
                continue
            a, b = item['lines']
            if spans('\n'.join(text.split('\n')[a - 1:b]), item['anchor']):
                continue
            moved = lines_for(text, item['anchor'], a)
            if moved is None:
                missing_anchors.append((item['id'], item['anchor']))
            elif moved != item['lines']:
                moved_lines.append((item['id'], item['lines'], moved))
                item['lines'] = moved

    # New prose assertions introduced by the positive formulations.
    additions = [
        ('A/verification/prose/031', 'paper/sections/verification.tex',
         'The failing starts constructed here form a sequence of points.',
         'SAME_AS', {'of': ['A/negative_upper/theorem/art:local-failure',
                            'A/negative_lower/theorem/art:local-failure-lower']},
         'Replaces the retired failure-section item A/failure/prose/009: both theorems give one '
         'failing start for each m, a sequence converging to the minimizer.'),
        (None, 'companion/chapters/01_I.tex',
         'The certificates, frames and comparison energies of the positive theory are used only in the proofs.',
         'NON_CLAIM', {'reason': 'Scope point (c): comparison objects are proof devices, '
                      'not inputs to the BFGS iteration. This describes the theorem contracts.'},
         'The proof-only role is stated once here instead of repeated disclaimers.'),
        (None, 'companion/chapters/09_C.tex',
         'The convergence proof treats the curved interfaces directly, in the original coordinates and with the unmodified BFGS update.',
         'NON_CLAIM', {'reason': 'Description of the proof of the nonradial example: '
                      'the original objective, coordinates and full-BFGS update are used.'},
         'Companion counterpart of A/local/prose/042.'),
        (None, 'companion/chapters/07_H.tex',
         'The infinite-run value conclusion proved here holds for the whole many-piece family.',
         'SAME_AS', {'of': ['C/07_H/prose/011']},
         'States the many-piece result directly after the attribution of the two-piece finite-detection theorem.'),
    ]
    new_ids = []
    for item_id, file, text_anchor, status, fields, note in additions:
        path = ex.register_path(file)
        data = registers[path]
        prefix = data['items'][0]['id'].split('/')[:2]
        if item_id is None:
            # Do not reuse retired ids.
            numbers = [int(it['id'].rsplit('/', 1)[1]) for it in before[path]['items'] if it['kind'] == 'prose']
            item_id = '/'.join(prefix) + f'/prose/{max(numbers) + 1:03}'
        assert item_id not in index
        lines = lines_for((ROOT / file).read_text(), text_anchor, 1)
        if lines is None:
            missing_anchors.append((item_id, text_anchor))
            continue
        data['items'].append({'id': item_id, 'kind': 'prose', 'anchor': text_anchor,
                              'lines': lines, 'status': status, **fields,
                              'note': 'Added on 18 October 2026 (M44): ' + note})
        new_ids.append(item_id)

    main_item = next(it for it in registers[ex.register_path('companion/chapters/12_D.tex')]['items']
                     if it['id'] == 'C/12_D/theorem/D:main')
    if 'BfgsCoverage.Companion.Ch12D.starts_null' not in main_item['lean']:
        main_item['lean'].append('BfgsCoverage.Companion.Ch12D.starts_null')
    pointer = next(it for it in registers[ex.register_path('companion/chapters/04_R.tex')]['items']
                   if it['id'] == 'C/04_R/prose/062')
    pointer['note'] = pointer.get('note', '') + ' ' + STAMP + 'The added chapter pointer refers to the '
    pointer['note'] += 'planar quadratic maxima treated in Chapters C and Q.'

    listed = {it['id']: it for data in registers.values() for it in data['items']}
    broken_of = []
    for data in registers.values():
        for item in data['items']:
            targets = item.get('of', [])
            for target in ([targets] if isinstance(targets, str) else targets):
                if target not in listed:
                    broken_of.append((item['id'], target))

    lean_edits, bad_docstrings = {}, []
    for path, data in registers.items():
        if not data.get('lean_module'):
            continue
        module = cc.module_file(data['lean_module'])
        text = module.read_text()
        fixed = rr.item_ref_edits(text, data['file'], listed)
        for start, end, replacement in sorted(fixed, reverse=True):
            text = text[:start] + replacement + text[end:]
        if text != module.read_text():
            lean_edits[module] = text
        for match in cc.ITEM_REF.finditer(text):
            if match.group(1) not in listed:
                bad_docstrings.append((str(module.relative_to(ROOT)), match.group(1)))

    print('Actions:', len(actions), dict(collections.Counter(a['action'] for a in actions.values())))
    print('Retired:', len(retired), '; added:', new_ids, '; line ranges corrected:', len(moved_lines))
    print('Missing anchors:', len(missing_anchors), '; broken of targets:', len(broken_of),
          '; unknown docstring refs:', len(bad_docstrings))
    for label, records in [('ANCHOR', missing_anchors), ('OF', broken_of), ('DOC', bad_docstrings)]:
        for record in records:
            print(label, *record)
    report = {'actions': list(actions.values()), 'retired': retired, 'added': new_ids,
              'moved_lines': moved_lines, 'missing_anchors': missing_anchors,
              'broken_of': broken_of, 'unknown_docstring_refs': bad_docstrings}
    (SCRATCH / 'reg/action_report.json').write_text(json.dumps(report, indent=1, ensure_ascii=False) + '\n')
    if missing_anchors:
        raise SystemExit('Resolve every missing anchor before writing.')
    if broken_of:
        raise SystemExit('Resolve every missing of target before writing.')
    if args.write:
        for path, data in registers.items():
            if data != before[path]:
                path.write_text(json.dumps(data, indent=1, ensure_ascii=False) + '\n')
        for path, text in lean_edits.items():
            path.write_text(text)
        print('WROTE', sum(registers[p] != before[p] for p in registers), 'registers and', len(lean_edits), 'Lean docstring files')


if __name__ == '__main__':
    main()
