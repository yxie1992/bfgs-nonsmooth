#!/usr/bin/env python3
"""Build proposals_E.json (group E: 09_C.tex, 14_E.tex) and check every `old` is unique."""
import json
from pathlib import Path

REPO = Path('/home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth')
C = 'companion/chapters/09_C.tex'
E = 'companion/chapters/14_E.tex'


def R(item, status, action, note='', anchor=None):
    r = {'item': item, 'status': status, 'action': action}
    if anchor is not None:
        r['anchor'] = anchor
    if note:
        r['note'] = note
    return r


P = []


def add(pid, file, kind, old, new, reason, register=()):
    P.append({'id': pid, 'file': file, 'kind': kind, 'old': old, 'new': new,
              'reason': reason, 'register': list(register)})


# ---------------------------------------------------------------- 09_C.tex
add('E-09C-01', C, 'positive',
    r'The positivity $t_k>0$ in the update is derived, not an additional assumption on later matrices:',
    r'The positivity $t_k>0$ in the update is derived:',
    'States the derived fact positively; the derivation after the colon already shows that t_k>0 is no assumption.',
    [R('C/09_C/prose/013', 'LEAN', 'reanchor',
       'Claim unchanged (t_k>0 is derived: curvature_derived). The Lean docstring Ch09C.lean:369-371 '
       'already quotes exactly this shorter anchor.',
       anchor=r'The positivity $t_k>0$ in the update is derived')])

add('E-09C-02', C, 'repeat',
    r' Existence of differentiable acceptable lengths on every exceptional search ray is not part of the theorem.',
    '',
    'Scope point (a) (existence of infinite admissible runs is a hypothesis), stated once in Chapter 1; '
    'the chapter argument does not use it; the article deleted its parallel sentences.',
    [R('C/09_C/prose/015', 'NON_CLAIM', 'retire',
       'Scope remark, scope point (a) of Chapter 1. No references (grep of registers and BfgsArticle: none).'),
     R('C/09_C/prose/014', 'LEAN', 'keep', 'Preceding sentence; anchor and claim unchanged.')])

add('E-09C-03', C, 'caveat',
    r' It does not prove its general-dimensional or merely weighted-tangential-curvature version.',
    '',
    'The preceding sentence already names the proved version (planar, strict contours); the general '
    'conjecture and its status are recorded in Chapter 8 ("What remains a conjecture").',
    [R('C/09_C/prose/017', 'NON_CLAIM', 'retire',
       'The open conjecture stays recorded in 08_A.tex Section "What remains a conjecture" '
       '(C/08_A/prose/042, OPEN). No references.'),
     R('C/09_C/prose/016', 'SAME_AS', 'keep', 'Preceding sentence; unchanged.')])

add('E-09C-04', C, 'caveat',
    r'No convex-support-function property of $h$ is asserted or needed.',
    r'No convex-support-function property of $h$ is needed.',
    'Drops "asserted or"; keeps the generality remark, now word for word the article '
    '(planar_geometry.tex:78-79).',
    [R('C/09_C/prose/044', 'NON_CLAIM', 'reanchor',
       'Generality remark (no hypothesis on h beyond those stated).',
       anchor=r'No convex-support-function property of $h$ is needed.'),
     R('C/09_C/prose/116', 'LEAN', 'keep', 'Preceding clause; anchor and claim unchanged.')])

add('E-09C-05', C, 'guard',
    r'has an actual right derivative',
    r'has a right derivative',
    'Guard word "actual"; the article has "The convex function $\\varphi$ has a right derivative at '
    'every $\\theta<1$". Inside the proof of Lemma C:lem:transport (wording only).',
    [R('C/09_C/proof/003', 'PROOF', 'keep',
       'Mechanical proof item: its hash changes; the argument is unchanged (wording only); re-accept.')])

add('E-09C-06', C, 'positive',
    r'This is a crossing-specific linear curvature estimate, not a uniform positive Hessian assumption.',
    r'This is a crossing-specific linear curvature estimate.',
    '"X, not Y" -> X; the proof just derived t >= c_0|s| from the crossing, and the preceding paragraph '
    'already says no positive lower Hessian bound is required. Inside the proof of Lemma C:lem:secant.',
    [R('C/09_C/proof/004', 'PROOF', 'keep',
       'Mechanical proof item: its hash changes; the argument is unchanged (the estimate and its '
       'derivation stay); re-accept.')])

add('E-09C-07', C, 'caveat',
    r' It does not first select one cluster point and assume all later iterates stay near it.',
    '',
    'Third statement of the no-iterate-limit point (Theorem C:thm:cluster: "No iterate limit ... is '
    'assumed"; line 151: "This does not assume that Gamma is a singleton"); the emphasized "whole '
    'hypothetical cluster set" in the kept sentence carries it.',
    [R('C/09_C/prose/059', 'SAME_AS', 'keep',
       'Anchor and claim unchanged (one field near all of Gamma; no single cluster point selected, as in '
       'the theorem statement and C/09_C/prose/028).')])

add('E-09C-08', C, 'repeat',
    r' Nor is the field an extra algorithmic input: it is an analytical object derived from the objective, independent of every $H_k$.',
    '',
    'Scope point (c) (comparison fields are used only in the proofs), stated in Chapter 1; the '
    'independence the argument needs is stated where it is used (line 247: constants chosen before the '
    'pair, none depends on a BFGS matrix). The article deleted its parallel sentences.',
    [R('C/09_C/prose/060', 'SAME_AS', 'retire',
       'Same content as C/09_C/prose/057 and prose/058 (field built from F alone; no BFGS matrix among '
       'the hypotheses of three_estimates), which remain. No references.'),
     R('C/09_C/prose/059', 'SAME_AS', 'keep', 'First sentence of the paragraph; unchanged.')])

add('E-09C-09', C, 'guard',
    r'its actual objective composition',
    r'its objective composition',
    'Guard word "actual".',
    [R('C/09_C/prose/062', 'LEAN', 'keep', 'Anchor survives; claim unchanged.')])

add('E-09C-10', C, 'guard',
    r'The actual affine-critical set also has',
    r'The affine-critical set also has',
    'Guard word "actual".',
    [R('C/09_C/prose/066', 'LEAN', 'reanchor',
       'Claim unchanged. The Lean docstring Ch09C.lean:3836-3837 quotes the old anchor ("The actual '
       'affine-critical set ...").',
       anchor='The affine-critical set also has finitely many piecewise-smooth path classes')])

add('E-09C-11', C, 'caveat',
    r' This avoids presuming that an arbitrary smooth point path has a semialgebraic graph or that its composition with a nonsmooth $F$ is differentiable in advance.',
    '',
    'Says only what the proof does not presume; the surrounding sentences state positively what is '
    'proved (path classes, value constancy, connected components proved separately).',
    [R('C/09_C/prose/068', 'NON_CLAIM', 'retire',
       'Methodological remark on what the proof does not presume. No references.'),
     R('C/09_C/prose/067', 'LEAN', 'keep', 'Preceding sentence; unchanged.')])

add('E-09C-12', C, 'guard',
    r'gives the following restricted planar basin conclusion',
    r'gives the following planar basin conclusion',
    'Hedge word "restricted"; the hypotheses are listed in the next sentence.',
    [R('C/09_C/prose/117', 'LEAN', 'keep',
       'Anchor survives. The note of C/09_C/prose/070 quotes "The restricted planar basin conclusion" '
       '(note text only).')])

add('E-09C-13', C, 'caveat',
    r' Semialgebraicity alone does not give the dynamical conclusion: degenerate noncritical ties and flat contours remain outside this theorem.',
    '',
    'Scope caveat; the paragraph states the retained hypotheses (strict contours, regular two-branch '
    'switching) positively, and line 508 repeats that they are kept. Parallel to the article\'s deleted '
    '"The strict-contour and regular-switching assumptions remain essential to this sufficient planar '
    'route".',
    [R('C/09_C/prose/073', 'NON_CLAIM', 'retire',
       'Scope remark; no semialgebraic counterexample was asserted. The hypotheses remain in '
       'C/09_C/prose/070 and prose/110. No references.'),
     R('C/09_C/prose/072', 'SAME_AS', 'keep', 'Earlier sentence; unchanged.')])

add('E-09C-14', C, 'positive',
    r'Curved interfaces between arbitrary quadratic branches are not being replaced by finite polyhedral cells or by a nonlinear change of BFGS coordinates.',
    r'This example lies beyond Theorem~\ref{R:thm:plq}: its objective has no polyhedral-cell '
    r'representation near the minimizer. The convergence proof treats the curved interfaces directly, '
    r'in the original coordinates and with the unmodified BFGS update.',
    'Group note: the positive form of the revised article (local.tex:434-437), with the companion\'s '
    'polyhedral theorem R:thm:plq (Finite polyhedral partitions) in place of art:polyhedral and '
    '"convergence proof" to distinguish it from the RS computation just above. RS failure (preceding '
    'sentence) is unchanged.',
    [R('C/09_C/prose/081', 'SAME_AS', 'reanchor',
       'Still SAME_AS A/local/prose/044 (Local.quadratic_max_no_polyhedral_cells: no representation as in '
       'art:polyhedral = R:thm:plq near 0); the coordinator re-anchors A/local/prose/044 to the article\'s '
       'revised sentence, which this sentence now matches. The new second sentence ("The convergence proof '
       'treats the curved interfaces directly, in the original coordinates and with the unmodified BFGS '
       'update.") is the method description that 081\'s note assigned to the old clause "or by a nonlinear '
       'change of BFGS coordinates" (like A/local/prose/042-043, NON_CLAIM); a NON_CLAIM item for it may '
       'be added. C/09_C/prose/080 (RS fails) is untouched.',
       anchor='its objective has no polyhedral-cell representation near the minimizer'),
     R('C/09_C/prose/080', 'LEAN', 'keep', 'Preceding sentence (RS fails on a positive band); unchanged.')])

add('E-09C-15', C, 'guard',
    r'for every actual subgradient',
    r'for every subgradient',
    'Guard word "actual" ("every subgradient" already covers all of the subdifferential).',
    [R('C/09_C/prose/089', 'LEAN', 'keep', 'Anchor survives; claim unchanged.')])

add('E-09C-16', C, 'guard',
    r'\textbf{What does not follow:} $C^1$ regularity',
    r'The $C^1$ regularity',
    'Bold face on a negative statement; the sharp statement itself (LEAN) is kept.',
    [R('C/09_C/prose/094', 'LEAN', 'reanchor',
       'Claim unchanged (C1_field_without_transport). The Lean docstring Ch09C.lean:4319-4320 quotes the '
       'old anchor "\\textbf{What does not follow:}". C/09_C/prose/115 (SAME_AS of 094) is retired by '
       'E-09C-22.',
       anchor='regularity of this field does not provide the projected transport needed by the BFGS energy')])

add('E-09C-17', C, 'positive',
    r'This is not nonexistence of all certificates or a BFGS counterexample; it demonstrates',
    r'Every admissible run on it converges; the example demonstrates',
    '"This is not ... a BFGS counterexample" stated positively as the fact the register and Lean pair it '
    'with (radial_field_works: every admissible run converges); "not nonexistence of all certificates" '
    'is the preceding sentence (the radial field works).',
    [R('C/09_C/prose/101', 'LEAN', 'reanchor',
       'Same Lean (radial_field_works, last conjunct: every infinite admissible run converges). The '
       'Lean docstring Ch09C.lean:4443-4445 quotes the old anchor "This is not nonexistence of all '
       'certificates or a BFGS counterexample".',
       anchor='Every admissible run on it converges; the example demonstrates the gap'),
     R('C/09_C/prose/100', 'LEAN', 'keep', 'Sentence and anchor unchanged.')])

add('E-09C-18', C, 'caveat',
    r'; the literature audit does not establish publication priority for the full statements in this chapter',
    '',
    'Priority disclaimer; the kept clause states the relation positively (related results, different '
    'hypotheses or algorithms).',
    [R('C/09_C/prose/105', 'NON_CLAIM', 'keep',
       'Anchor survives; its reason "and a statement about the literature audit (priority)" no longer '
       'applies (literature description only).')])

add('E-09C-19', C, 'caveat',
    r'Here $h$ is a glued comparison function, without an asserted convex-support-function property.',
    r'Here $h$ is a glued comparison function, with no convex-support-function requirement.',
    'Replaces "without an asserted ... property" by the generality form used in Section 9.4.2 and in the '
    'article ("without a convexity requirement on $h$").',
    [R('C/09_C/prose/107', 'NON_CLAIM', 'reanchor',
       'Remark on h (no hypothesis of support-function type).',
       anchor=r'Here $h$ is a glued comparison function, with no convex-support-function requirement.'),
     R('C/09_C/prose/106', 'SAME_AS', 'keep', 'Preceding sentence; unchanged.')])

add('E-09C-20', C, 'positive',
    r'is a reproof of a consequence of',
    r'also follows from',
    'Defensive prior-work attribution made plain: the result also follows from [BDLS] (Chapter 8 gives '
    'its own proof and the same attribution).',
    [R('C/09_C/prose/109', 'NON_CLAIM', 'reanchor',
       'Relation to the literature [BDLS], unchanged in content.',
       anchor=r"Chapter~\ref{comp:A}'s finite-value result also follows from stratified projection")])

add('E-09C-21', C, 'positive',
    r', rather than every convergence criterion',
    '',
    '"X, rather than Y" -> X; the convergent basin of the same example makes Y evident.',
    [R('C/09_C/prose/112', 'SAME_AS', 'reanchor',
       'Claim unchanged (RS fails while the explicit basin holds).',
       anchor='The subsequent radial obstruction excludes the stated RS condition.')])

add('E-09C-22', C, 'caveat',
    r' Neither this antecedent nor the partial statement supplies the missing transport estimate in arbitrary dimension.',
    '',
    'Repeats the higher-dimensional limitation stated and proved in Section 9.9 ("The $C^1$ regularity of '
    'this field does not provide the projected transport ...", LEAN prose/094).',
    [R('C/09_C/prose/115', 'SAME_AS', 'retire',
       'SAME_AS of C/09_C/prose/094, which survives (re-anchored by E-09C-16). No references besides its '
       'own "of".'),
     R('C/09_C/prose/114', 'SAME_AS', 'keep', 'Preceding sentence; unchanged.')])

# ---------------------------------------------------------------- 14_E.tex
add('E-14E-01', E, 'guard',
    r'\textbf{Operative verification record.}',
    r'\textbf{Verification record.}',
    'Guard word "operative" (span title; PROOF_CORRESPONDENCE.html shows it after regeneration).')

add('E-14E-02', E, 'guard',
    r'consists of actual pinned Lean builds',
    r'consists of pinned Lean builds',
    'Guard word "actual" (the group note\'s example).',
    [R('C/14_E/prose/003', 'NON_CLAIM', 'reanchor', 'Description of the verification, unchanged.',
       anchor='The evidence for this edition consists of pinned Lean builds')])

add('E-14E-03', E, 'guard',
    r'algebraic roots, actual matrix updates,',
    r'algebraic roots, matrix updates,',
    'Guard word "actual".',
    [R('C/14_E/prose/007', 'NON_CLAIM', 'keep', 'Anchor survives.')])

add('E-14E-04', E, 'repeat',
    r' An external numerical result is not imported as a proof.',
    '',
    'Scope point (e) (numerics are not proofs); the chapter states its trust base once, in "Reproduce '
    'the audit": "No external symbolic, interval or numerical result is a trusted mathematical input."',
    [R('C/14_E/prose/008', 'NON_CLAIM', 'retire',
       'Same content as C/14_E/prose/099, which remains. No references.')])

add('E-14E-05', E, 'caveat',
    r'Compiler logs are evidence of actual executions; they are not axioms and do not prove that an older execution happened.',
    r'Compiler logs are evidence of the executions they record.',
    'Keeps what the logs evidence (the recorded executions) and drops the hedges "actual", "not axioms", '
    '"do not prove that an older execution happened".',
    [R('C/14_E/prose/009', 'NON_CLAIM', 'reanchor', 'Description of the verification.',
       anchor='Compiler logs are evidence of the executions they record.')])

add('E-14E-06', E, 'guard',
    r'are actual objective/run constructions',
    r'are explicit objective/run constructions',
    'Guard word "actual", replaced by "explicit" as in the revised article ("an explicit infinite '
    'admissible run").',
    [R('C/14_E/prose/011', 'SAME_AS', 'reanchor', 'Claim unchanged (seeds and embeddings are runs on '
       'explicit objectives).',
       anchor='The negative seeds and their embeddings are explicit objective/run constructions.')])

add('E-14E-07', E, 'guard',
    r'from actual principal determinants',
    r'from the principal determinants of the full-BFGS matrices',
    'Guard word "actual", replaced by what it meant, as in the revised abstract ("the principal minors of '
    'full-BFGS matrices").',
    [R('C/14_E/prose/012', 'SAME_AS', 'reanchor', 'Claim unchanged (its note: e_j(H_k) of the BFGS '
       'matrices).',
       anchor='derives its scalar hierarchy from the principal determinants of the full-BFGS matrices')])

add('E-14E-08', E, 'repeat',
    r'follows from the actual return map and a proved analytic argument, not a numerical starting vector assumed to lie on that manifold.',
    r'follows from the return map and a proved analytic argument.',
    'Drops "actual" and scope point (e) (rounded points are not claimed to lie on the stable manifold), '
    'stated in Chapter 1 and in Chapter 13.',
    [R('C/14_E/prose/013', 'SAME_AS', 'reanchor',
       'Claim unchanged (existence argument: stable_manifold_positive_scale, global_failure). Ch14E.lean:42 '
       'quotes the pre-M29 wording "The stable-manifold conclusion in L follows ..." (history, unaffected).',
       anchor=r'The stable-manifold conclusion in Chapter~\ref{comp:L} follows from the return map and a proved analytic argument.')])

add('E-14E-09', E, 'guard',
    r'\section{Actual build and audit register}',
    r'\section{Build and audit register}',
    'Guard word "actual" in a section title (label fresh-execution-register unchanged).')

add('E-14E-10', E, 'caveat',
    r'; the two scopes must not be conflated',
    '',
    'Guard clause; the table rows keep the two audits\' counts apart.',
    [R('C/14_E/prose/018', 'NON_CLAIM', 'reanchor', 'Description of the audits.',
       anchor='The current module-wide audit supplements the older namespace-based theorem audit.')])

add('E-14E-11', E, 'guard',
    r'Six actual supplemental compiler jobs',
    r'Six supplemental compiler jobs',
    'Guard word "actual"; the count is kept.',
    [R('C/14_E/prose/023', 'NON_CLAIM', 'reanchor', 'Table row, counts unchanged.',
       anchor='Claim review 20 & Six supplemental compiler jobs; 182 ordinary declaration reports')])

add('E-14E-12', E, 'guard',
    r'and actual type/value dependencies',
    r'and type/value dependencies',
    'Guard word "actual".',
    [R('C/14_E/prose/024', 'NON_CLAIM', 'keep', 'Anchor survives.')])

add('E-14E-13', E, 'guard',
    r'The actual command records',
    r'The command records',
    'Guard word "actual"; the location of the records is kept.',
    [R('C/14_E/prose/025', 'NON_CLAIM', 'reanchor', 'Description of the records, unchanged.',
       anchor=r'The command records, exit codes, compiler output and source hashes are delivered under')])

add('E-14E-14', E, 'positive',
    r'They describe present formal results, not a claim that the unavailable old scripts ran with their printed sample counts.',
    r'They describe present formal results.',
    'Hedge about the original report\'s scripts dropped; the positive statement stays.',
    [R('C/14_E/prose/030', 'NON_CLAIM', 'reanchor', 'Description of the suite labels.',
       anchor='They describe present formal results.')])

add('E-14E-15', E, 'guard',
    r'Actual algebraic seed existence',
    r'Algebraic seed existence',
    'Guard word "actual".',
    [R('C/14_E/prose/032', 'SAME_AS', 'reanchor', 'Claim unchanged.',
       anchor='Algebraic seed existence and isolation, denominator signs, accepted and rejected trial decisions')])

add('E-14E-16', E, 'positive',
    r', rather than a rounded seed',
    '',
    '"X, rather than Y" -> X (Y is scope point (e)); "exact" is mathematical and kept.',
    [R('C/14_E/prose/033', 'NON_CLAIM', 'reanchor', 'Remark on the formal statements (exact root, exact runs).',
       anchor='The root and containment statements apply to the exact specified objects.')])

add('E-14E-17', E, 'repeat',
    r' No symbolic-program output is accepted as a mathematical premise.',
    '',
    'Scope point (e); the preceding sentence says these are Lean equalities or inequalities, and the '
    'chapter states the trust base in "Reproduce the audit" (No external symbolic ... result is a '
    'trusted mathematical input).',
    [R('C/14_E/prose/036', 'NON_CLAIM', 'retire',
       'Same content as C/14_E/prose/099, which remains. No references.')])

add('E-14E-18', E, 'guard',
    r'establish the actual run',
    r'establish the run',
    'Guard word "actual".',
    [R('C/14_E/prose/037', 'SAME_AS', 'reanchor', 'Claim unchanged.',
       anchor='embedded local failure theorems establish the run and every stated line-search trial')])

add('E-14E-19', E, 'repeat',
    r'; a finite list of sampled trials is not their proof',
    '',
    'Scope point (e) (finite numerics are not proofs); "They imply the specified infinite behavior" stays.',
    [R('C/14_E/prose/038', 'SAME_AS', 'keep', 'Anchor "They imply the specified infinite behavior" survives.'),
     R('C/14_E/prose/039', 'NON_CLAIM', 'retire', 'Remark on the nature of the proofs. No references.')])

add('E-14E-20', E, 'guard',
    r'derivative of the actual return map',
    r'derivative of the return map',
    'Guard word "actual".',
    [R('C/14_E/prose/040', 'SAME_AS', 'reanchor', 'Claim unchanged.',
       anchor='The normalized Jacobian is the derivative of the return map.')])

add('E-14E-21', E, 'guard',
    r'and the actual stable-manifold construction',
    r'and the stable-manifold construction',
    'Guard word "actual".',
    [R('C/14_E/prose/041', 'SAME_AS', 'reanchor', 'Claim unchanged.',
       anchor='and the stable-manifold construction is linked to it')])

add('E-14E-22', E, 'caveat',
    r" The embedding's Hessian claims retain their stated local scope.",
    '',
    'Says only that claims are not stronger than stated.',
    [R('C/14_E/prose/042', 'NON_CLAIM', 'retire',
       'Remark on phrasing; the Hessian statements are in C/13_L (disp/004) and the article. No references.')])

add('E-14E-23', E, 'guard',
    r'their respective actual failure copies',
    r'their respective failure copies',
    'Guard word "actual".',
    [R('C/14_E/prose/044', 'SAME_AS', 'reanchor', 'Claim unchanged.',
       anchor='The smooth and step constructions then give their respective failure copies.')])

add('E-14E-24', E, 'caveat',
    r' The two regularity constructions retain their distinct hypotheses and conclusions.',
    '',
    'Defensive framing ("retain their distinct ..."); no content beyond the previous sentence.',
    [R('C/14_E/prose/045', 'NON_CLAIM', 'retire', 'Remark on presentation. No references.')])

add('E-14E-25', E, 'positive',
    r'The principal Gram-sum identity and full-BFGS principal-minor hierarchy use actual determinants. Selected finite-dimensional cases are not substituted for this theorem.',
    r'The principal Gram-sum identity and the full-BFGS principal-minor hierarchy are proved in the same generality.',
    'Positive form of both sentences: "actual" dropped, and "selected finite-dimensional cases are not '
    'substituted" stated as what it means (proved in arbitrary finite dimension, like the previous '
    'sentence).',
    [R('C/14_E/prose/047', 'SAME_AS', 'reanchor',
       'Same targets (M:hierarchy etc., proved for every n).',
       anchor='The principal Gram-sum identity and the full-BFGS principal-minor hierarchy are proved in the same generality.'),
     R('C/14_E/prose/048', 'NON_CLAIM', 'retire',
       'Its content (general dimension) is now stated in prose/047\'s sentence. No references.')])

add('E-14E-26', E, 'guard',
    r'Actual projected full updates',
    r'Projected full updates',
    'Guard word "actual".',
    [R('C/14_E/prose/049', 'SAME_AS', 'reanchor', 'Claim unchanged.',
       anchor='Projected full updates and the invariant matrix range give affine-fiber lifting.')])

add('E-14E-27', E, 'guard',
    r'the actual full-matrix hierarchy',
    r'the full-matrix hierarchy',
    'Guard word "actual".',
    [R('C/14_E/prose/052', 'SAME_AS', 'reanchor', 'Claim unchanged.',
       anchor='Along runs with bounded gradients, the full-matrix hierarchy yields the normalized hierarchy')])

add('E-14E-28', E, 'guard',
    r'and actual-run convergence',
    r'and convergence of admissible runs',
    'Guard word "actual", replaced by what it meant.',
    [R('C/14_E/prose/057', 'SAME_AS', 'reanchor', 'Claim unchanged.',
       anchor='lead to the stated radial basins and convergence of admissible runs')])

add('E-14E-29', E, 'caveat',
    r'with an actual full-BFGS failure run; it is not asserted to be an unidentified historical objective.',
    r'with a full-BFGS failure run.',
    'Drops the guard word "actual" and the disclaimer about an unidentified historical objective; '
    '"a new specified reconstruction" already says what it is.',
    [R('C/14_E/prose/061', 'SAME_AS', 'reanchor',
       'Claim unchanged (fourPiece_failure_run). Ch14E.lean:43 quotes the pre-M29 wording (history).',
       anchor=r'The explicit four-piece objective in Chapter~\ref{comp:R} is a new specified reconstruction with a full-BFGS failure run'),
     R('C/14_E/prose/062', 'NON_CLAIM', 'retire', 'History disclaimer. No references.')])

add('E-14E-30', E, 'positive',
    r'Accessible and all-active jump spans remain distinct.',
    r'Accessible and all-active jump spans can differ.',
    '"X remains distinct" stated as the proved fact it stands for (Ch05G.accessible_span_differs: '
    'N_acc = {0} while N = R for an explicit scalar example).',
    [R('C/14_E/prose/064', 'SAME_AS', 'reanchor',
       'Same targets (C/05_G/prose/035, prose/044).',
       anchor='Accessible and all-active jump spans can differ.')])

add('E-14E-31', E, 'caveat',
    r' Failure of a certificate is not represented as failure of BFGS.',
    '',
    'Disclaimer; the chapter states the fact positively in T-certificate (scalar nonnecessity) and '
    'G-oscillatory ("It disproves local certificate existence while scalar admissible runs converge").',
    [R('C/14_E/prose/065', 'SAME_AS', 'retire',
       'Its content (certificate failure with convergent runs) is stated by C/14_E/prose/070 and '
       'C/14_E/prose/082, which remain (same targets C/05_G/prose/002, prose/068). No references.')])

add('E-14E-32', E, 'guard',
    r'are operative formal results',
    r'are formal results',
    'Guard word "operative".',
    [R('C/14_E/prose/067', 'LEAN', 'reanchor',
       'Claim unchanged. The Lean docstring Ch14E.lean:139-140 quotes "[is an] operative formal result".',
       anchor='the scalar-ridge implication into the planar convergence theorem are formal results'),
     R('C/14_E/prose/066', 'SAME_AS', 'keep', 'Anchor "The moving-frame identity" survives.')])

add('E-14E-33', E, 'caveat',
    r' No unavailable independent ridge archive is needed for that implication.',
    '',
    'Disclaimer about an unavailable historical archive; the implication is stated as a formal result.',
    [R('C/14_E/prose/068', 'NON_CLAIM', 'retire', 'History of the source report. No references.')])

add('E-14E-34', E, 'guard',
    r'transport and actual BFGS convergence',
    r'transport and BFGS convergence',
    'Guard word "actual".',
    [R('C/14_E/prose/069', 'SAME_AS', 'reanchor', 'Claim unchanged.',
       anchor='certificate normalization, transport and BFGS convergence are proved')])

add('E-14E-35', E, 'positive',
    r'establishes a separate logical limitation of the sufficient condition',
    r'shows that the sufficient condition is not necessary',
    'Nonnecessity result kept and stated plainly (the register note: "The limitation named is that the '
    'sufficient condition is not necessary"); drops the defensive "separate logical limitation".',
    [R('C/14_E/prose/070', 'SAME_AS', 'reanchor', 'Same targets (C/05_G/prose/002, prose/068).',
       anchor='The scalar nonnecessity result shows that the sufficient condition is not necessary.')])

add('E-14E-36', E, 'guard',
    r'actual angular derivative',
    r'angular derivative',
    'Guard word "actual".',
    [R('C/14_E/prose/071', 'SAME_AS', 'reanchor', 'Claim unchanged.',
       anchor='The correctly oriented determinant identity, angular derivative, all-pair endpoint estimates')])

add('E-14E-37', E, 'caveat',
    r' The higher-dimensional example does not invalidate the restricted planar theorem.',
    '',
    'Disclaimer; the three-dimensional warning concerns a proof device, not BFGS, and Chapter 9 now says '
    'that every run on it converges.',
    [R('C/14_E/prose/072', 'NON_CLAIM', 'retire', 'Consistency remark. No references.')])

add('E-14E-38', E, 'caveat',
    r' It is not a finite truncation used as a proxy for the function.',
    '',
    'Disclaimer; the previous sentence says positively that the oracle is the complete infinite-series '
    'objective.',
    [R('C/14_E/prose/075', 'NON_CLAIM', 'retire',
       'Its mathematics (exact evaluation of the whole series) is C/11_U/prose/055 and prose/074 here. '
       'No references.'),
     R('C/14_E/prose/074', 'SAME_AS', 'keep', 'Preceding sentence; unchanged.')])

add('E-14E-39', E, 'guard',
    r'The operative statement is analytic:',
    r'The statement is analytic:',
    'Guard word "operative".',
    [R('C/14_E/prose/076', 'LEAN', 'reanchor',
       'Claim unchanged (planar_tolerance). The Lean docstring Ch14E.lean:186 quotes "The operative '
       'statement is analytic".',
       anchor=r'The statement is analytic: the stated planar example converges from its basin~\eqref{C:eq:explicitbasin}')])

add('E-14E-40', E, 'caveat',
    r' This does not establish the original execution count, trial count, decimal precision or a particular iteration at which a tolerance was attained.',
    '',
    'Disclaimer about the original report\'s run data (the group note\'s "this does not certify").',
    [R('C/14_E/prose/077', 'NON_CLAIM', 'retire', 'History disclaimer. No references.')])

add('E-14E-41', E, 'guard',
    r'The actual fixed-normal spike objective',
    r'The fixed-normal spike objective',
    'Guard word "actual".',
    [R('C/14_E/prose/078', 'SAME_AS', 'reanchor', 'Claim unchanged.',
       anchor='The fixed-normal spike objective has a complete oracle and the stated convergence basin')])

add('E-14E-42', E, 'caveat',
    r' Historical run lengths, starts and precision remain unsupported rather than retrospectively certified.',
    '',
    'Hedge on historical data (the group note\'s "unsupported historical ...").',
    [R('C/14_E/prose/080', 'NON_CLAIM', 'retire', 'History disclaimer. No references.'),
     R('C/14_E/prose/079', 'LEAN', 'keep', 'Preceding sentence; unchanged.')])

add('E-14E-43', E, 'caveat',
    r'; it is not identified with that auxiliary or used as an infinite bad BFGS trajectory',
    '',
    'Disclaimer; the replacement is stated plainly and the previous sentence says the scalar runs converge.',
    [R('C/14_E/prose/083', 'NON_CLAIM', 'reanchor', 'History of the source report, stated plainly.',
       anchor='This construction replaces an unavailable auxiliary.')])

add('E-14E-44', E, 'positive',
    r'Reviewed analytic arguments and remaining boundaries',
    r'Reviewed analytic arguments and open questions',
    'Section title follows its content once the boundary list is deleted (E-14E-46, -48 to -50); label '
    'unchanged.')

add('E-14E-45', E, 'guard',
    r'The actual matrix hierarchy',
    r'The matrix hierarchy',
    'Guard word "actual".',
    [R('C/14_E/prose/084', 'SAME_AS', 'keep',
       'Anchor "all have formal proof chains in the delivered project" survives; its note quotes "The '
       'actual matrix hierarchy" (note text only).')])

add('E-14E-46', E, 'caveat',
    r' Assumptions such as regular switching, fixed normals, compact structural sublevels or low effective rank remain substantive.',
    '',
    'Hedge on hypotheses that the theorems state; parallel to the article\'s deleted "assumptions remain '
    'essential" sentence.',
    [R('C/14_E/prose/086', 'NON_CLAIM', 'retire', 'Remark on hypotheses. No references.')])

add('E-14E-47', E, 'positive',
    r'The broader questions explicitly marked open in Chapters~\ref{comp:A} and~\ref{comp:H} are not proved.',
    r'Chapters~\ref{comp:A} and~\ref{comp:H} record the broader open questions.',
    'Open questions kept, phrased plainly (no "explicitly", no "are not proved" framing).',
    [R('C/14_E/prose/087', 'OPEN', 'reanchor',
       'Status OPEN unchanged (same Lean propositions: GeneralDimensionalConjecture, '
       'ZeroValueIterateQuestion, TiltNoInfiniteRunQuestion).',
       anchor=r'Chapters~\ref{comp:A} and~\ref{comp:H} record the broader open questions.')])

add('E-14E-48', E, 'repeat',
    r' Nor does the report claim convergence for every finite convex nonsmooth objective, a positive-measure basin for the deterministic seed, robustness to floating-point perturbation, or a rounded initial point lying exactly on the stable manifold.',
    '',
    'Scope points (b) and (e) and a general disclaimer, stated in Chapter 1.',
    [R('C/14_E/prose/088', 'NON_CLAIM', 'retire', 'Disclaimer. No references.')])

add('E-14E-49', E, 'caveat',
    r' No publication-priority claim is made.',
    '',
    'Priority disclaimer.',
    [R('C/14_E/prose/089', 'NON_CLAIM', 'retire', 'No references.')])

add('E-14E-50', E, 'caveat',
    r' Those boundaries are part of the corrected statement, not gaps concealed by the compiler pass.',
    '',
    'Defensive remark; it also refers to the deleted boundary list.',
    [R('C/14_E/prose/090', 'NON_CLAIM', 'retire', 'Editorial remark. No references.')])

add('E-14E-51', E, 'guard',
    r'The audit records the actual commands',
    r'The audit records the commands',
    'Guard word "actual".',
    [R('C/14_E/prose/094', 'NON_CLAIM', 'reanchor', 'Description of the audit, unchanged.',
       anchor='The audit records the commands and compiler output, checks the main source hashes')])

add('E-14E-52', E, 'positive',
    r', not the consistency of the permitted standard axioms',
    '',
    '"X, not Y" -> X; what the audit verifies is stated.',
    [R('C/14_E/prose/098', 'NON_CLAIM', 'reanchor', 'Description of the audit.',
       anchor='The axiom audit verifies proof dependencies.')])

add('E-14E-53', E, 'caveat',
    r'; they perform no unchecked computation for a Lean proof',
    '',
    'Reassurance clause; "These are document tools" says what they are.',
    [R('C/14_E/prose/105', 'NON_CLAIM', 'reanchor', 'Description of the tools.',
       anchor='These are document tools.')])

add('E-14E-54', E, 'guard',
    r'and actual compiler evidence',
    r'and compiler evidence',
    'Guard word "actual".',
    [R('C/14_E/prose/106', 'NON_CLAIM', 'reanchor', 'Description of the records, unchanged.',
       anchor='bind the generated report, source correspondence and compiler evidence')])


# ---------------------------------------------------------------- checks
texts = {f: (REPO / f).read_text() for f in (C, E)}
ok = True
for p in P:
    n = texts[p['file']].count(p['old'])
    if n != 1:
        ok = False
        print('NOT UNIQUE', p['id'], n, repr(p['old'][:60]))
# apply to check anchors exist in rendered text
rendered = dict(texts)
for f in (C, E):
    group = sorted((p for p in P if p['file'] == f), key=lambda p: -texts[f].index(p['old']))
    t = texts[f]
    for p in group:
        s = t.index(p['old']) if t.count(p['old']) == 1 else None
        if s is None:
            continue
        t = t[:s] + p['new'] + t[s + len(p['old']):]
    rendered[f] = t
for p in P:
    norm = ' '.join(rendered[p['file']].split())
    for r in p['register']:
        if 'anchor' in r:
            a = ' '.join(r['anchor'].split())
            c = norm.count(a)
            if c != 1:
                ok = False
                print('ANCHOR COUNT', p['id'], r['item'], c, repr(a[:60]))
out = {'group': 'E', 'proposals': P}
Path('/tmp/opencode/m44/companion/proposals_E.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
print(len(P), 'proposals written;', 'all old unique and anchors found' if ok else 'PROBLEMS')
