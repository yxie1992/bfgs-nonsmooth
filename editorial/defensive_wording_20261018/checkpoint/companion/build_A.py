#!/usr/bin/env python3
"""Build proposals_A.json (group A: 01_I.tex, 02_M.tex). Scratch helper; never touches the repository."""
import json
from pathlib import Path

REPO = Path('/home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth')
I = 'companion/chapters/01_I.tex'
M = 'companion/chapters/02_M.tex'
P = []


def add(pid, file, kind, old, new, reason, register):
    P.append({'id': pid, 'file': file, 'kind': kind, 'old': old, 'new': new,
              'reason': reason, 'register': register})


def R(item, status, action, note='', anchor=None):
    r = {'item': item, 'status': status, 'action': action}
    if anchor is not None:
        r['anchor'] = anchor
    if note:
        r['note'] = note
    return r


# ---------------------------------------------------------------- 01_I
add('A-01I-01', I, 'guard',
    r'This inventory states the operative mathematical scope.',
    r'This inventory states the mathematical scope.',
    'Guard word "operative" removed.',
    [R('C/01_I/prose/002', 'NON_CLAIM', 'reanchor', 'Edition note; "operative" removed.',
       anchor=r'This inventory states the mathematical scope.')])

add('A-01I-02', I, 'caveat',
    r'The original source record is preserved separately; unsupported historical execution and archive assertions are not repeated as facts.',
    r'The original source record is preserved separately.',
    'Disclaimer about unsupported historical assertions of the source record; the reader only needs to know where the record is.',
    [R('C/01_I/prose/002', 'NON_CLAIM', 'keep',
       'Same edition-note item; its anchor is edited by A-01I-01 only. The deleted clause is also stated (and deleted) at line 343 (A-01I-49).')])

add('A-01I-03', I, 'guard',
    r'substantive unnamed deductions and actual objective applications are included.',
    r'substantive unnamed deductions and objective applications are included.',
    'Guard word "actual" removed ("objective applications" is the chapter\'s term, cf. P3).',
    [R('C/01_I/prose/003', 'NON_CLAIM', 'keep', 'Anchor (first sentence of the paragraph) unchanged.')])

add('A-01I-04', I, 'positive',
    r'Some informal proof routes have been replaced by different formal proofs; these changes are disclosed rather than described as literal translations.',
    r'Some informal proof routes have been replaced by different formal proofs, and these replacements are recorded.',
    '"X rather than Y" rewritten as the positive fact.',
    [R('C/01_I/prose/003', 'NON_CLAIM', 'keep', 'Anchor unchanged; process statement only.')])

add('A-01I-05', I, 'caveat',
    r' No unavailable provenance archive is required to reproduce the formal proofs.',
    r'',
    'Defensive remark about an unavailable archive; the delivered sources are listed in the previous sentence and reproduction is in Chapter E.',
    [R('C/01_I/prose/004', 'NON_CLAIM', 'keep', 'Anchor (first sentence) unchanged; the last sentence of the paragraph is deleted.')])

add('A-01I-06', I, 'caveat',
    r" This is not a proof of Lean's consistency, a human-referee certification or a publication-priority claim.",
    r'',
    'States what the verification is not (consistency, referee certification, priority); same deletion as the article (V3).',
    [R('C/01_I/prose/005', 'NON_CLAIM', 'keep',
       'Anchor unchanged; the reason "and of its limits" no longer applies to a deleted sentence.')])

add('A-01I-07', I, 'caveat',
    r' Background bibliographic pointers are separate from formal proof dependencies.',
    r'',
    'Says what bibliographic pointers are not; the "Relation to earlier work" section already introduces the bibliography (coordinator sentence).',
    [R('C/01_I/prose/005', 'NON_CLAIM', 'keep', 'Anchor unchanged.')])

add('A-01I-08', I, 'positive',
    r'unless a more specific implementation is stated.',
    r'unless a more specific implementation is stated. The certificates, frames and comparison energies of the positive theory are used only in the proofs.',
    'ADDED SENTENCE: scope point (c) is stated nowhere in 01_I; this is its single plain statement (cf. article I7), so that later chapters can drop their repeats.',
    [R('C/01_I/prose/008', 'NON_CLAIM', 'keep',
       'Anchor unchanged. NEW SENTENCE "The certificates, frames and comparison energies of the positive theory are used only in the proofs." needs a new NON_CLAIM prose item (scope convention, scope point (c); no mathematical claim).')])

add('A-01I-09', I, 'positive',
    r'Three conclusions must remain distinct:',
    r'We distinguish three conclusions:',
    '"must remain distinct" is defensive framing; the display that follows is unchanged.',
    [])

add('A-01I-10', I, 'caveat',
    r'; arbitrary nonunique solution sets do not inherit that conclusion.',
    r'.',
    'Non-claim; the question (iterate convergence for arbitrary nonunique solution sets) is stated once in the open-gap list of Section "Verification and unresolved boundaries".',
    [R('C/01_I/prose/011', 'NON_CLAIM', 'retire',
       'The open question survives as C/01_I/prose/140 (OPEN, NonuniqueIterateConvergence). Mentioned by text (not by "of") in the reason of an item of editorial/lean_coverage/register/C_research_story.json ("parallel of C/07_H/prose/019 and C/01_I/prose/011"); no Lean reference.'),
     R('C/01_I/prose/010', 'SAME_AS', 'keep', 'Anchor "Affine-fiber nonuniqueness has a separate lifting theorem" survives.')])

add('A-01I-11', I, 'positive',
    r'The positive statements must not silently be strengthened into universal all-ray existence or finite oracle complexity.',
    r'Existence of an infinite admissible run is a hypothesis of the positive theorems. Their quantitative conclusions are the stated rates and finite-horizon bounds, measured in iterations.',
    'Scope points (a) and (f), stated once and positively instead of "must not silently be strengthened".',
    [R('C/01_I/prose/014', 'NON_CLAIM', 'reanchor',
       'Scope convention (a) run existence is a hypothesis (five-piece obstruction Ch06F.five_piece_obstruction: an acceptable point need not exist on every ray), (f) the quantitative conclusions are the stated rates and finite-horizon bounds, counted in iterations (no oracle complexity).',
       anchor=r'Existence of an infinite admissible run is a hypothesis of the positive theorems.'),
     R('C/01_I/prose/013', 'LEAN', 'keep', 'Preceding sentence; anchor and claim unchanged.')])

add('A-01I-12', I, 'positive',
    r'\section{The negative results that must both be retained}',
    r'\section{Negative results}',
    'Section title rephrased positively; the \\label is unchanged and no register anchor quotes the title.',
    [])

add('A-01I-13', I, 'guard',
    r'The \textbf{actual deterministic unit-first weak-Wolfe doubling/bisection search}',
    r'The \textbf{deterministic unit-first weak-Wolfe doubling/bisection search}',
    'Guard word "actual" removed (the search is specified by name).',
    [R('C/01_I/prose/016', 'LEAN', 'keep', 'Anchor "There is one fixed coercive ..." unchanged; claim unchanged.')])

add('A-01I-14', I, 'caveat',
    r'This is a failure of a deterministic neighborhood guarantee, not a claim that every close start fails.',
    r'This is a failure of a deterministic neighborhood guarantee.',
    'Drops "not a claim that every close start fails" (scope point (b); positive-measure failure is in the open-gap list).',
    [R('C/01_I/prose/017', 'SAME_AS', 'reanchor', 'Same restatement of the quantifiers of prose/016.',
       anchor=r'This is a failure of a deterministic neighborhood guarantee.')])

add('A-01I-15', I, 'guard',
    r'Three of the four branches \textbf{are not twice differentiable at the minimizer}.',
    r'Three of the four branches are not twice differentiable at the minimizer.',
    'Bold face on a negative statement removed; the corrected mathematical fact (M8/M30) is kept verbatim.',
    [R('C/01_I/prose/023', 'SAME_AS', 'reanchor', 'Only the bold face is removed; claim unchanged.',
       anchor=r'Three of the four branches are not twice differentiable at the minimizer.'),
     R('C/01_I/prose/022', 'LEAN', 'keep', 'Preceding sentence; anchor and claim unchanged.')])

add('A-01I-16', I, 'caveat',
    r', not a displayed rounded point claimed to lie exactly on that manifold.',
    r'.',
    'Scope point (e) is stated once, in Section "Verification and unresolved boundaries" (line 345); the positive description of the seed stays.',
    [R('C/01_I/prose/026', 'NON_CLAIM', 'reanchor', 'Description of the proof method; the disclaimer part is deleted (kept once at prose/135).',
       anchor=r'Its bad seed is an existence object on a certified hyperbolic stable manifold.')])

add('A-01I-17', I, 'caveat',
    r'\textbf{N1 and N2 are not merged into a fictitious stronger theorem.} ',
    r'',
    'Bold defensive lead sentence; the comparison of N1 and N2 that follows states the point positively.',
    [R('C/01_I/prose/028', 'LEAN', 'keep',
       'Anchor and claim unchanged; the note\'s mention of the bold editorial lead sentence becomes obsolete.')])

add('A-01I-18', I, 'positive',
    r' It is not superseded by an accumulation-based local example.',
    r'',
    '"X is not superseded by Y"; the positive statement of X is the previous sentence.',
    [R('C/01_I/prose/033', 'NON_CLAIM', 'retire', 'Editorial non-claim; no references found.'),
     R('C/01_I/prose/032', 'LEAN', 'keep', 'Anchor and claim unchanged.')])

add('A-01I-19', I, 'positive',
    r'\section{General positive mechanisms: retain distinct hypotheses}',
    r'\section{General positive mechanisms}',
    'Section title rephrased positively; \\label unchanged; no register anchor quotes it.',
    [])

add('A-01I-20', I, 'positive',
    r'Its equivalent inward Taylor condition is useful for checking functions, but is not a separate strongest certificate theorem.',
    r'Its equivalent inward Taylor condition is useful for checking functions.',
    'Drops "is not a separate strongest certificate theorem" (brief: drop this framing).',
    [R('C/01_I/prose/049', 'SAME_AS', 'reanchor', 'The editorial rest of the sentence is deleted; the equivalence (R:thm:equiv) stays.',
       anchor=r'Its equivalent inward Taylor condition is useful for checking functions.'),
     R('C/01_I/prose/048', 'SAME_AS', 'keep', 'Preceding sentence; unchanged.')])

add('A-01I-21', I, 'guard',
    r'The transported condition itself is not necessary for actual convergence.',
    r'The transported condition is not necessary for convergence.',
    'Nonnecessity result (Chapter G) kept as the single plain statement of scope point (d); guard words "itself", "actual" removed.',
    [R('C/01_I/prose/051', 'SAME_AS', 'reanchor', 'Same nonnecessity result (C/05_G/prose/068).',
       anchor=r'The transported condition is not necessary for convergence.'),
     R('C/01_I/prose/050', 'SAME_AS', 'keep', 'Preceding sentence (strict inclusion of RS); unchanged.')])

add('A-01I-22', I, 'guard',
    r'the actual update gives',
    r'the BFGS update gives',
    'Guard word "actual" removed.',
    [R('C/01_I/prose/055', 'LEAN', 'reanchor', 'Wording only; mathematical content unchanged.',
       anchor=r'If a fixed subspace \(S\) satisfies \(\|P_Sy_k\|^2\le L_Sy_k^Ts_k\), the BFGS update gives \(\operatorname{tr}(P_SB_k)=O(k)\) for \(B_k=H_k^{-1}\).')])

add('A-01I-23', I, 'guard',
    r'This extends the proof mechanism; \textbf{a strict inclusion between the existential function classes of P1 and P3 has not been proved}.',
    r'This extends the proof mechanism; whether one of the existential function classes of P1 and P3 strictly contains the other is open.',
    'Bold "has not been proved" turned into a plain open question (kept once; its repeats in the supersession table and 02_M:275 are deleted).',
    [R('C/01_I/prose/057', 'NON_CLAIM', 'reanchor',
       'Now phrased as an open question; the coordinator may change the status to OPEN (no Lean Prop exists for it).',
       anchor=r'This extends the proof mechanism; whether one of the existential function classes of P1 and P3 strictly contains the other is open.')])

add('A-01I-24', I, 'positive',
    r'Also retained are finite sums of powered nonnegative gauges',
    r'Also covered are finite sums of powered nonnegative gauges',
    'Consolidation framing "retained" replaced by the positive statement.',
    [R('C/01_I/prose/067', 'SAME_AS', 'reanchor', 'Same families (C/06_F/prose/011, F:transform).',
       anchor=r'Also covered are finite sums of powered nonnegative gauges, and increasing convex smooth transforms of coercive gauges.')])

add('A-01I-25', I, 'positive',
    r'For smooth-plus-polyhedral objectives, retain the explicit sufficient basin threshold obtained by',
    r'For smooth-plus-polyhedral objectives, an explicit sufficient basin threshold is obtained by',
    'Imperative "retain" replaced by the statement of the result.',
    [R('C/01_I/prose/071', 'SAME_AS', 'reanchor', 'Same threshold (C/06_F/disp/010, prose/017).',
       anchor=r'For smooth-plus-polyhedral objectives, an explicit sufficient basin threshold is obtained by minimizing the objective over the active regions of pieces inactive at the optimizer.')])

add('A-01I-26', I, 'positive',
    r'For nonunique affine fibers, retain the exact linear-image lifting formula.',
    r'For nonunique affine fibers, there is an exact linear-image lifting formula.',
    'Imperative "retain" replaced by the statement of the result.',
    [R('C/01_I/prose/072', 'SAME_AS', 'reanchor', 'Same theorem F:lifting.',
       anchor=r'For nonunique affine fibers, there is an exact linear-image lifting formula.'),
     R('C/01_I/prose/071', 'SAME_AS', 'keep', 'Preceding sentence; reanchored by A-01I-25, not by this proposal.')])

add('A-01I-27', I, 'caveat',
    r' These are not replaced by a generic uniqueness statement.',
    r'',
    'Says what the results are not replaced by; no content.',
    [R('C/01_I/prose/073', 'NON_CLAIM', 'retire', 'Editorial non-claim; no references found.'),
     R('C/01_I/prose/072', 'SAME_AS', 'keep', 'Preceding sentence; reanchored by A-01I-26, not by this proposal.')])

add('A-01I-28', I, 'caveat',
    'This does not cover every planar finite maximum: rank-degenerate ties and flat positive contours are outside the stated theorem. Nor does it prove the arbitrary-dimensional rotating-normal conjecture.\n\n',
    '',
    'Paragraph restates P5\'s hypotheses negatively; the flat-contour sharpness fact is kept at P6 and the rotating-normal conjecture in the open-gap list.',
    [R('C/01_I/prose/079', 'SAME_AS', 'retire',
       'Same fact as C/01_I/prose/088 (P6, also SAME_AS C/10_Q/prose/001); rank-degenerate ties are excluded by P5\'s hypothesis of linearly independent active gradients. No references found.'),
     R('C/01_I/prose/080', 'NON_CLAIM', 'retire',
       'The conjecture stays in the open-gap list (C/01_I/prose/136, OPEN). No references found.')])

add('A-01I-29', I, 'positive',
    r'is a \textbf{corollary of P5}, not an independent strongest theorem.',
    r'is a \textbf{corollary of P5}.',
    'Drops "not an independent strongest theorem"; the supersession fact (corollary of P5) stays.',
    [R('C/01_I/prose/082', 'LEAN', 'keep', 'Anchor "The older theorem for" and claim unchanged.')])

add('A-01I-30', I, 'caveat',
    r'This is a disclosed deduction between the stated theorems. ',
    r'',
    'Provenance hedge ("disclosed"); the next sentence says where the implication is proved.',
    [R('C/01_I/prose/084', 'NON_CLAIM', 'reanchor',
       'Provenance remark now carried by the remaining sentence (after A-01I-31).',
       anchor=r'The implication and its formal proof are included here and in the Lean index.')])

add('A-01I-31', I, 'guard',
    r'The operative implication and its formal proof are included here and in the Lean index; no unavailable independent archive is needed.',
    r'The implication and its formal proof are included here and in the Lean index.',
    'Guard word "operative" and the unavailable-archive hedge removed.',
    [R('C/01_I/prose/084', 'NON_CLAIM', 'reanchor', 'See A-01I-30 (same anchor).',
       anchor=r'The implication and its formal proof are included here and in the Lean index.')])

add('A-01I-32', I, 'positive',
    r'Such branches can create flat contour segments, so P5 does \textbf{not} subsume the whole family.',
    r'Such branches can create flat contour segments, which put those members of the family outside P5.',
    'Bold "not subsume" rewritten as the positive sharpness fact (brief example).',
    [R('C/01_I/prose/088', 'SAME_AS', 'reanchor', 'Same fact (C/10_Q/prose/001).',
       anchor=r'Such branches can create flat contour segments, which put those members of the family outside P5.'),
     R('C/01_I/prose/087', 'SAME_AS', 'keep', 'Preceding sentence; unchanged.')])

add('A-01I-33', I, 'guard',
    r'\textbf{parallel genuinely nonsmooth interfaces}',
    r'\textbf{parallel nondifferentiable interfaces}',
    '"genuinely nonsmooth" replaced by the precise hypothesis of Theorem 11.2 (every point of the interfaces is nondifferentiable).',
    [R('C/01_I/prose/095', 'SAME_AS', 'reanchor', 'Same theorem (C/11_U/heading/002, prose/020).',
       anchor=r'A separate cluster theorem permits a closed collection of \textbf{parallel nondifferentiable interfaces}.')])

add('A-01I-34', I, 'positive',
    r'The arbitrary-dimensional result is not a planar reduction or a block-diagonal algorithm. Its real restriction is the fixed normal direction.',
    r'The arbitrary-dimensional result applies to full BFGS in every dimension, with an arbitrary SPD initial matrix; its main restriction is the fixed normal direction.',
    '"is not a planar reduction or a block-diagonal algorithm" restated positively (as 11_U:447 does); "real" dropped.',
    [R('C/01_I/prose/098', 'SAME_AS', 'reanchor', 'Same content (C/11_U/prose/005 every dimension, prose/012 full BFGS with any coupled SPD initial matrix).',
       anchor=r'The arbitrary-dimensional result applies to full BFGS in every dimension, with an arbitrary SPD initial matrix'),
     R('C/01_I/prose/099', 'NON_CLAIM', 'reanchor', 'Same evaluative remark, now a clause of the merged sentence.',
       anchor=r'its main restriction is the fixed normal direction.')])

add('A-01I-35', I, 'positive',
    r'This remains nonredundant because it covers functions lacking every local transported certificate.',
    r'The result covers functions lacking every local transported certificate.',
    '"remains nonredundant because" dropped; the positive content (P8 covers certificate-free functions) stays.',
    [R('C/01_I/prose/103', 'SAME_AS', 'reanchor', 'Same fact (C/05_G/prose/068, prose/066).',
       anchor=r'The result covers functions lacking every local transported certificate.'),
     R('C/01_I/prose/102', 'SAME_AS', 'keep', 'Anchor and claim unchanged.')])

add('A-01I-36', I, 'positive',
    r'\section{Noncompact homogeneous theory remains independent}',
    r'\section{Noncompact homogeneous theory}',
    'Section title rephrased positively; \\label unchanged; no register anchor quotes it.',
    [])

add('A-01I-37', I, 'positive',
    r'For finite max-linear objectives, retain three refinements:',
    r'For finite max-linear objectives, there are three refinements:',
    'Imperative "retain" replaced by the statement.',
    [R('C/01_I/prose/107', 'SAME_AS', 'reanchor', 'Same three results.',
       anchor=r'For finite max-linear objectives, there are three refinements')])

add('A-01I-38', I, 'guard',
    r'The noncompact zero-value iterate branch in recurrent dimension at least three is \textbf{not completely classified}.',
    r'The complete classification of the noncompact zero-value iterate branch in recurrent dimension at least three is open.',
    'Bold negative turned into a plain open question; the question is kept.',
    [R('C/01_I/prose/109', 'OPEN', 'reanchor', 'Same open question (Ch07H.ZeroValueIterateQuestion).',
       anchor=r'The complete classification of the noncompact zero-value iterate branch in recurrent dimension at least three is open.')])

add('A-01I-39', I, 'positive',
    r'The two-piece finite-escape theorem from Xie--Wächter is pre-existing background and remains stronger in its finite-termination conclusion than the new many-piece infinite-run escape statement. That paper~\cite{XW} is prior work, not a new result of this report.',
    r'The two-piece finite-escape theorem is due to Xie--Wächter~\cite{XW}; its finite-termination conclusion is stronger than that of the new many-piece infinite-run escape statement.',
    'Defensive prior-work attribution made a positive attribution; the comparison (C/07_H/prose/044) is kept.',
    [R('C/01_I/prose/112', 'SAME_AS', 'reanchor', 'Same attribution and comparison (C/07_H/prose/044).',
       anchor=r'The two-piece finite-escape theorem is due to Xie--Wächter~\cite{XW}'),
     R('C/01_I/prose/113', 'NON_CLAIM', 'retire',
       'The attribution is merged into prose/112\'s sentence ("is due to Xie--Wächter~\\cite{XW}"). No references found.')])

add('A-01I-40', I, 'positive',
    r'Retain the explicit finite-horizon bound as well; an asymptotic statement does not replace its finite constants.',
    r'Chapter~\ref{comp:M} also records the explicit finite-horizon bound behind this limit.',
    'Imperative "retain ... does not replace" restated as the positive fact.',
    [R('C/01_I/prose/115', 'NON_CLAIM', 'reanchor', 'Pointer to the finite-horizon bound of Theorem M:superquadratic.',
       anchor=r'Chapter~\ref{comp:M} also records the explicit finite-horizon bound behind this limit.')])

add('A-01I-41', I, 'caveat',
    r'This last sentence is an explicit consolidation consequence of the two displayed inequalities, not a claim of an additional source theorem.',
    r'This last sentence is a consolidation consequence of the two displayed inequalities.',
    'Provenance kept, the "not a claim of" hedge and the guard "explicit" dropped.',
    [R('C/01_I/prose/119', 'NON_CLAIM', 'reanchor', 'Provenance remark.',
       anchor=r'This last sentence is a consolidation consequence of the two displayed inequalities.'),
     R('C/01_I/prose/118', 'SAME_AS', 'keep', 'Preceding sentence; unchanged.')])

add('A-01I-42', I, 'guard',
    r'These are disclosed consolidation deductions, proved in Chapter~\ref{comp:F} while preserving the stronger explicit finite-horizon inequalities.',
    r'These are consolidation deductions, proved in Chapter~\ref{comp:F} together with the stronger explicit finite-horizon inequalities.',
    'Guard word "disclosed" removed; "while preserving" made plain.',
    [R('C/01_I/prose/122', 'NON_CLAIM', 'reanchor',
       'Provenance remark; the disclaimers mentioned in the reason are deleted by A-01I-43.',
       anchor=r'These are consolidation deductions, proved in Chapter~\ref{comp:F} together with the stronger explicit finite-horizon inequalities.'),
     R('C/01_I/prose/121', 'SAME_AS', 'keep', 'Preceding sentence (the rates); unchanged.')])

add('A-01I-43', I, 'caveat',
    r' They are not uniform rates over arbitrary certificates, sharpness statements, or line-search evaluation bounds.',
    r'',
    'Scope point (f) is stated once at line 57; sharp rates are in the open-gap list.',
    [R('C/01_I/prose/122', 'NON_CLAIM', 'keep', 'Its disclaimer part is deleted; anchor handled by A-01I-42.')])

add('A-01I-44', I, 'positive',
    r'\section{Geometric findings retained independently of convergence}',
    r'\section{Geometric findings}',
    'Section title rephrased positively; \\label unchanged; no register anchor quotes it.',
    [])

add('A-01I-45', I, 'caveat',
    r'This is a geometric proposition, not a blanket BFGS theorem. ',
    r'',
    'Says what the proposition is not; the section title already says these are geometric findings.',
    [R('C/01_I/prose/128', 'NON_CLAIM', 'reanchor', 'The item keeps only the pointer that followed the deleted remark.',
       anchor=r'\textbf{Proofs: Chapter~\ref{comp:A}.}'),
     R('C/01_I/prose/127', 'LEAN', 'keep', 'Preceding sentence; anchor and claim unchanged.')])

add('A-01I-46', I, 'positive',
    r'It neither assumes regularity of the certificate nor constructs one common BFGS history.',
    r'It requires no regularity of the certificate, and the incoming jumps need not belong to one BFGS history.',
    'Rewritten as the two generality facts it refers to (C/05_G/prose/047 and prose/026).',
    [R('C/01_I/prose/130', 'SAME_AS', 'reanchor', 'Same two facts (C/05_G/prose/047 no regularity; C/05_G/prose/026 predecessors need not belong to one BFGS history).',
       anchor=r'It requires no regularity of the certificate, and the incoming jumps need not belong to one BFGS history.'),
     R('C/01_I/prose/129', 'SAME_AS', 'keep', 'Preceding sentence; unchanged.')])

add('A-01I-47', I, 'positive',
    r'These distinctions are retained in Chapter~\ref{comp:G}.',
    r'\textbf{Proofs: Chapter~\ref{comp:G}.}',
    '"retained" framing replaced by the chapter\'s standard proof pointer.',
    [R('C/01_I/prose/132', 'NON_CLAIM', 'reanchor', 'Pointer to Chapter 5.',
       anchor=r'\textbf{Proofs: Chapter~\ref{comp:G}.}'),
     R('C/01_I/prose/131', 'SAME_AS', 'keep', 'Preceding sentence (scalar accumulating-kink examples); unchanged.')])

add('A-01I-48', I, 'guard',
    r'contain actual pinned Lean builds',
    r'contain pinned Lean builds',
    'Guard word "actual" removed.',
    [R('C/01_I/prose/133', 'NON_CLAIM', 'reanchor', 'Description of the verification records.',
       anchor=r'The delivered verification records contain pinned Lean builds, exact theorem contracts, module-wide declaration inventories and transitive axiom checks.')])

add('A-01I-49', I, 'caveat',
    r' Earlier claims about unprovided scripts, old execution counts, precisions and timings remain unsupported historical text in the original snapshot.',
    r'',
    'Disclaimer about the historical snapshot ("unsupported historical"); duplicates the clause deleted at line 9.',
    [R('C/01_I/prose/133', 'NON_CLAIM', 'keep', 'The reason\'s "and of unsupported historical text" becomes obsolete; anchor handled by A-01I-48.')])

add('A-01I-50', I, 'guard',
    r'the actual return-map derivative',
    r'the return-map derivative',
    'Guard word "actual" removed.',
    [R('C/01_I/prose/134', 'NON_CLAIM', 'reanchor', 'Description of the formalization.',
       anchor=r'The exact deterministic cycle, its smooth embedding, the return-map derivative and stable manifold, principal determinants, frame identities, geometric joining and infinite tail arguments have Lean proofs.')])

add('A-01I-51', I, 'caveat',
    r' Their logical roles are distinct.',
    r'',
    'Empty editorial hedge.',
    [R('C/01_I/prose/134', 'NON_CLAIM', 'keep', 'The reason\'s mention of "Their logical roles are distinct." becomes obsolete.')])

add('A-01I-52', I, 'positive',
    r'The blanket question is not answered by calling all semialgebraic functions safe: global failure already occurs for affine maxima.',
    r'Semialgebraicity alone does not prevent global failure: it already occurs for affine maxima.',
    'Rhetorical negative framing replaced by the sharpness statement it supports (N3 is semialgebraic).',
    [R('C/01_I/prose/143', 'LEAN', 'reanchor', 'Same content (n3_polyhedral_semialgebraic: not every finite convex semialgebraic function is safe).',
       anchor=r'Semialgebraicity alone does not prevent global failure: it already occurs for affine maxima.')])

add('A-01I-53', I, 'caveat',
    r' The planar and fixed-normal positive theorems have precise additional assumptions.',
    r'',
    'Hedge on the positive theorems; their assumptions are stated in P5 and P7.',
    [R('C/01_I/prose/144', 'NON_CLAIM', 'retire', 'No references found.'),
     R('C/01_I/prose/143', 'LEAN', 'keep', 'Preceding sentence; reanchored by A-01I-52, not by this proposal.')])

add('A-01I-54', I, 'caveat',
    r' The latest lower-curvature counterexamples likewise do not establish local failure in a finite analytic or semialgebraic description.',
    r'',
    'Says what N2 does not establish; N2\'s relation to the smooth strongly convex class is stated at line 107 (prose/029) and the question is in the open-gap list.',
    [R('C/01_I/prose/145', 'NON_CLAIM', 'retire',
       'Surviving statements: C/01_I/prose/029 (LEAN, constructed branches) and the open question C/01_I/prose/137. No references by id found (prose/029\'s note mentions prose/145 and should drop that comparison).'),
     R('C/01_I/prose/144', 'NON_CLAIM', 'retire', 'Preceding sentence; retired by A-01I-53 (listed here only because the validator names it).')])

add('A-01I-55', I, 'guard',
    r'Corollary of the later planar theorem; the implication and its Lean proof are operative.',
    r'Corollary of the later planar theorem; the implication has a Lean proof.',
    'Guard word "operative" removed.',
    [R('C/01_I/prose/149', 'SAME_AS', 'keep', 'Anchor "Original scalar-ridge convergence headline & Corollary of the later planar theorem" survives.')])

add('A-01I-56', I, 'caveat',
    r'Retain the distinct hypotheses; no unproved strict inclusion of function classes is asserted.',
    r'Retain the distinct hypotheses.',
    'Disclaimer repeated from P3, where it is kept once as an open question (A-01I-23).',
    [R('C/01_I/prose/153', 'NON_CLAIM', 'keep', 'Anchor survives; the disclaimer part of the reason becomes obsolete.')])

add('A-01I-57', I, 'positive',
    r'Keep the general obstruction and strongest nonnecessity example; do not label these as bad BFGS trajectories.',
    r'Keep the general obstruction and strongest nonnecessity example as results about certificates.',
    '"do not label these as bad BFGS trajectories" stated positively.',
    [R('C/01_I/prose/156', 'SAME_AS', 'keep', 'Anchor survives; the note quoting "Do not label these as bad BFGS trajectories" should quote "as results about certificates".')])

add('A-01I-58', I, 'caveat',
    r'The scope of the positive and negative programs is now substantially clearer, but neither gives a necessary-and-sufficient classification of nonsmooth full-BFGS convergence.',
    r'The scope of the positive and negative programs is now substantially clearer.',
    'Closing disclaimer dropped; sufficiency/nonnecessity is stated once (P1, scope point (d)).',
    [R('C/01_I/prose/157', 'NON_CLAIM', 'reanchor', 'Closing assessment.',
       anchor=r'The scope of the positive and negative programs is now substantially clearer.')])

add('A-01I-59', I, 'caveat',
    r', rather than certify publication priority.',
    r'.',
    'Priority disclaimer removed (as in the article).',
    [R('C/01_I/prose/159', 'NON_CLAIM', 'keep', 'Anchor (first sentence of the paragraph) unchanged.')])

add('A-01I-60', I, 'caveat',
    r' Such historical and comparative notes are separate from the mathematical assertions paired with Lean proofs.',
    r'',
    'Repeats the coordinator sentence that opens the section ("bibliographic scholarship, separate from the formal theorem assertions").',
    [R('C/01_I/prose/159', 'NON_CLAIM', 'keep', 'Anchor unchanged.')])

add('A-01I-61', I, 'caveat',
    r'; internal topic labels are not independently published sources.',
    r'.',
    'Disclaimer about the literature register removed.',
    [R('C/01_I/prose/159', 'NON_CLAIM', 'keep', 'Anchor unchanged.')])

add('A-01I-62', I, 'positive',
    r'The broader applications retain their own hypotheses and proofs.',
    r'The broader applications are proved here under their own hypotheses.',
    '"retain their own hypotheses and proofs" stated positively.',
    [R('C/01_I/prose/161', 'NON_CLAIM', 'reanchor', 'Scholarship remark.',
       anchor=r'The broader applications are proved here under their own hypotheses.'),
     R('C/01_I/prose/160', 'SAME_AS', 'keep', 'Preceding sentence (Guo--Lewis attribution); unchanged.')])

add('A-01I-63', I, 'caveat',
    r' The existence of a known special case does not identify the complete family theorem with that earlier result.',
    r'',
    'Defensive priority remark; the attribution of the known case is the first sentence.',
    [R('C/01_I/prose/161', 'NON_CLAIM', 'keep', 'Deleted sentence was part of this scholarship remark; anchor handled by A-01I-62.')])

add('A-01I-64', I, 'positive',
    r'A compact-level certificate theorem cannot replace these noncompact statements.',
    r'Unlike the compact-level certificate theorems, the results of this section need no compact sublevel.',
    '"Y cannot replace X" restated as the positive fact behind it (Lean: |v| has no compact sublevel, yet every run has value convergence).',
    [R('C/01_I/prose/110', 'LEAN', 'reanchor',
       'Same content (compact_theorem_cannot_replace: for F(u,v)=|v| no sublevel is compact, so compact-level theorems do not apply, while Theorem 7.A gives F(x_k) -> 0 and runs exist); stated positively.',
       anchor=r'Unlike the compact-level certificate theorems, the results of this section need no compact sublevel.'),
     R('C/01_I/prose/109', 'OPEN', 'keep', 'Preceding sentence; reanchored by A-01I-38, not by this proposal.')])

add('A-01I-65', I, 'positive',
    r'The single-hyperplane theorem is not a literal specialization: it allows differentiable but non-\(C^{1,1}\) exceptional points.',
    r'The single-hyperplane theorem, unlike the cluster theorem, allows differentiable but non-\(C^{1,1}\) exceptional points.',
    'The difference between the two theorems is kept, stated positively (11_U:151; Theorem 11.2 requires nondifferentiable interface points and C^{1,1} elsewhere).',
    [R('C/01_I/prose/097', 'SAME_AS', 'reanchor', 'Same comparison (C/11_U/prose/024).',
       anchor=r'The single-hyperplane theorem, unlike the cluster theorem, allows differentiable but non-\(C^{1,1}\) exceptional points.'),
     R('C/01_I/prose/096', 'SAME_AS', 'keep', 'Preceding sentence; unchanged.')])

# ---------------------------------------------------------------- 02_M
add('A-02M-01', M, 'caveat',
    r'No outside BFGS convergence theorem is substituted for this algebra. ',
    r'',
    'Defensive method remark; the chapter proves its algebra and the bibliographic notes give the classical sources.',
    [R('C/02_M/prose/003', 'NON_CLAIM', 'retire', 'Method non-claim; no references found.'),
     R('C/02_M/prose/002', 'NON_CLAIM', 'keep', 'Preceding sentence; unchanged.')])

add('A-02M-02', M, 'caveat',
    r'These conclusions do not say $H_k\to0$, $q_k\to0$ pointwise, or that eigenvectors converge. ',
    r'',
    'States what the theorems do not say; the article deleted the same sentence (E3).',
    [R('C/02_M/prose/012', 'NON_CLAIM', 'retire', 'Scope non-claim; no references found.')])

add('A-02M-03', M, 'positive',
    r'are retained alongside the strongest summable-budget asymptotic statement.',
    r'complement the strongest summable-budget asymptotic statement.',
    '"retained alongside" framing replaced by a positive statement; the comparisons are unchanged.',
    [R('C/02_M/prose/013', 'LEAN', 'reanchor',
       'Same comparisons (retained_comparison: d_k -> 0 weaker than summability; (M:superquad) the stronger asymptotic statement); "retained" was descriptive.',
       anchor=r'The finite-horizon bound and the weaker-assumption geometric-mean theorem complement the strongest summable-budget asymptotic statement.')])

add('A-02M-04', M, 'caveat',
    r'This last observation is an explicit consolidation deduction from the recorded energy and reciprocal results; no new regularity hypothesis is inferred.',
    r'This last observation is a consolidation deduction from the recorded energy and reciprocal results.',
    'Provenance kept; the "no new hypothesis is inferred" hedge and the guard "explicit" dropped (same edit as 01_I:317).',
    [R('C/02_M/prose/020', 'NON_CLAIM', 'reanchor', 'Provenance remark.',
       anchor=r'This last observation is a consolidation deduction from the recorded energy and reciprocal results.'),
     R('C/02_M/prose/019', 'LEAN', 'keep', 'Preceding sentence; anchor and claim unchanged.')])

add('A-02M-05', M, 'caveat',
    r'This is a trajectory criterion; one still has to derive its hypotheses from the objective.',
    r'This is a trajectory criterion.',
    'Hedge "one still has to derive" dropped; "trajectory criterion" already says its hypotheses are on the run.',
    [R('C/02_M/prose/024', 'NON_CLAIM', 'reanchor', 'Methodological remark.',
       anchor=r'This is a trajectory criterion.'),
     R('C/02_M/prose/023', 'LEAN', 'keep', 'Preceding sentence; anchor and claim unchanged.')])

add('A-02M-06', M, 'repeat',
    r' Neither $P_k$ nor $T_k$ is a BFGS matrix.',
    r'',
    'Scope point (c) (comparison objects are used only in the proofs), stated once in 01_I; the argument does not use it.',
    [R('C/02_M/prose/025', 'NON_CLAIM', 'retire', 'Clarification non-claim; no references found.'),
     R('C/02_M/prose/024', 'NON_CLAIM', 'keep', 'Preceding sentence; reanchored by A-02M-05, not by this proposal.')])

add('A-02M-07', M, 'caveat',
    r' No strict inclusion of all existential objective-certificate classes is claimed.',
    r'',
    'Disclaimer; 01_I (P3) states the question once as an open question.',
    [R('C/02_M/prose/028', 'NON_CLAIM', 'retire', 'Survives as the open question in C/01_I/prose/057 (A-01I-23). No references found.'),
     R('C/02_M/prose/027', 'LEAN', 'keep', 'Preceding sentence; anchor and claim unchanged.')])

add('A-02M-08', M, 'positive',
    r'The complete adjacent-degree principal-minor inequality is distinguished from it; the literature audit found no exact match, without establishing publication priority.',
    r'The complete adjacent-degree principal-minor inequality extends it; the literature audit found no exact match.',
    'Priority disclaimer dropped; "is distinguished from it" stated positively (the j=n case of the hierarchy is the determinant identity, proof of M:hierarchy).',
    [R('C/02_M/prose/033', 'NON_CLAIM', 'reanchor', 'Literature comparison; no priority statement remains.',
       anchor=r'The complete adjacent-degree principal-minor inequality extends it'),
     R('C/02_M/prose/032', 'NON_CLAIM', 'keep', 'Preceding sentence; unchanged.')])

add('A-02M-09', M, 'guard',
    r'Here the actual principal-minor hierarchy supplies',
    r'Here the principal-minor hierarchy supplies',
    'Guard word "actual" removed.',
    [R('C/02_M/prose/037', 'SAME_AS', 'reanchor', 'Same summary.',
       anchor=r'Here the principal-minor hierarchy supplies reciprocal bounds for $q_k=g_k^TH_kg_k$'),
     R('C/02_M/prose/036', 'NON_CLAIM', 'keep', 'Preceding sentence; unchanged.')])

add('A-02M-10', M, 'positive',
    r'Their use in a moving-frame criterion still requires the separately stated visibility, secant and transport hypotheses.',
    r'The moving-frame criterion combines them with the visibility, secant and transport hypotheses.',
    '"still requires" hedge restated positively.',
    [R('C/02_M/prose/040', 'NON_CLAIM', 'reanchor', 'Remark on the hypotheses of frame_criterion.',
       anchor=r'The moving-frame criterion combines them with the visibility, secant and transport hypotheses.'),
     R('C/02_M/prose/039', 'SAME_AS', 'keep', 'Preceding sentence; unchanged.')])

# ---------------------------------------------------------------- checks
texts = {f: (REPO / f).read_text() for f in (I, M)}
bad = 0
for p in P:
    c = texts[p['file']].count(p['old'])
    if c != 1:
        print('COUNT', p['id'], c)
        bad += 1
out = Path('/tmp/opencode/m44/companion/proposals_A.json')
out.write_text(json.dumps({'group': 'A', 'proposals': P}, ensure_ascii=False, indent=1) + '\n')
print(len(P), 'proposals written,', bad, 'count problems')
