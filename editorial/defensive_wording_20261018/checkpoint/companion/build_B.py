#!/usr/bin/env python3
"""Build proposals_B.json (group B: 03_T, 04_R, 08_A). Writes only under /tmp/opencode/m44/companion."""
import json
from pathlib import Path

REPO = Path('/home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth')
OUT = Path('/tmp/opencode/m44/companion/proposals_B.json')

T = 'companion/chapters/03_T.tex'
R = 'companion/chapters/04_R.tex'
A = 'companion/chapters/08_A.tex'


def reg(item, status, action, note='', anchor=None):
    r = {'item': item, 'status': status, 'action': action}
    if anchor is not None:
        r['anchor'] = anchor
    if note:
        r['note'] = note
    return r


P = []


def prop(pid, file, kind, old, new, reason, register):
    P.append({'id': pid, 'file': file, 'kind': kind, 'old': old, 'new': new,
              'reason': reason, 'register': register})


# ---------------------------------------------------------------- 03_T
prop('B-03T-01', T, 'caveat',
     'Eligibility does not assert compatibility of an arbitrary chain with BFGS; imposing a condition on all such pairs is an objective-only sufficient assumption.',
     'Imposing a condition on all eligible pairs is an assumption on the objective alone.',
     'Drops the clause saying what eligibility does not assert and keeps the positive point, worded as in the revised article ("is an assumption on the objective alone").',
     [reg('C/03_T/prose/008', 'NON_CLAIM', 'retire',
          'The disclaimer clause is deleted; no references to the item in the registers or BfgsArticle.'),
      reg('C/03_T/prose/044', 'SAME_AS', 'reanchor',
          'Same content (conditions of theorem/001 are imposed on all eligible pairs, defined from F and the constants alone); "sufficient" dropped as in the article.',
          anchor='Imposing a condition on all eligible pairs is an assumption on the objective alone.'),
      reg('C/03_T/prose/007', 'LEAN', 'keep', 'Preceding sentence unchanged.')])

prop('B-03T-02', T, 'positive',
     'objective-pair data, not $H_k$.',
     'objective-pair data.',
     'States X ("objective-pair data") without the "not $H_k$" contrast; that the fields are objective data used only in the proof is scope point (c) of Chapter 1.',
     [reg('C/03_T/prose/009', 'SAME_AS', 'reanchor', 'Clarification of theorem/001 unchanged.',
          anchor='All matrices in the next assumption are objective-pair data.')])

prop('B-03T-03', T, 'positive',
     "; it is not necessary to the formal principal theorem's contradiction",
     '',
     'The preceding sentences already say which bound the formal theorem uses; the trailing "it is not Y" clause is dropped.',
     [reg('C/03_T/prose/021', 'LEAN', 'keep',
          'Anchor survives; the item note mentions the deleted clause ("describes the Lean development") and can drop that remark.')])

prop('B-03T-04', T, 'guard',
     r'\section{Why this is genuinely weaker than RS}',
     r'\section{Why this is strictly weaker than RS}',
     'Section title: "genuinely" is a guard word; "strictly" states the proved strict inclusion that the section establishes.',
     [])

prop('B-03T-05', T, 'positive',
     'This is strict inclusion of sufficient conditions, not merely a new notation for the old inequality.',
     'The inclusion of RS in the new condition is therefore strict.',
     'Sharpness result kept as a positive statement; the "not merely a new notation" contrast is dropped.',
     [reg('C/03_T/prose/033', 'SAME_AS', 'reanchor',
          'Same content: inclusion (prose/031) plus failure of the reverse inclusion (prose/032).',
          anchor='The inclusion of RS in the new condition is therefore strict.'),
      reg('C/03_T/prose/032', 'LEAN', 'keep', 'Preceding sentences (reverse implication fails; Chapter Q fields) unchanged.')])

prop('B-03T-06', T, 'guard',
     'are precisely what make the new hypothesis sufficient',
     'make the new hypothesis sufficient',
     '"precisely" is emphasis only.',
     [reg('C/03_T/prose/036', 'SAME_AS', 'reanchor', 'Summary of the proof mechanism unchanged.',
          anchor=r'Projection and the multiplicative budget make the new hypothesis sufficient without assumptions on $B_k$.')])

# ---------------------------------------------------------------- 04_R
prop('B-04R-01', R, 'repeat',
     ' General all-ray existence of differentiable acceptable points is not asserted.',
     '',
     'Scope point (a) (run existence is a hypothesis), stated in Chapter 1; repeated here only as a hedge.',
     [reg('C/04_R/prose/009', 'NON_CLAIM', 'retire',
          'Disclaimer deleted; no references to the item in the registers or BfgsArticle.'),
      reg('C/04_R/prose/008', 'DEFINITION', 'keep', 'The run convention ("Every run" ...) is unchanged.')])

prop('B-04R-02', R, 'caveat',
     "The label ``inward radial smoothness'' is descriptive terminology in this chapter, not a claim of a standardized definition or of novelty for the terminology. ",
     '',
     'The sentence only disclaims standardization and novelty of a name; the theorem title already introduces the label.',
     [reg('C/04_R/prose/010', 'NON_CLAIM', 'retire',
          'Terminology/novelty disclaimer deleted (W8 had only changed "note" to "chapter"); no references to the item.')])

prop('B-04R-03', R, 'guard',
     r'is \emph{not enough}:',
     'is not enough:',
     'Emphasis on a negative statement; the warning itself (a.e. checking misses radial jumps) is kept.',
     [reg('C/04_R/prose/017', 'SAME_AS', 'keep', 'Anchor ("For a nonsmooth function, checking this expression almost everywhere is") survives.')])

prop('B-04R-04', R, 'caveat',
     ' The square root of $T$ is not being asserted to be a metric.',
     '',
     'Says only what is not asserted.',
     [reg('C/04_R/prose/026', 'NON_CLAIM', 'retire', 'Disclaimer deleted; no references to the item.'),
      reg('C/04_R/prose/025', 'LEAN', 'keep', 'Preceding sentence unchanged.')])

prop('B-04R-05', R, 'caveat',
     ' without changing their compact-basin hypotheses',
     '',
     'The clause only says the hypotheses are not relaxed; the preceding sentence (the constant function F=1) already shows why compactness matters.',
     [reg('C/04_R/prose/040', 'NON_CLAIM', 'keep',
          'Anchor ("These identities explain the breadth of the sufficient classes of Section~4.6") survives.')])

prop('B-04R-06', R, 'positive',
     ', not an identification of an unspecified earlier objective',
     '',
     '"X, not Y": keeps the provenance fact (explicit reconstruction for this edition) and drops the contrast.',
     [reg('C/04_R/prose/041', 'NON_CLAIM', 'keep',
          'Anchor ("This definition is an explicit reconstruction for this edition") survives.')])

prop('B-04R-07', R, 'guard',
     'This objective has an actual infinite unmodified full-BFGS failure run.',
     'This objective has an infinite unmodified full-BFGS failure run.',
     '"actual" is a guard word (the article now writes "explicit"/nothing).',
     [reg('C/04_R/prose/047', 'LEAN', 'reanchor', 'Mathematical content unchanged.',
          anchor='This objective has an infinite unmodified full-BFGS failure run.')])

prop('B-04R-08', R, 'guard',
     'The gradients are the actual derivatives of $F_R$ at the accepted points',
     r'The vectors $\widehat g_k$ are the gradients of $F_R$ at the accepted points',
     'Removes the guard word "actual"; names the vectors so the sentence is not circular. Content as in the Lean note ("Every g^_k is the gradient of F_R at x^_k").',
     [reg('C/04_R/prose/048', 'LEAN', 'reanchor', 'Mathematical content unchanged. (The validator lists C/04_R/prose/047 as the preceding claim; it is re-anchored by B-04R-07.)',
          anchor=r'The vectors $\widehat g_k$ are the gradients of $F_R$ at the accepted points')])

prop('B-04R-09', R, 'positive',
     'This proves a transformed full-BFGS run, rather than prescribing an unrelated sequence of endpoint pairs.',
     'Thus the transformed data form a full-BFGS run on $F_R$.',
     '"X rather than Y" rewritten as X, matching the Lean statement (the transformed data are an admissible run on F_R).',
     [reg('C/04_R/prose/051', 'LEAN', 'reanchor', 'Mathematical content unchanged.',
          anchor='Thus the transformed data form a full-BFGS run on $F_R$.'),
      reg('C/04_R/prose/050', 'LEAN', 'keep', 'Preceding sentence unchanged ("predicted and actual" is the mathematical contrast, kept).')])

prop('B-04R-10', R, 'guard',
     'In every three phases the actual supporting errors repeat',
     'In every three phases the supporting errors at the iterates repeat',
     '"actual" is a guard word; "at the iterates" says what it pointed to (b_{F_R} at the run\'s points, as opposed to the branch errors at the optimizer).',
     [reg('C/04_R/prose/053', 'LEAN', 'reanchor', 'Mathematical content unchanged.',
          anchor='In every three phases the supporting errors at the iterates repeat $0,0,25/4$.'),
      reg('C/04_R/prose/052', 'LEAN', 'keep', 'Preceding sentence unchanged.')])

prop('B-04R-11', R, 'guard',
     'The actual positive secant curvatures are',
     'The positive secant curvatures are',
     '"actual" is a guard word.',
     [reg('C/04_R/prose/054', 'LEAN', 'reanchor', 'Mathematical content unchanged. (The validator lists C/04_R/prose/053 as the preceding claim; it is re-anchored by B-04R-10.)',
          anchor=r'The positive secant curvatures are $a$ times those of the run of Chapter~\ref{comp:D} and tend to zero.')])

prop('B-04R-12', R, 'guard',
     'fail on this actual initial sublevel',
     'fail on this initial sublevel',
     '"actual" is a guard word.',
     [reg('C/04_R/prose/056', 'LEAN', 'reanchor', 'Mathematical content unchanged.',
          anchor='Thus (SP), and by the compact-domain equivalence also (RS), fail on this initial sublevel.')])

prop('B-04R-13', R, 'caveat',
     ' Convexity of the full objective remains essential.',
     '',
     'Restates a hypothesis of Theorem 4.5.1 (and of "finite convex piecewise linear-quadratic" in the same paragraph) as an unproved necessity qualifier.',
     [reg('C/04_R/prose/061', 'NON_CLAIM', 'retire',
          'Emphasis on a hypothesis that the theorem states; no counterexample was asserted; no references to the item.'),
      reg('C/04_R/prose/060', 'LEAN', 'keep', 'Preceding sentence unchanged.')])

prop('B-04R-14', R, 'positive',
     'need not have a polyhedral partition and is not automatically included.',
     r'need not have a polyhedral partition; Chapters~\ref{comp:C} and~\ref{comp:Q} treat planar maxima of this kind.',
     'Keeps the fact (no polyhedral partition) and replaces "is not automatically included" by a pointer to where such maxima are treated, as the revised article does ("are treated in the plane below").',
     [reg('C/04_R/prose/062', 'SAME_AS', 'keep',
          'Anchor ("A finite maximum of arbitrary convex quadratics need not have a polyhedral partition") survives; the added clause is a cross-reference (Chapter C: explicit three-quadratic basin and planar smooth maxima; Chapter Q: parabolic maxima max{a_i u^2+b_i v}). The article counterpart A/local/prose/010 was rewritten the same way.')])

prop('B-04R-15', R, 'caveat',
     ' Local statements are not global arbitrary-initialization statements.',
     '',
     'Says only what local statements are not; the first sentence of the paragraph keeps the hypotheses.',
     [reg('C/04_R/prose/063', 'NON_CLAIM', 'keep', 'Anchor (first sentence) survives.')])

prop('B-04R-16', R, 'positive',
     'This does not imply that every spectral penalty is smooth near every nonzero residual.',
     'Spectral penalties, by contrast, can be nonsmooth near a nonzero residual.',
     '"This does not imply ..." restated positively as the property it records (proved in Lean: the nuclear norm is not differentiable at diag(1,0)).',
     [reg('C/04_R/prose/076', 'LEAN', 'reanchor',
          'Same existential content (some spectral penalty is nonsmooth near a nonzero residual; witness nuclear_not_smooth).',
          anchor='Spectral penalties, by contrast, can be nonsmooth near a nonzero residual.'),
      reg('C/04_R/prose/075', 'LEAN', 'keep', 'Preceding sentence unchanged.')])

prop('B-04R-17', R, 'guard',
     'also clear on genuine active ties',
     'also clear on active ties',
     '"genuine" is a guard word.',
     [reg('C/04_R/prose/080', 'LEAN', 'reanchor', 'Mathematical content unchanged.',
          anchor='The necessity for (RS) is also clear on active ties')])

prop('B-04R-18', R, 'repeat',
     ' It is not a necessary condition for BFGS convergence itself.',
     '',
     'Scope point (d) (sufficient, not necessary; nonnecessity examples in Chapter G), stated in Chapter 1; the chapter\'s argument does not use it.',
     [reg('C/04_R/prose/082', 'SAME_AS', 'retire',
          'Nonnecessity is carried by A/local/theorem/art:nonradial-example (and Chapter Q, Chapter 1); no references to the item.'),
      reg('C/04_R/prose/081', 'LEAN', 'keep', 'Preceding sentence unchanged.')])

prop('B-04R-19', R, 'guard',
     'A ray crosses a genuine one-dimensional kink there.',
     'A ray crosses a one-dimensional kink there.',
     '"genuine" is a guard word.',
     [reg('C/04_R/prose/085', 'LEAN', 'reanchor', 'Mathematical content unchanged.',
          anchor='A ray crosses a one-dimensional kink there.'),
      reg('C/04_R/prose/084', 'LEAN', 'keep', 'Preceding sentence unchanged.')])

prop('B-04R-20', R, 'caveat',
     r' It is \emph{not} a nonconvergent BFGS trajectory and does not establish failure of BFGS.',
     '',
     'Says only what the example does not establish (with bold-like emphasis on "not").',
     [reg('C/04_R/prose/087', 'NON_CLAIM', 'retire',
          'Disclaimer deleted; no references to the item. (Its reason records that every admissible run on this objective converges, ParabolicRadialBoundary.converges_without_radial_secant; see the final report for an optional positive cross-reference.)'),
      reg('C/04_R/prose/086', 'LEAN', 'keep', 'Preceding sentence unchanged.')])

prop('B-04R-21', R, 'caveat',
     ' No failure of BFGS on this spectral problem is being claimed.',
     '',
     'Says only what is not claimed.',
     [reg('C/04_R/prose/097', 'NON_CLAIM', 'retire', 'Disclaimer deleted; no references to the item.'),
      reg('C/04_R/prose/096', 'LEAN', 'keep', 'Preceding sentence unchanged.')])

prop('B-04R-22', R, 'positive',
     '; no new divergence construction is asserted',
     '',
     'Defensive prior-work clause; the attribution to [BB] in the previous sentence stays.',
     [reg('C/04_R/prose/101', 'NON_CLAIM', 'retire', 'Disclaimer deleted; no references to the item.'),
      reg('C/04_R/prose/100', 'SAME_AS', 'keep', 'Anchor ("Only its supporting endpoint must be differentiable") survives.')])

prop('B-04R-23', R, 'positive',
     'That standard calculation is separate from the rotated-pair obstruction to the radial condition established in this chapter; the obstruction makes no claim of BFGS failure.',
     'The rotated-pair obstruction to the radial condition is established in this chapter.',
     '"X is separate from Y" plus a no-claim clause rewritten as a positive provenance statement; the attribution to [CCS10] in the previous sentence stays.',
     [reg('C/04_R/prose/107', 'NON_CLAIM', 'reanchor', 'Provenance remark, positive form.',
          anchor='The rotated-pair obstruction to the radial condition is established in this chapter.'),
      reg('C/04_R/prose/106', 'LEAN', 'keep', 'Anchor (previous sentence) survives.')])

# ---------------------------------------------------------------- 08_A
prop('B-08A-01', A, 'caveat',
     r'is now proved only in the completed settings of Chapters~\ref{comp:C} and~\ref{comp:U}; no blanket theorem for all finite smooth maxima is asserted.',
     r'is now proved in the settings of Chapters~\ref{comp:C} and~\ref{comp:U}.',
     'Drops "only" and the "no blanket theorem is asserted" clause; the general case is the open conjecture of Section 8.5, which is kept.',
     [reg('C/08_A/prose/005', 'SAME_AS', 'reanchor',
          'Same targets (C:thm:cluster, art:planar-cluster, Chapter U Theorem 11.2); the note\'s remark on "only" and the clause can go.',
          anchor='The originally proposed dynamical step is now proved in the settings of Chapters')])

prop('B-08A-02', A, 'positive',
     'This is a geometric rank-loss example, not a BFGS counterexample.',
     'This is a geometric rank-loss example.',
     '"X, not Y" reduced to X; the next sentence (rank-loss point excluded near the optimizer) answers the natural question.',
     [reg('C/08_A/prose/024', 'NON_CLAIM', 'reanchor', 'Classification of the example, positive form.',
          anchor='This is a geometric rank-loss example.')])

prop('B-08A-03', A, 'guard',
     'neighborhood of its actual optimizer',
     'neighborhood of its optimizer',
     '"actual" is a guard word; the example has one optimizer.',
     [reg('C/08_A/prose/025', 'LEAN', 'reanchor', 'Mathematical content unchanged.',
          anchor='A sufficiently small neighborhood of its optimizer excludes the rank-loss point.')])

prop('B-08A-04', A, 'caveat',
     ' It is not itself a BFGS convergence theorem.',
     '',
     'Says only what the argument is not.',
     [reg('C/08_A/prose/027', 'NON_CLAIM', 'keep',
          'Anchor ("This is the source note\'s barycentric-stability argument") survives; its reason mentions "not a BFGS convergence theorem" and can drop that part.')])

prop('B-08A-05', A, 'positive',
     'This establishes visibility, not the full transport needed in arbitrary dimension.',
     r'This establishes the visibility condition of Chapter~\ref{comp:T}.',
     '"X, not Y" reduced to X; names the condition as the Lean note does (gap_gives_visibility: condition (V) of Chapter T; "(V)" is not printed to avoid a clash with this chapter\'s V(p)). The open arbitrary-dimensional case stays in Section 8.5.',
     [reg('C/08_A/prose/032', 'LEAN', 'reanchor',
          'Same content (gamma >= gamma_0 > 0 gives (V) for W = a a^T); the note\'s remark on the caveat clause can go.',
          anchor=r'This establishes the visibility condition of Chapter~\ref{comp:T}.'),
      reg('C/08_A/prose/031', 'LEAN', 'keep', 'Preceding sentence unchanged.')])

prop('B-08A-06', A, 'guard',
     r'the actual composition $F\circ p$',
     r'the composition $F\circ p$',
     '"actual" is a guard word; inside the proof of Proposition A:semialgebraic, argument unchanged.',
     [reg('C/08_A/proof/002', 'PROOF', 'keep', 'Edit inside the proof of Proposition A:semialgebraic: one guard word removed, argument unchanged; the proof hash changes and needs re-acceptance.')])

prop('B-08A-07', A, 'positive',
     ' rather than unproved premises',
     '',
     '"X rather than Y": the first clause already says the facts are established; the references supply context.',
     [reg('C/08_A/prose/034', 'NON_CLAIM', 'keep',
          'Anchor ("The geometric facts used above are established by real-polynomial projection") survives.')])

prop('B-08A-08', A, 'guard',
     'finitely many actual semialgebraic path classes',
     'finitely many semialgebraic path classes',
     '"actual" is a guard word.',
     [reg('C/08_A/prose/035', 'LEAN', 'reanchor', 'Mathematical content unchanged.',
          anchor='The affine-critical set also has finitely many semialgebraic path classes')])

prop('B-08A-09', A, 'guard',
     'its actual composition with $F$',
     'its composition with $F$',
     '"actual" is a guard word.',
     [reg('C/08_A/prose/036', 'LEAN', 'keep', 'Anchor survives; content unchanged.')])

prop('B-08A-10', A, 'caveat',
     '; their identification with path classes is not needed here',
     '',
     'Says only what is not needed/claimed.',
     [reg('C/08_A/prose/038', 'LEAN', 'keep',
          'Anchor ("Ordinary topological connected components are separately finite and semialgebraic, with constant objective value") survives.')])

prop('B-08A-11', A, 'caveat',
     r'It does not imply local BFGS convergence without a dynamical theorem forcing an affine-critical cluster point. Chapters~\ref{comp:C} and~\ref{comp:U} provide such theorems under their respective additional hypotheses.',
     r'Chapters~\ref{comp:C} and~\ref{comp:U} provide dynamical theorems forcing an affine-critical cluster point under their respective additional hypotheses.',
     'Deletes the "does not imply" sentence and states positively what Chapters C and U provide (the antecedent of "such theorems" moves into the sentence).',
     [reg('C/08_A/prose/040', 'NON_CLAIM', 'retire', 'Scope remark deleted; no references to the item.'),
      reg('C/08_A/prose/041', 'SAME_AS', 'reanchor', 'Same targets (C:thm:cluster, art:planar-cluster, Chapter U Theorem 11.2).',
          anchor='provide dynamical theorems forcing an affine-critical cluster point under their respective additional hypotheses'),
      reg('C/08_A/prose/039', 'LEAN', 'keep', 'Preceding sentence unchanged.')])

prop('B-08A-12', A, 'positive',
     'Neither establishes this full conjecture.',
     'The full conjecture remains open.',
     'Open question kept, phrased plainly instead of the "neither establishes" framing.',
     [reg('C/08_A/prose/044', 'NON_CLAIM', 'reanchor', 'Status of the open problem prose/042, plain form.',
          anchor='The full conjecture remains open.'),
      reg('C/08_A/prose/043', 'SAME_AS', 'keep', 'Preceding sentence unchanged.')])

prop('B-08A-13', A, 'positive',
     '; the general rank-loss mechanism is not claimed as new',
     '',
     'Defensive prior-work clause; the attribution to Liu--Sagastizabal--Solodov in the previous sentence stays.',
     [reg('C/08_A/prose/050', 'SAME_AS', 'keep',
          'Anchor survives; the note\'s remark on the priority disclaimer can go.')])


def main():
    texts = {f: (REPO / f).read_text() for f in (T, R, A)}
    for p in P:
        n = texts[p['file']].count(p['old'])
        assert n == 1, (p['id'], n)
    OUT.write_text(json.dumps({'group': 'B', 'proposals': P}, indent=1, ensure_ascii=False) + '\n')
    print(len(P), 'proposals written to', OUT)


if __name__ == '__main__':
    main()
