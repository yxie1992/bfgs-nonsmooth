#!/usr/bin/env python3
"""M44, 18 October 2026: remove defensive and over-qualifying sentences from the article.

Each edit replaces the unique whitespace-normalized occurrence of OLD in FILE by NEW
(edits of one file apply in order). Nothing is written unless every OLD occurs exactly
once. Also writes the edit list to /tmp/opencode/m44/article_edits.json.

Kinds: caveat = a sentence that only says what a result does not claim; repeat = a scope
point now stated once elsewhere (proof devices: introduction, I7; run existence:
geometry.tex, G12; deterministic starts versus almost-sure: Section 7, V2b); guard = a
guard word ("actual", "genuine") or a figure/table disclaimer; positive = rewritten as a
positive statement.

Kept on purpose: every theorem-like statement (paper/statements/ and all environments);
explanations that answer a natural question (why the counterexamples evade the positive
hypotheses, verification.tex; the polyhedral failure versus the local theorem,
failure.tex "This already excludes global convergence ..."); generality remarks ("This
asks nothing about transverse smoothness", "The algorithm need not identify a cell or a
manifold", "Neither continuity, uniform boundedness nor positive definiteness of W_eta is
required", "The resulting objective-level conditions require neither iterate convergence
nor prescribed spectral behavior"); the open question "The local question for finitely
many uniformly strongly convex $C^2$ branches remains open here ..." (article OPEN item).
No edit in matrix_algebra.tex or paper/statements/.
"""
import json, re, sys
from pathlib import Path

ROOT = Path('/home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth')
INTRO = 'paper/sections/introduction.tex'
GEOM = 'paper/sections/geometry.tex'
ENERGY = 'paper/sections/energy.tex'
GLOBAL = 'paper/sections/global.tex'
LOCAL = 'paper/sections/local.tex'
VERIF = 'paper/sections/verification.tex'
FAIL = 'paper/sections/failure.tex'
HYP = 'paper/appendices/hypothesis_examples.tex'
LOWER = 'paper/appendices/lower_curvature.tex'
PLANAR = 'paper/appendices/planar_geometry.tex'
SEED = 'paper/appendices/seed_certificate.tex'

EDITS = [
 ('A1', 'paper/master.tex', 'guard',
  r'''for finite convex objectives with Armijo--weak-Wolfe steps and actual gradients at differentiable accepted iterates.''',
  r'''for finite convex objectives with Armijo--weak-Wolfe steps and gradients at
differentiable accepted iterates.'''),
 ('A2', 'paper/master.tex', 'guard',
  r'''adjacent-degree hierarchy for actual principal minors of full-BFGS matrices,''',
  r'''adjacent-degree hierarchy for the principal minors of full-BFGS matrices,'''),

 ('I1', INTRO, 'repeat',
  r'''objectives. Successful termination is allowed; infinite runs are analyzed under the differentiable-iterate convention made precise below.''',
  r'''objectives.'''),
 ('I2', INTRO, 'caveat',
  r'''family theorem rather than a special planar recurrence.''',
  r'''family theorem.'''),
 ('I3', INTRO, 'caveat',
  r'''many iterations~\preprintcite*[Theorem IV.1]{XW}; the value-convergence theorem for a broader homogeneous family in Chapter~7 of the complete companion (introduced at the end of this section) does not replace that finite escape result.''',
  r'''many iterations~\preprintcite*[Theorem IV.1]{XW}.'''),
 ('I4', INTRO, 'caveat',
  r'''Our positive results instead derive convergence from objective hypotheses within the convex families stated here; they do not subsume his potentially nonconvex selection setting.''',
  r'''Our positive results instead derive
convergence from hypotheses on the objective.'''),
 ('I5', INTRO, 'repeat',
  r'''The positive theorems concern every infinite such run. They do not assert that every search ray contains an acceptable differentiable point.''',
  r'''The positive theorems concern every infinite
such run.'''),
 ('I6', INTRO, 'repeat',
  r'''guarantees under either regularity regime. They establish no positive-measure failure set and do not refute the almost-sure semialgebraic challenge.''',
  r'''guarantees under either regularity regime.'''),
 ('I7', INTRO, 'positive',
  r'''The field is an analytical device, not part of the algorithm.''',
  r'''The field, like every
comparison object in the paper, is used only in the proofs.'''),
 ('I8', INTRO, 'caveat',
  r'''Our conditions are sufficient; they do not classify every successful run. Sections~\ref{art:geometry}''',
  r'''Sections~\ref{art:geometry}'''),
 ('I9', INTRO, 'positive',
  r'''The article includes the essential proofs of these claims.''',
  r'''The article contains complete proofs of these results.'''),

 ('G1', GEOM, 'repeat',
  r'''uses this property to prove convergence of the whole sequence. The inward segment is a comparison used in the proof; it is not a direction BFGS is assumed to take. No eventual eigenvector or eigenvalue description is needed.''',
  r'''uses this property to prove convergence of the whole sequence, without any
description of the eventual eigenvalues or eigenvectors of the matrices.'''),
 ('G2', GEOM, 'guard',
  r'''excludes zero, but its affine hull is the plane. The vertices on the right are rendered from the certified root's rational center; the mathematical definition uses the isolated root. Zero lies just above''',
  r'''excludes zero, but its affine hull is the plane.
Zero lies just above'''),
 ('G3', GEOM, 'guard',
  r'''Solid arrows indicate gradients and the dashed arrow a common descent direction; none is a BFGS step.}''',
  r'''Solid arrows indicate gradients and the dashed arrow a common descent
direction.}'''),
 ('G4', GEOM, 'guard',
  r'''asks a different question: can a genuine full-BFGS run contract around a point where descent still exists? The bad corner is specific. Its slopes are''',
  r'''asks a different question: can a full-BFGS run
contract around a point where descent still exists? The slopes of the bad corner
are'''),
 ('G5', GEOM, 'caveat',
  r'''convex hull. These are elementary separation facts, not a classification of BFGS behavior.''',
  r'''convex hull.'''),
 ('G6', GEOM, 'repeat',
  r'''proofs. In every row the quantifier is over infinite admissible runs with arbitrary positive-definite initialization. An admissible run uses actual gradients and satisfies Armijo--weak-Wolfe at its accepted points; the definition does not assert that an arbitrary line-search implementation always finds such points.''',
  r'''proofs. In every row the guarantee covers every infinite admissible run, with
arbitrary positive-definite initialization.'''),
 ('G7', GEOM, 'repeat',
  r'''row gives global convergence. The results concern admissible runs, without a presumed matrix limit.}''',
  r'''row gives global convergence.}'''),
 ('G8', GEOM, 'positive',
  r'''The first two rows make precise global assertions; they do not claim global convergence for every affine maximum. Indeed, the coercive polyhedral realization of the wrong corner in Corollary~\ref{art:failure_polyhedral} has a positive limiting objective gap.''',
  r'''Homogeneity cannot be dropped from the second row: the coercive polyhedral
realization of the wrong corner in Corollary~\ref{art:failure_polyhedral},
a maximum of four affine functions, has a positive limiting objective gap.'''),
 ('G9', GEOM, 'caveat',
  r'''proves convergence. These are complementary sufficient mechanisms and specific realized failures, rather than a classification by jump span.''',
  r'''proves convergence.'''),
 ('G10', GEOM, 'guard',
  r'''For the centered route one must locate an actual minimizer and''',
  r'''For the centered route one must locate a minimizer and'''),
 ('G11', GEOM, 'guard',
  r'''verifies these conditions jointly with actual full-BFGS histories.''',
  r'''verifies these conditions jointly with
explicit full-BFGS histories.'''),
 ('G12', GEOM, 'positive',
  r'''constant pair (Corollary~\ref{art:examples-nonradial-runs}). The qualification on run existence is essential: Proposition~\ref{art:examples-no-step} gives a coercive homogeneous objective and initial data for which no differentiable weak-Wolfe first step exists. These are sufficient classes with explicit witnesses, not a genericity or necessity claim for nonsmooth BFGS.''',
  r'''constant pair (Corollary~\ref{art:examples-nonradial-runs}).
Proposition~\ref{art:examples-no-step} shows why the theorems quantify over
runs: it gives a coercive homogeneous objective and initial data for which no
differentiable weak-Wolfe first step exists.'''),

 ('E1', ENERGY, 'repeat',
  r'''These are the usual actual-gradient, full-BFGS conventions \cite{LO}; see also \preprintcite{XW}. A zero gradient is successful termination. Statements about admissible runs do not assert that a differentiable acceptable point exists on every ray, or that every implementation finds one.''',
  r'''These are the usual full-BFGS conventions
\cite{LO}; see also \preprintcite{XW}.
A zero gradient is successful termination.'''),
 ('E2', ENERGY, 'guard',
  r'''\end{equation} This recurrence is derived for the run's principal determinants.''',
  r'''\end{equation}'''),
 ('E3', ENERGY, 'caveat',
  r'''and the stronger reciprocal-sum consequence under summability are retained in the companion's Chapter~2; the qualitative conclusion above is sufficient for the article. Neither limit in \eqref{art:reciprocal-limits} asserts that $q_k\to0$ pointwise or that $H_k$ converges.''',
  r'''and the stronger reciprocal-sum consequence under summability are developed
in the companion's Chapter~2.'''),
 ('E4', ENERGY, 'repeat',
  r'''A positive-semidefinite field packages one or several comparison directions. It is constructed from the objective for the analysis; BFGS neither evaluates it nor changes its step in response to it. The rank-one''',
  r'''A positive-semidefinite field, built from the objective, packages one or
several comparison directions. The rank-one'''),
 ('E5', ENERGY, 'caveat',
  r'''is an objective assumption; it does not assert that an arbitrary sequence of eligible pairs can be realized by BFGS. Put''',
  r'''is an assumption on the objective alone. Put'''),
 ('E6', ENERGY, 'caveat',
  r'''The companion's scalar convergence and certificate-nonexistence results show that the certificate is not necessary for successful BFGS behavior. The planar application below shows a different point: moving geometry can prove convergence where the fixed radial field fails.''',
  r'''The planar application below shows that moving geometry can prove
convergence where the fixed radial field fails.'''),

 ('GL1', GLOBAL, 'repeat',
  r'''accurate on short inward segments. This asks nothing about transverse smoothness, and it does not require BFGS to take radial steps. The comparison segments are an analytical device; the actual steps remain those in \eqref{art:update}.''',
  r'''accurate on short inward segments. This asks nothing about transverse
smoothness.'''),
 ('GL2', GLOBAL, 'positive',
  r'''includes such jumps. The condition is sufficient; Theorem~\ref{art:nonradial-example} will exhibit convergence where''',
  r'''includes such jumps. Theorem~\ref{art:nonradial-example} goes further: it
exhibits convergence where'''),
 ('GL3', GLOBAL, 'repeat',
  r'''the homogeneous part is centered at a minimizer of the sum. Centering is a geometric hypothesis on the objective, not knowledge required by the algorithm. Moreover, the two summands need not separately be minimized at that center.''',
  r'''the homogeneous part is centered at a minimizer of the sum.'''),
 ('GL4', GLOBAL, 'caveat',
  r'''the full objective away from the minimizer is required. Without uniqueness, the stated conclusion is value and solution-set distance convergence; convergence to one particular minimizer is not asserted.''',
  r'''the full objective away from the minimizer is required.'''),
 ('GL5', GLOBAL, 'caveat',
  r'''they left open, under the admissible full-BFGS convention of this paper.''',
  r'''they left open.'''),
 ('GL6', GLOBAL, 'caveat',
  r'''coordinate forms of $\norm{\cdot}_\infty$ have distinct gradients. These are concrete specializations of the norm corollary, with no separate priority claim. The familiar Euclidean norm is an already established consequence of Guo--Lewis's smooth-extension analysis''',
  r'''coordinate forms of $\norm{\cdot}_\infty$ have distinct gradients. The
Euclidean norm case follows from Guo--Lewis's
smooth-extension analysis'''),
 ('GL7', GLOBAL, 'caveat',
  r'''model was analyzed by Lewis--Overton under their stated search conventions \cite[Section~5.1]{LO}.''',
  r'''model was analyzed by Lewis--Overton \cite[Section~5.1]{LO}.'''),

 ('L1', LOCAL, 'positive',
  r'''quadratic Hessians. A finite maximum of arbitrary quadratic formulas need not admit such a polyhedral partition and is not automatically covered. There is also no claim that iterates identify a cell or that rejected trials remain in the neighborhood $U$ of Theorem~\ref{art:polyhedral}.''',
  r'''quadratic Hessians. Maxima of quadratic formulas, whose switching sets are
generally curved, are treated in the plane below.'''),
 ('L2', LOCAL, 'caveat',
  r'''in which every admissible run converges in value and iterates to $x_*$. Uniqueness is a hypothesis here; $\lambda>0$ alone does not supply it.''',
  r'''in which every admissible run converges in value and iterates to $x_*$.'''),
 ('L3', LOCAL, 'repeat',
  r'''by the actual objective decrease. The field is constructed from the objective; BFGS never evaluates it.''',
  r'''by the objective decrease.'''),
 ('L4', LOCAL, 'caveat',
  r'''is stronger than ordinary descent. The strict-contour and regular-switching assumptions remain essential to this sufficient planar route; it does not give a criterion for every convergent run.''',
  r'''is stronger than ordinary descent.'''),
 ('L5', LOCAL, 'caveat',
  r'''charges its own motion to the accepted decrease. The proof uses the original coordinates and the unmodified BFGS update; a nonlinear change of variables or a replacement by polyhedral cells would not establish this conclusion.''',
  r'''charges its own motion to the accepted decrease.'''),

 ('V1', VERIF, 'positive',
  r'''The stable-manifold and strict-query arguments establish that this decomposition is realized by the specified algorithm; a branch change alone does not imply failure.''',
  r'''The stable-manifold
and strict-query arguments show that the specified algorithm realizes this
decomposition.'''),
 ('V2a', VERIF, 'caveat',
  r'''These comparisons explain sufficient hypotheses separating the proved positive classes from the examples. They do not make affine independence, positive multipliers or a comparison certificate necessary for convergence, and they do not turn every nonoptimal affine-critical point or accumulating singularity into a counterexample. The local question''',
  r'''These comparisons identify the hypotheses that separate the proved
positive classes from the examples. The local question'''),
 ('V2b', VERIF, 'positive',
  r'''Corollary~\ref{art:planar-max}. The examples concern the specified weak-Wolfe implementation with $0<c_1\le1/3$ and exceptional deterministic starts; they do not settle Lewis--Overton's almost-sure challenge under its additional hypotheses~\cite[Challenge~7.1]{LO}.''',
  r'''Corollary~\ref{art:planar-max}.
The failing starts constructed here form a sequence of points. Whether a
convex objective can have a set of failing starts of positive measure, the
setting of Lewis--Overton's almost-sure Challenge~7.1~\cite{LO}, is a natural
next question.'''),
 ('V3', VERIF, 'caveat',
  r'''needed for the article's main results are also contained here. Formal checking and author-side correspondence review have distinct roles; neither certifies publication priority or floating-point robustness.''',
  r'''needed for the article's main results are also contained here.'''),

 ('F1', FAIL, 'guard',
  r'''We construct an actual failure of each assertion,''',
  r'''We construct a counterexample to each assertion,'''),
 ('F2', FAIL, 'caveat',
  r'''keeps the initial matrix fixed across the copies. The distinction between a formal cycle and an implemented run matters at every part of this argument.''',
  r'''keeps the initial matrix fixed across the copies.'''),
 ('F3', FAIL, 'positive',
  r'''parameters. The failure set supplied by the theorem is a sequence of starts; it is not a positive-measure basin. There is no uniform positive lower curvature requirement on these branches.''',
  r'''parameters. Theorem~\ref{art:local-failure-lower} below adds uniform
positive lower curvature.'''),
 ('F4', FAIL, 'positive',
  r'''Choosing them in the algebra does not prove that the algorithm accepts them: we must also exclude every earlier candidate and verify both tests at the intended endpoint. The strict trial certificate below supplies exactly this missing dynamical condition.''',
  r'''The strict trial certificate below proves that the algorithm accepts them:
it excludes every earlier candidate and verifies both tests at the intended
endpoint.'''),
 ('F5', FAIL, 'guard',
  r'''All displayed intervals are rational enclosures, not rounded values.}''',
  r'''All displayed intervals are rational enclosures.}'''),
 ('F6', FAIL, 'caveat',
  r'''Theorem~\ref{art:local-failure}; no accepted-length sequence is assumed.''',
  r'''Theorem~\ref{art:local-failure}.'''),
 ('F7', FAIL, 'guard',
  r'''Coordinates are rendered from the rational center of the certified root box; exact cycle closure and trial decisions follow from Appendix~\ref{art:seed_certificate}. This drawing is not evidence of stable-manifold membership for the perturbed construction.}''',
  r'''Exact cycle closure and trial decisions are proved in
Appendix~\ref{art:seed_certificate}.}'''),
 ('F8', FAIL, 'caveat',
  r'''This is a covariance calculation, not an existence theorem for a local trajectory. To transfer a particular run,''',
  r'''To transfer a particular run with this calculation,'''),
 ('F9', FAIL, 'guard',
  r'''of the infinite induction. Locations, neighborhood shapes and relative scales are schematic, not a plot of the infinitely defined objective. The lower-curvature''',
  r'''of the infinite induction.
The lower-curvature'''),
 ('F10', FAIL, 'caveat',
  r'''map defined in a neighborhood of the point. A pointwise second-order expansion alone is not the convention.''',
  r'''map defined in a neighborhood of the point.'''),
 ('F11', FAIL, 'caveat',
  r'''persist along that orbit, for every fixed pair $0<c_1\le1/3$, $c_1<c_2<1$. No rounded initial state is asserted to lie on the stable manifold.''',
  r'''persist along that orbit, for every fixed pair $0<c_1\le1/3$, $c_1<c_2<1$.'''),
 ('F12', FAIL, 'repeat',
  r'''copies accumulate. This is why the theorem does not supply a finite strongly convex $C^2$ local counterexample.''',
  r'''copies accumulate.'''),
 ('F13', FAIL, 'guard',
  r'''a local copy of an actual bad query tree;''',
  r'''a local copy of a bad query
tree;'''),

 ('H1', HYP, 'positive',
  r'''full-BFGS histories together. They distinguish a function satisfying a convergence theorem from an infinite admissible run on that function, and from existence for every prescribed initial state. All norms''',
  r'''full-BFGS histories together. They exhibit functions satisfying the
convergence theorems, explicit infinite admissible runs on them, and a
criterion for runs from every initial state. All norms'''),
 ('H2', HYP, 'caveat',
  r'''not just differentiability of $t\mapsto F(x+tp)$. The lemma proves existence of a sequence of acceptable steps; it does not assert that a prescribed line-search implementation finds them.''',
  r'''not just differentiability of $t\mapsto F(x+tp)$.'''),
 ('H3', HYP, 'positive',
  r'''\subsection{Why the run-existence qualification matters}''',
  r'''\subsection{Initial data without an admissible run}'''),
 ('H4', HYP, 'caveat',
  r'''\end{proof} This is an obstruction to a differentiable infinite history from prescribed data, not an example of nonoptimal stagnation: the ray itself passes through the minimizer. The explicit histories above and the existence criterion specify which stronger non-vacuity conclusions accompany the convergence examples.''',
  r'''\end{proof}'''),

 ('LC1', LOWER, 'caveat',
  r'''region. This gives exact perturbed orbits; closeness of a finite floating-point trajectory would not. To prove''',
  r'''region. This gives exact perturbed orbits. To prove'''),
 ('LC2', LOWER, 'caveat',
  r'''the degree-two polynomial; no numerical eigenvector is used.''',
  r'''the degree-two polynomial.'''),
 ('LC3', LOWER, 'caveat',
  r'''This proves the proposition. The initial matrix is supplied by the stable-manifold point, not presumed to be identity or obtained by rounded forward shooting.\qed''',
  r'''This proves the proposition.\qed'''),
 ('LC4', LOWER, 'positive',
  r'''construction need not, and will not, have a second derivative at zero.''',
  r'''construction has no second derivative at zero.'''),

 ('P1', PLANAR, 'caveat',
  r'''regular part of one positive level. It does not assume that the BFGS iterates converge to one point of that level.''',
  r'''regular part of one positive level.'''),
 ('P2', PLANAR, 'positive',
  r'''of these finitely many curves. This is a compactness consequence of the charts, rather than an assumed finite bound on future branch changes.''',
  r'''of these finitely many curves, by compactness of the charts.'''),

 ('S1', SEED, 'caveat',
  r'''the strict inequalities force the specified search to choose that cycle. Solving the equations alone would leave the algorithmic claim unproved. All decimals defining a box are terminating rationals. No rounded point is substituted for a root or an infinite orbit.''',
  r'''the strict inequalities force the specified search to choose that cycle.
All decimals defining a box are terminating rationals.'''),
 ('S2', SEED, 'caveat',
  r'''Thus they are finite integer inequalities, rather than tolerances for a numerically computed root.''',
  r'''Thus they are finite integer
inequalities.'''),
 ('S3', SEED, 'caveat',
  r'''\eqref{art:seed_query_bounds}. All inputs, expressions, interval rules and output bounds of this finite certificate are now specified. The strict active gaps''',
  r'''\eqref{art:seed_query_bounds}. The
strict active gaps'''),
]


def pattern(old):
    return re.compile(r'\s+'.join(map(re.escape, old.split())))


def main():
    texts, failed = {}, []
    for eid, path, kind, old, new in EDITS:
        if path not in texts:
            texts[path] = (ROOT / path).read_text()
        found = list(pattern(old).finditer(texts[path]))
        if len(found) != 1:
            failed.append(f'{eid} {path}: {len(found)} matches')
            continue
        m = found[0]
        texts[path] = texts[path][:m.start()] + new + texts[path][m.end():]
    Path('/tmp/opencode/m44/article_edits.json').write_text(json.dumps(
        [dict(id=e, file=p, kind=k, old=o, new=n) for e, p, k, o, n in EDITS], indent=1) + '\n')
    if failed:
        print('NOT APPLIED; failed edits:')
        print('\n'.join(failed))
        sys.exit(1)
    if '--dry-run' in sys.argv:
        print(f'DRY RUN: all {len(EDITS)} edits match once')
        return
    for path, text in texts.items():
        (ROOT / path).write_text(text)
    print(f'APPLIED {len(EDITS)} edits to {len(texts)} files')


if __name__ == '__main__':
    main()
