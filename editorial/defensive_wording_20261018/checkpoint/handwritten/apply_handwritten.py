#!/usr/bin/env python3
"""M44 (TODO_MANUSCRIPT_REVIEW.md): edits of the hand-written companion files.

RS1 (research_story), MS1 (master), CV1 (current_verification), CR1
(correspondence) and the bibliography header were applied by hand before this
script.  Every old text must occur exactly once.  Usage: apply_handwritten.py [--write]
"""
import pathlib
import sys

ROOT = pathlib.Path('/home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth')

EDITS = [
    # research_story.tex
    ('companion/research_story.tex', 'RS2',
     r'''maxima of linear functions. The Euclidean norm is an attributed known case.
''',
     r'''maxima of linear functions. The Euclidean norm case recovers the theorem of
Guo--Lewis.
'''),
    ('companion/research_story.tex', 'RS3',
     r'''The full noncompact homogeneous value alternatives are retained separately:
they conclude objective-value convergence without any conclusion about the iterates, and they do not subsume
Xie--W\"achter's finite detection of unbounded descent in the two-piece
affine model~\cite[Theorem~IV.1]{XW}.
''',
     r'''Chapter~\ref{comp:H} uses a different potential to prove value alternatives
for noncompact homogeneous objectives.
'''),
    ('companion/research_story.tex', 'RS4',
     r'''family use different hypotheses and remain independent parts of the theory.
''',
     r'''family extend the theory under different hypotheses.
'''),
    ('companion/research_story.tex', 'RS5',
     r'''neighborhood guarantees. They neither establish positive-probability failure
nor produce a finite uniformly strongly convex $C^2$ local counterexample.
''',
     r'''neighborhood guarantees.
'''),
    ('companion/research_story.tex', 'RS6',
     r'''The common analytical tool is an adjacent-degree hierarchy for actual
principal determinants''',
     r'''The common analytical tool is an adjacent-degree hierarchy for the
principal determinants'''),
    ('companion/research_story.tex', 'RS7',
     r'''is allowed throughout. The radial and moving-field arguments demonstrate
ways this mechanism succeeds; the scalar nonnecessity results prevent it
from being read as a complete characterization.
''',
     r'''is allowed throughout. The radial and moving-field arguments show how this
mechanism succeeds.
'''),
    # master.tex (not registered)
    ('companion/master.tex', 'MS2',
     r'''This report accompanies the research article of the same title. It is a
complete repository report, not journal-published supplementary material.
''',
     r'''This report accompanies the research article of the same title and
contains the complete mathematical record.
'''),
    ('companion/master.tex', 'MS3',
     r'''The article proves the centered and coercive homogeneous global results,
the local finite-partition theorem and a genuinely nonradial planar
application, alongside both independent local failure constructions. This
companion retains the full corrected record, including conclusions with
incomparable hypotheses beyond the article's selection. Shared matrix
foundations are proved once in Chapter~\ref{comp:M}.
''',
     r'''The article proves the centered and coercive homogeneous global results,
the local finite-partition theorem and a nonradial planar application,
alongside both independent local failure constructions. This companion
contains the complete theory, including results beyond the article's
selection. Shared matrix foundations are proved once in
Chapter~\ref{comp:M}.
'''),
    ('companion/master.tex', 'MS4',
     r'''proof in Chapter~\ref{comp:C}. Chapters~\ref{comp:Q} and \ref{comp:U} retain
the distinct flat-contour and fixed-normal extensions; neither is absorbed
by the planar strict-contour argument. Chapter~\ref{comp:G} tests the limits
of the certificate itself. Chapters~\ref{comp:D} and \ref{comp:L} keep the two
local negative regimes separate. Appendix~\ref{comp:seed_certificate} spells out the finite
''',
     r'''proof in Chapter~\ref{comp:C}. Chapters~\ref{comp:Q} and \ref{comp:U} give
the flat-contour and fixed-normal extensions, which reach objectives outside
the planar strict-contour theorem. Chapter~\ref{comp:G} tests the limits
of the certificate itself. Chapters~\ref{comp:D} and \ref{comp:L} construct
the two local counterexamples. Appendix~\ref{comp:seed_certificate} spells out the finite
'''),
    ('companion/master.tex', 'MS5',
     r'''and Appendix~\ref{comp:correspondence} distinguish mathematical theorems,
exact formal contracts, conditional results and execution evidence.
''',
     r'''and Appendix~\ref{comp:correspondence} describe the formal verification and
its correspondence with the text.
'''),
    ('companion/master.tex', 'MS6',
     r'''theorem-level correspondence. Definitions, assumptions, questions and
historical execution records are distinguished from proved conclusions.
''',
     r'''theorem-level correspondence.
'''),
    ('companion/master.tex', 'MS7',
     r'''The literature record distinguishes known special cases, standard tools,
related results and unresolved priority. The Euclidean-norm result of
Guo--Lewis and the two-piece affine escape theorem of Xie--W\"achter are
prior work, not new discoveries here~\cite{GL18,XW}. Exact access levels, versions and
search limits are in \path{editorial/LITERATURE_LEDGER.json} and the narrative
revision's primary-source comparison ledger; a metadata check
does not constitute reading a proof. Nothing in a Lean audit certifies novelty.
''',
     r'''The literature record identifies known special cases, standard tools and
related results. The Euclidean-norm theorem is due to Guo--Lewis~\cite{GL18},
and the two-piece affine escape theorem to Xie--W\"achter~\cite{XW}. Source
versions and access records are in \path{editorial/LITERATURE_LEDGER.json}
and the narrative revision's primary-source comparison ledger.
'''),
    # current_verification.tex
    ('companion/current_verification.tex', 'CV2',
     r'''dependencies. This restriction identifies the foundations actually used;
it does not establish their consistency or replace trust in the kernel.
''',
     r'''dependencies. This restriction identifies the foundations the proofs use.
'''),
    ('companion/current_verification.tex', 'CV3',
     r'''\path{editorial/formal_audit/}. Actual per-command output, input/output hashes,''',
     r'''\path{editorial/formal_audit/}. Per-command output, input/output hashes,'''),
    ('companion/current_verification.tex', 'CV4',
     r'''The literal mixed-benchmark theorem quantifies over every actual admissible
run for''',
     r'''The mixed-benchmark theorem quantifies over every admissible
run for'''),
    ('companion/current_verification.tex', 'CV5',
     r'''A further skeptical review
freshly compiled''',
     r'''A further review
freshly compiled'''),
    ('companion/current_verification.tex', 'CV6',
     r'''The runner and actual compiler/audit
evidence''',
     r'''The runner and the compiler/audit
evidence'''),
    ('companion/current_verification.tex', 'CV7',
     r'''lower-counterexample branches: each actual
whitened branch''',
     r'''lower-counterexample branches: each
whitened branch'''),
    ('companion/current_verification.tex', 'CV8',
     r'''release and its limits. Its dates identify those earlier executions.''',
     r'''release. Its dates identify those earlier executions.'''),
    # correspondence.tex
    ('companion/correspondence.tex', 'CR2',
     r'''Preserved runner, actual fresh compiler and
transitive audit evidence.''',
     r'''Preserved runner, fresh compiler and
transitive audit evidence.'''),
    ('companion/correspondence.tex', 'CR3',
     r'''homogeneous convergence, local finite-partition and planar results, the
actual-matrix framework and both finite-branch local counterexamples. The
noncompact homogeneous alternatives, fixed-normal geometry, flat-contour
parabolic family, lifting, rates and scalar baseline remain separate
companion results. The infinite constant-Hessian family in
Chapter~\ref{comp:L} also remains here after its removal from the article's
main theorem selection. None of these results is treated as
superseded merely because the article selects a smaller statement set.
''',
     r'''homogeneous convergence, local finite-partition and planar results, the
matrix framework and both finite-branch local counterexamples. The
noncompact homogeneous alternatives, fixed-normal geometry, flat-contour
parabolic family, lifting, rates and scalar baseline are proved in this
companion, as is the infinite constant-Hessian family of Chapter~\ref{comp:L}.
'''),
    ('companion/correspondence.tex', 'CR4',
     r'''data; their code is in \path{paper/figures/}. The figure computations are
renderings, not additional formal proof premises. Build logs, page-level''',
     r'''data; their code is in \path{paper/figures/}. Build logs, page-level'''),
    ('companion/correspondence.tex', 'CR5',
     r'''closure. Reading one exported name without expanding those contracts would
not validate the prose. Correspondence review is a separate logical bridge
from kernel checking, and author approval remains necessary before submission.''',
     r'''closure. Correspondence review links the prose to the kernel-checked
statements; author approval remains necessary before submission.'''),
    # bibliography.tex (not registered): access disclaimers removed; versions,
    # locators and disambiguations kept.
    ('companion/bibliography.tex', 'B-header',
     r'''Numbered source locators below identify the inspected version. Journal publication metadata and preprint proof text are distinguished. Per-source access records are in''',
     r'''Numbered locators below refer to the version identified in each entry. Per-source records are in'''),
    ('companion/bibliography.tex', 'B-WW',
     r'''Theorem~2.5 in this report refers specifically to the inspected preprint \url{https://arxiv.org/abs/2204.00282v1} (1 April 2022). The journal identity was verified separately; no identical journal numbering is assumed.''',
     r'''Theorem~2.5 in this report refers to the preprint \url{https://arxiv.org/abs/2204.00282v1} (1 April 2022).'''),
    ('companion/bibliography.tex', 'B-LW',
     r'''Propositions 5.5--5.6 and the bundle-Newton result are cited in the inspected preprint; no journal publication was established in the audit.''',
     r'''Propositions 5.5--5.6 and the bundle-Newton result refer to this preprint.'''),
    ('companion/bibliography.tex', 'B-BDLS',
     r'''Inspected preprint: \url{https://arxiv.org/abs/math/0601530v1}''',
     r'''Preprint: \url{https://arxiv.org/abs/math/0601530v1}'''),
    ('companion/bibliography.tex', 'B-LL',
     r''' (2018). The earlier audit inspected that proof text; the present run verified the 2022 publication metadata. Numbered statements are not transferred between versions, and references to the 2018 version retain its two authors.''',
     r''' (2018).'''),
    ('companion/bibliography.tex', 'B-CCS10',
     r'''Theorem~2.1 is cited in the inspected preprint''',
     r'''Theorem~2.1 refers to the preprint'''),
    ('companion/bibliography.tex', 'B-GR91',
     r'''Publisher abstract and history were inspected; the original full proof was not obtained. The 1987 ANL/MCS-TM-105 predecessor has a different title containing ``semi-smooth and is only a bibliographic pointer here.''',
     r'''The 1987 predecessor ANL/MCS-TM-105 has a different title, containing ``semi-smooth''.'''),
    ('companion/bibliography.tex', 'B-BN89',
     r'''Original full-text access was limited. The matrix-technique comparison is additionally supported by the inspected exposition~\cite{FND_N92}.''',
     r'''The matrix-technique comparison also draws on the exposition~\cite{FND_N92}.'''),
    ('companion/bibliography.tex', 'B-P76',
     r'''Original full text was not obtained; bibliographic identity and the classical antecedent were checked through~\cite{FND_BN89,FND_N92,GL18}. No inspected exact match for a report theorem is asserted.''',
     r'''See also the accounts in~\cite{FND_BN89,FND_N92,GL18}.'''),
    ('companion/bibliography.tex', 'B-Z05',
     r''' Publisher contents and metadata were inspected; this is a classical matrix-algebra pointer, not an inspected BFGS proof.''',
     r''''''),
    ('companion/bibliography.tex', 'B-JJM24AW',
     r'''was first posted 25 April 2024; its revised v2 (8 January 2025) was also inspected in the earlier audit.''',
     r'''was first posted 25 April 2024 and revised on 8 January 2025.'''),
    ('companion/bibliography.tex', 'B-JM25',
     r'''Earlier inspected version: \url{https://arxiv.org/abs/2507.00361v2} (25 October 2025; first posted 1 July 2025). The current run verified the NeurIPS publication and read its setup. The earlier Proposition~2.1 and Appendix~B locators remain preprint-version locators, without an assumed transfer of numbering.''',
     r'''Earlier version: \url{https://arxiv.org/abs/2507.00361v2} (25 October 2025; first posted 1 July 2025), to which the Proposition~2.1 and Appendix~B locators refer.'''),
    ('companion/bibliography.tex', 'B-Bogosel',
     r'''equation~(4), refers to the inspected preprint''',
     r'''equation~(4), refers to the preprint'''),
    ('companion/bibliography.tex', 'B-DDJ',
     r'''Inspected preprint: \url{https://arxiv.org/abs/2108.11832v2}. Numbered locators in the literature review refer to this version, not an assumed identical journal numbering.''',
     r'''Preprint: \url{https://arxiv.org/abs/2108.11832v2}; numbered locators in the literature review refer to this version.'''),
    ('companion/bibliography.tex', 'B-BC10',
     r'''Inspected preprint: \url{https://arxiv.org/abs/0906.0807}''',
     r'''Preprint: \url{https://arxiv.org/abs/0906.0807}'''),
    ('companion/bibliography.tex', 'B-LZ15',
     r''' Publisher information and indexed portions of the 2013 author manuscript were inspected; complete proof access remains limited. The comparison is restricted to the inspected source claims.''',
     r''''''),
    ('companion/bibliography.tex', 'B-M14',
     r'''Sections~3 and~5 refer to the inspected preprint''',
     r'''Sections~3 and~5 refer to the preprint'''),
    ('companion/bibliography.tex', 'B-DAI02',
     r''' Publisher abstract and author bibliography were inspected; full proof access was limited.''',
     r''''''),
    ('companion/bibliography.tex', 'B-DAI13',
     r''' Only the abstract and opening discussion were inspected; no complete proof audit is asserted.''',
     r''''''),
    ('companion/bibliography.tex', 'B-DIAO26',
     r''' Theorem 1 and the relevant construction were inspected for comparison; this citation neither establishes journal publication nor an independent correctness audit.''',
     r''''''),
    ('companion/bibliography.tex', 'B-RUMP10',
     r'''(author PDF p.~89), not Section~13.2, which concerns multiple roots.''',
     r'''(author PDF p.~89).'''),
    ('companion/bibliography.tex', 'B-YVGS10',
     r'''The publisher abstract was screened for the modified subBFGS/subLBFGS algorithms; this is not a proof source for unmodified full BFGS.''',
     r'''Its subBFGS and subLBFGS algorithms modify BFGS for nonsmooth objectives.'''),
    ('companion/bibliography.tex', 'B-Rockafellar',
     r'''Theorem~25.5 is the conventional differentiability locator. Author and publisher metadata were freshly verified; the original proof text was not freshly obtained in this run.''',
     r'''Theorem~25.5 is the cited differentiability theorem.'''),
]


def main() -> int:
    write = '--write' in sys.argv[1:]
    texts = {}
    failures = 0
    for path, ident, old, new in EDITS:
        text = texts.setdefault(path, (ROOT / path).read_text())
        count = text.count(old)
        if count != 1:
            print(f'FAIL {ident}: old text occurs {count} times in {path}')
            failures += 1
            continue
        texts[path] = text.replace(old, new)
        print(f'ok   {ident}')
    if failures:
        print(f'{failures} failures; nothing written')
        return 1
    if write:
        for path, text in texts.items():
            (ROOT / path).write_text(text)
        print('written:', ', '.join(sorted(texts)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
