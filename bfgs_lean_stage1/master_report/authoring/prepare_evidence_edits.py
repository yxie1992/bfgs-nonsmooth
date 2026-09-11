#!/usr/bin/env python3
"""Editorial replacement of unsupported execution history; no mathematics computed."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
source='BFGS_MASTER_REPORT_LaTeX/report/chapters/verification.tex'
lines=(ROOT.parent/source).read_text().splitlines(keepends=True)
reg=json.loads((ROOT/'audit/REPORT_STATUS.json').read_text())
mod=next(m for m in reg['modules'] if m['module']=='E')
new={
1:r'''\textbf{Operative verification record.} The evidence for this edition consists of actual pinned Lean builds, checked theorem statements and module-wide transitive axiom audits. The original report's old job counts, timings, precision claims and unprovided archive assertions are not adopted. They remain visible only in the preserved original and edit ledger.
''',
2:r'''\section{What the checks mean}\label{what-the-checks-mean}

Lean checks the formal proof term against its precise statement. Exact rational inequalities, algebraic roots, actual matrix updates, objective derivatives, infinite sequences and geometric existence arguments have different mathematical roles, but each retained assertion here has a reviewed formal correspondence. An external numerical result is not imported as a proof. Compiler logs are evidence of actual executions; they are not axioms and do not prove that an older execution happened.

The principal results concern ordinary full BFGS. The negative seeds and their embeddings are actual objective/run constructions. The positive framework derives its scalar hierarchy from actual principal determinants. The stable-manifold conclusion in L follows from the actual return map and a proved analytic argument, not a numerical starting vector assumed to lie on that manifold. Exact formal hypotheses and dependencies appear in the complete claim index.
''',
3:r'''\section{Actual build and audit register}\label{fresh-execution-register}

The pinned project uses Lean 4.19.0 and mathlib revision
\path{c44e0c8ee63ca166450922a373c7409c5d26b00b}.
All nine package revisions and clean dependency trees are checked. The preserved main source set contains 737 Lean files. The current module-wide audit supplements the older namespace-based theorem audit; the two scopes must not be conflated.

\begin{longtable}{@{}p{.39\textwidth}p{.55\textwidth}@{}}
\toprule Record & Meaning\\\midrule\endhead
Main project & 9,672 safe declarations, including 7,874 theorems.\\
Main plus exact supplemental corrections & 9,781 distinct safe declarations, including 7,954 theorems.\\
Transitive foundations & Only \texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}. No safe proof may reach an unsafe or partial artifact.\\
Preserved theorem audit & All 7,813 formerly enumerated theorem types and axiom sets are reconciled with the wider audit.\\
Claim review 20 & Six actual supplemental compiler jobs; 182 ordinary declaration reports, representing 141 distinct names. These occurrences are not added to the unique-declaration totals.\\
Module-wide audit & Main-only and combined environments are checked separately, including private/generated declarations and actual type/value dependencies.\\
\bottomrule\end{longtable}

The actual command records, exit codes, compiler output and source hashes are delivered under \path{master_report/audit/}. The earlier closed records under \path{audit/claim_review20/} and the reconstruction audit remain byte-preserved. New runs use new output directories. The safe declaration set is counted by names: lazy equation lemmas can receive different importing-module metadata without changing their names, types or proof dependencies.
''',
4:r'''\section{Mathematical scope of the reconstructed suites}\label{what-each-suite-actually-checks}

The labels below preserve correspondence with the original report. They describe present formal results, not a claim that the unavailable old scripts ran with their printed sample counts. Each subsection's exact exports are listed in the claim index.
''',
5:r'''\subsection{D-root}\label{d-root}

Actual algebraic seed existence and isolation, denominator signs, accepted and rejected trial decisions, and the global embedding geometry are proved. The root and containment statements apply to the exact specified objects, rather than a rounded seed.
''',
6:r'''\subsection{D-symbolic}\label{d-symbolic}

The inverse and Hessian updates, their secant identities, determinant and positivity properties, and the literal seed-cycle closure are Lean equalities or inequalities. No symbolic-program output is accepted as a mathematical premise.
''',
7:r'''\subsection{D-full-oracle}\label{d-full-oracle}

The exact deterministic failure and embedded local failure theorems establish the actual run and every stated line-search trial. They imply the specified infinite behavior; a finite list of sampled trials is not their proof.
''',
8:r'''\subsection{L-hyperbolicity}\label{l-hyperbolicity}

The normalized Jacobian is the derivative of the actual return map. The spectral contract and rational precision statements are proved for that derivative, and the actual stable-manifold construction is linked to it. The embedding's Hessian claims retain their stated local scope.
''',
9:r'''\subsection{L-embedding}\label{l-embedding}

Scalar node, peak, ramp and regularity formulas prove the complete local model. The smooth and step constructions then give their respective actual failure copies. The two regularity constructions retain their distinct hypotheses and conclusions.
''',
10:r'''\subsection{A-minors}\label{a-minors}

Compression identities and the Gram numerator are proved in arbitrary finite dimension. The principal Gram-sum identity and full-BFGS principal-minor hierarchy use actual determinants. Selected finite-dimensional cases are not substituted for this theorem.
''',
11:r'''\subsection{H-lifting}\label{h-lifting}

Actual projected full updates and the invariant matrix range give affine-fiber lifting. Reusable conditional limit implications retain their projected-run hypotheses. The final low-rank applications derive the limits they use.
''',
12:r'''\subsection{M-mixed}\label{m-mixed}

The actual full-matrix hierarchy yields the normalized hierarchy, weighted potential, qualitative reciprocal growth and superquadratic reciprocal growth under summable predicted decreases. A separately specified unexcited-metric example proves its literal matrix-limit statement; no such limit is assumed in the principal convergence framework.
''',
13:r'''\subsection{P-polyhedral}\label{p-polyhedral}

The smooth-plus-polyhedral and smooth PLQ basin theorems, linear-image lifting and the stated scalar regularity example are formal results. Their hypotheses distinguish local smoothness from the stronger twice-differentiable conditions that some examples fail.
''',
14:r'''\subsection{R-secant}\label{r-secant}

Finite maxima, mixed powers, inward inequalities and homogeneous gauge composition lead to the stated radial basins and actual-run convergence. The exponents, domains and differentiability assumptions are present in the exact theorem types.
''',
15:r'''\subsection{R-interpretation}\label{r-interpretation}

Supporting-plane, radial and inward formulations are related by proved equivalences on their stated compact domains. The corrected homogeneous reference formula and compact optimizer deductions are included. The explicit four-piece objective in R is a new specified reconstruction with an actual full-BFGS failure run; it is not asserted to be an unidentified historical objective.
''',
16:r'''\subsection{G-obstruction}\label{g-obstruction}

Pointwise PSD feasibility, eligible-pair realization, incoming-jump obstructions and accumulating-kink certificate nonexistence are proved. Accessible and all-active jump spans remain distinct. Failure of a certificate is not represented as failure of BFGS.
''',
17:r'''\subsection{V-ridges}\label{v-ridges}

The moving-frame identity and the scalar-ridge implication into the planar convergence theorem are operative formal results. No unavailable independent ridge archive is needed for that implication.
''',
18:r'''\subsection{T-certificate}\label{t-certificate}

Projected PSD energy, objective-value rescaling, certificate normalization, transport and actual BFGS convergence are proved. The scalar nonnecessity result establishes a separate logical limitation of the sufficient condition.
''',
19:r'''\subsection{C-planar}\label{c-planar}

The correctly oriented determinant identity, actual angular derivative, all-pair endpoint estimates, quadratic basin and higher-dimensional warnings are formal statements. The higher-dimensional example does not invalidate the restricted planar theorem.
''',
20:r'''\subsection{U-multidimensional}\label{u-multidimensional}

Residual-frame contradiction, cutoff transport, finite-horizon bounds and the fixed-normal convergence theorem are proved. The spike oracle is the complete infinite-series objective with exact rational-query identities and proved peak derivatives. It is not a finite truncation used as a proxy for the function.
''',
21:r'''\subsection{C-planar-numerical}\label{c-planar-numerical}

The operative statement is analytic: the stated planar example converges, and hence every positive displayed tolerance is eventually attained. This does not establish the original execution count, trial count, decimal precision or a particular iteration at which a tolerance was attained.
''',
22:r'''\subsection{U-multidimensional-numerical}\label{u-multidimensional-numerical}

The actual fixed-normal spike objective has a complete oracle and the stated convergence basin in each allowed dimension. Its convergence implies eventual attainment of the printed positive tolerance. Historical run lengths, starts and precision remain unsupported rather than retrospectively certified.
''',
23:r'''\subsection{G-oscillatory-numerical}\label{g-oscillatory-numerical}

The explicitly defined accumulating-kink objective has proved eligible crossings, secant curvature and a divergent obstruction quotient. It disproves local certificate existence while scalar admissible runs converge. This construction replaces an unavailable auxiliary; it is not identified with that auxiliary or used as an infinite bad BFGS trajectory.
''',
24:r'''\section{Reviewed analytic arguments and remaining boundaries}\label{analytic-steps-that-still-require-independent-review}

The actual matrix hierarchy, ordered tail limits, objective certificate equivalences, planar joining, fixed-normal residual budgets, exact failure embeddings, stable-manifold existence and semialgebraic finite critical values all have formal proof chains in the delivered project. The claim index identifies their exact final contracts and internal dependencies. Assumptions such as regular switching, fixed normals, compact structural sublevels or low effective rank remain substantive.

The broader questions explicitly marked open in Modules A and H are not proved. Nor does the report claim convergence for every finite convex nonsmooth objective, a positive-measure basin for the deterministic seed, robustness to floating-point perturbation, or a rounded initial point lying exactly on the stable manifold. No publication-priority claim is made. Those boundaries are part of the corrected statement, not gaps concealed by the compiler pass.
''',
25:r'''\section{Reproduce the audit}\label{reproduce-the-audit}

From \path{bfgs_lean_stage1/}, the original pinned bootstrap remains the entry point for obtaining the toolchain and building the project:
\begin{verbatim}
bash scripts/bootstrap.sh
\end{verbatim}
The closed milestone evidence should be preserved when rerunning tools that write their historical output paths. The current edition's public runner instead creates fresh output directories:
\begin{verbatim}
python3 master_report/audit/run.py --run
\end{verbatim}
The audit records the actual commands and compiler output, checks the main source hashes, verifies the pinned clean dependencies before and after, enumerates the compiled module-owned declarations, and reconciles the main and supplemental environments. Its README describes the read-only evidence check and the exact default output path. A nonzero exit or mismatch fails the gate.

The earlier source/correspondence records also have read-only validators:
\begin{verbatim}
python3 scripts/validate_report_reconstruction_19.py
python3 scripts/verify_report_claim_review_20.py
\end{verbatim}
The axiom audit verifies proof dependencies, not the consistency of the permitted standard axioms. No external symbolic, interval or numerical result is a trusted mathematical input.
''',
26:r'''\section{Rebuild the corrected report}\label{rebuild-the-report}

From \path{bfgs_lean_stage1/}:
\begin{verbatim}
python3 scripts/build_rigorous_master_report.py
python3 scripts/build_rigorous_master_report.py --check
python3 scripts/render_rigorous_master_report.py
\end{verbatim}
The first command applies uniquely anchored, source-hash-bound edits to the preserved chapters and generates the complete claim/proof index. The second checks reproducible textual assembly. The third runs the LaTeX build and records PDF checks. The resulting PDF is \path{output/pdf/Rigorous_BFGS_Master_Report.pdf}. These are document tools; they perform no unchecked computation for a Lean proof. The edition status and final review record bind the generated report, source correspondence and actual compiler evidence.
'''
}
edits=[]
for span in mod['coverage_spans']:
 n=int(span['id'].split('.')[-1]);a=span['start_line'];b=span['end_line']
 replacement=new[n]+'\n'
 exports=[]
 if n==15:
  extra=json.loads((ROOT/'master_report/edits/20_rg_uq.json').read_text())
  exports=next(e['lean_exports'] for e in extra if e['id']=='R.homogeneous_reference_and_compact_optimizer')
 if n==16:
  exports=next(e['lean_exports'] for e in json.loads((ROOT/'master_report/edits/20_rg_uq.json').read_text()) if e['id']=='G.accessible_span_vs_all_active')
 edits.append({'id':'E.actual_record.'+str(n),'source':source,'source_sha256':mod['source_sha256'],'start_line':a,'end_line':b,'old':''.join(lines[a-1:b]),'new':replacement,'lean_exports':exports,'kind':'execution_evidence_correction_and_formal_scope','reason':'Replace unsupported historical execution/provenance with actual compiler evidence or the exact reconstructed mathematical scope; historical counts are not certified.'})
(ROOT/'master_report/edits/40_evidence.json').write_text(json.dumps(edits,indent=2,ensure_ascii=False)+'\n')
print('Prepared',len(edits),'disjoint E replacements.')
