# Independent peer review: foundation M/T/G literature packet

Reviewed 2026-09-12 05:01 UTC (2026-09-11 America/Los_Angeles). Scope: the foundation packet, corrected `foundation.tex`, `T.tex`, and `G.tex`, with independent primary-source checks focused on the requested classical matrix and multiplicative-error comparisons. All baseline report hashes still match. No sealed report or Lean files were edited.

## Verdict

The packet accurately distinguishes established matrix tools from the report's specific hierarchy and certificates. No displayed-formula mismatch or false unconditional convergence claim was found. The broad absence-of-exact-match classifications remain bounded search findings, not novelty certificates. Minor hypothesis and attribution clarifications were applied directly to the packet's Markdown and JSON.

## Formula and scope checks

- The adjacent-degree inequality agrees with `M:minor`, including the coefficient on each term and the convention at degree n+1. The packet's beta=t/d equals the report's beta=−yᵀHg/q because s=−alpha Hg and d=alpha q. The determinant endpoint is classical; its existence does not establish the full hierarchy.
- The qualitative reciprocal theorem requires an infinite full-BFGS run, bounded gradients, and fixed weak-Wolfe parameters. The packet now states these explicitly. Its superquadratic statement now explicitly retains the bounded-gradient and fixed-Wolfe hypotheses when adding summability. The finite-horizon conclusion and fixed-tail order agree with `M:finitehorizon` and `M:superquad`.
- The fixed-reference energy identity and the moving-frame scope agree with `M:fixedenergy` and `M:frameidentity`. The residual theorem derives its restricted trace bound; it does not assume matrix convergence.
- The T criterion quantifies over all eligible pairs within each positive band, for sufficiently small predicted decrease. G's rank-one reduction covers visibility and secants only; its normalization is existentially equivalent transport, and its incoming-jump obstruction is certificate nonexistence rather than algorithmic failure. These distinctions are preserved.

## Primary-source checks and corrections

[Nocedal 1992](https://users.iems.northwestern.edu/~nocedal/PDFfiles/acta.pdf): Section 5 and equations (5.3), (5.7), (5.13), and (5.15) are correct locators. Added (5.21), the explicit matrix potential. Equation (5.13) uses smooth Hessian bounds; it is background rather than a nonsmooth result.

[Jin–Jiang–Mokhtari 2024](https://proceedings.neurips.cc/paper_files/paper/2024/file/1e269abc604816c35f600ae14b354efd-Paper-Conference.pdf): Appendix C, pp.15–16, and Appendix D, Proposition D.1, p.16, are correct. Added the proposition's explicit attribution to the exact-search preprint's Proposition 2. Clarified that the potential inequality is algebraic, while smooth strong-convexity assumptions belong to the rate analysis.

[Combettes–Vũ 2013](https://pcombet.math.ncsu.edu/nonan3.pdf): Lemmas 2.2–2.3 and pp.3–4 are correct. Distinguished scalar Lemma 2.2 from operator Lemma 2.3. The latter's positive common coercivity, uniform norm bound, summable errors, and operator-order condition support the packet's exclusion of a direct substitution for T.

## Taxonomy correction agreed during consolidation

The parent reviewer agreed to define `standard_deduction` as an elementary algebraic consequence or application of established techniques, without claiming an exact publication match. Accordingly, `FND_REFERENCE`, `FND_NORMALIZE`, and `FND_POINTWISE` were changed to that classification. `FND_Z05` was removed from the closest-source list for the polar/pointwise characterization because publisher book metadata does not establish that formulation. The book remains a general matrix-algebra background reference elsewhere. These changes make the classification agree with the packet's qualified prose.

## Limits and validation

This was an independent bounded literature review, not a second Lean audit or an independent proof certification of external publications. The packet already marks inaccessible Powell, Byrd–Nocedal, and Schur-complement texts; this review does not upgrade their access status. Other bibliographic dates and unrelated theorem families were not exhaustively rechecked. The updated JSON parses, and all baseline report hashes remain unchanged.
