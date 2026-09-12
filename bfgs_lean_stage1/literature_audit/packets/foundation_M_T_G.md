# Literature comparison: the matrix foundation and transported certificates

Search cutoff: 11 September 2026, America/Los_Angeles. The comparison target is the corrected edition at the commit and hashes in `../BASELINE.json`. The companion JSON records individual research claims, source access, exact locators, and searches. This is a bounded literature audit; the absence of an exact match does not establish priority.

## What is already established

The full BFGS update, its positive definiteness under positive curvature, its secant equation, and its determinant identity are classical. Trace and determinant potentials are central to the Powell/Byrd–Nocedal tradition. Nocedal's author manuscript **Section 5**, equations (5.3), (5.7), (5.13), (5.15), and the potential (5.21), is an accessible primary exposition. The relevant manuscript pages are 16–21, rather than the journal's pagination. The report should credit this background before introducing its additional hierarchy. [Nocedal 1992](https://users.iems.northwestern.edu/~nocedal/PDFfiles/acta.pdf)

Byrd–Nocedal's 1989 article is a direct bibliographic antecedent for matrix-potential analysis. Its abstract and publication metadata were accessible; its complete original proof was not. Powell's 1976 paper was identified through primary bibliographies and Nocedal's exposition, but its original full text was not obtained. Neither inaccessible text is counted as having been searched internally for the exact hierarchy. [Byrd–Nocedal 1989](https://epubs.siam.org/doi/10.1137/0726042)

Gram determinants, Schur complements, spectral decomposition, Cauchy–Binet, arithmetic–geometric mean, PSD Cauchy–Schwarz, and congruence of quadratic forms are established mathematics. Horn–Zhang's chapter, pages 17–46, is an appropriate general bibliographic pointer for Schur complements; only the publisher contents and metadata were inspected, so no unseen chapter theorem is used as an exact match. [Zhang, editor, 2005](https://link.springer.com/book/10.1007/b105056)

Recent BFGS work also uses matrix potentials and product bounds. Jin–Jiang–Mokhtari's Armijo–Wolfe analysis uses a trace-minus-log-determinant potential inequality in Appendix D, Proposition D.1 (p.16), explicitly credited there to the exact-search preprint's Proposition 2. Appendix C (pp.15–16) applies AM–GM twice. The rate theorems' smooth strong-convexity assumptions differ from the report's accepted-gradient setting; the underlying potential inequality is algebraic. Moreover, its normalized gradient quantity is not the report's predicted quadratic form q = gᵀHg. [NeurIPS 2024 paper](https://proceedings.neurips.cc/paper_files/paper/2024/file/1e269abc604816c35f600ae14b354efd-Paper-Conference.pdf)

The related exact-search paper is now published online (19 August 2025), with a 2026 volume assignment. Its Section 2 discusses the classical variational characterization and Section 3 develops potential inequalities. The exact-search algorithm and smooth assumptions prevent treating its rates as the same theorem as the nonsmooth rates in Module F. [Published article](https://link.springer.com/article/10.1007/s10107-025-02256-7)

## The matrix hierarchy and its quantitative consequences

Module M uses actual full matrices and actual elementary symmetric sums of principal determinants, not an assumed scalar recursion. With B = H⁻¹, q = gᵀHg, d = αq, t = yᵀs, and β = t/d, its hierarchy is

\[
 e_j(H_+)\le \frac{\|y\|^2}{\beta^2q}e_{j+1}(H)
             +\frac{\alpha}{\beta}e_j(H),\qquad 1\le j\le n,
\]

where e_(n+1) = 0. At the top degree the report additionally retains the exact determinant update. The determinant endpoint is classical; an exact precedent for the complete adjacent-degree inequality, under these hypotheses, was not found in the accessed primary literature or the distinctive-formula searches.

The resulting reciprocal theorems must be distinguished. For an infinite admissible full-BFGS run with fixed weak-Wolfe parameters, bounded accepted gradients and d_k → 0 imply divergence of the geometric and arithmetic means of q_k⁻¹. Under the same bounded-gradient and fixed weak-Wolfe assumptions, summability of d_k gives the stronger finite-horizon bound and

\[
 N^{-2}\sum_{k<N}q_k^{-1}\longrightarrow+\infty.
\]

These statements neither assert q_k → 0 pointwise nor convergence of H_k. The proof weights the principal-minor hierarchy, iterates it, applies AM–GM, and takes the horizon limit on a fixed tail before shrinking the tail budget. The elementary inequalities are existing tools. No exact match was found for this nonsmooth full-BFGS combination of a finite-horizon inequality and superquadratic reciprocal-sum growth.

It would be inaccurate to call this the first use of determinants, matrix potentials, or product estimates in BFGS. A defensible attribution separates those antecedents from the particular hierarchy and its consequences. Recent smooth convergence rates are contextual comparisons, not grounds for identifying different quantities or transferring smoothness assumptions.

## Moving references, frames and residuals

The identity E_(k+1) = E_k − a_k²/q_k + (y_kᵀr_(k+1))²/t_k follows by expansion of the classical Hessian update. It is elementary algebraic content; the important report-level question is how its correction term is controlled. The moving-frame identity follows from annihilation of the step direction and congruence. The report's frame criterion also requires visibility, a bounded secant correction, and bounded cumulative transport products and inverses, all derived separately when an objective theorem is claimed. A trajectory criterion is not by itself an unconditional objective result.

For residual frames, Module M first derives a linear restricted trace bound on a fixed smooth subspace, then obtains a quadratic cumulative energy allowance, which the reciprocal-sum theorem contradicts. This uses standard Young inequalities and a discrete multiplicative-error estimate. An exact published match for that BFGS residual-frame theorem was not found.

Summable multiplicative errors and their normalization have a clear earlier precedent in Combettes–Vũ, Lemmas 2.2–2.3. Lemma 2.2 is a scalar summable-error result; Lemma 2.3 uses a common positive coercivity constant and a uniform operator-norm bound, together with one of its two approximate-monotonicity inequalities. Module T's comparison field may be singular and unbounded, while M's residual error budget need not be summable. Consequently their theorem cannot simply replace the report's proof. [Combettes–Vũ 2013](https://pcombet.math.ncsu.edu/nonan3.pdf)

## Objective certificates and the geometry of their limitations

Module T's sufficient condition uses a position-dependent PSD field, visibility of gradients, control of incoming secants, and transport only after projecting away the executed step. Its quantifiers cover all eligible small-decrease pairs on each positive band. No matching complete full-BFGS criterion was found. Its local and one-sided shell forms are localization deductions from that criterion. They do not establish convergence for every convex nonsmooth function.

Module G's objective-value exponential rescaling removes the multiplicative transport allowance. This is a specific application of a familiar normalization idea; it is not an independent algorithmic modification. The ellipsoid/support-function interpretation and the pointwise reduction from PSD fields to rank-one choices use standard linear and convex duality. The latter concerns visibility and secants only and says nothing about compatibility of transport across points.

The incoming-jump obstruction is more specific: if an endpoint gradient can be expressed as a combination of incoming jumps whose weighted square-root curvature cost vanishes, every field satisfying visibility and secant control is excluded. Its proof is PSD Cauchy–Schwarz and the triangle inequality. No exact published statement was located for this certificate class. Different predecessors need not lie on one infinite BFGS history, since the certificate requires every eligible pair. This is a certificate nonexistence result, not an algorithmic failure result.

The normal/tangent discussion has the established VU and partial-smoothness antecedents in the geometry packet. The report correctly distinguishes accessible eligible jumps from the span of all active-gradient differences. Only with an additional accessibility argument may the latter replace the former. Neither this comparison nor the failure of one canonical field excludes all other convergence proofs.

The self-concordant analysis of Jin–Mokhtari is another recent smooth comparison: it avoids uniform global strong convexity and Lipschitz-gradient bounds while retaining smooth self-concordant structure. Its affine invariance and potential analysis are related techniques, not a published nonsmooth certificate theorem. [2025 preprint, v2](https://arxiv.org/html/2507.00361v2)

## Attribution and remaining limits

The mathematical lineage warrants citations to classical BFGS matrix analysis and standard quadratic-form tools even if no exact theorem match is found. Similarity does not identify which papers an AI system actually used. Explicit report citations establish acknowledged connections; newly located similarities establish mathematical antecedents, with causal provenance unknown.

Searches included classical references, recent smooth full-BFGS rates, variable-metric convergence, principal-minor and elementary-symmetric terminology, reciprocal growth, and incoming-jump/certificate terminology. Differently named results, inaccessible texts, dissertations, and unindexed work may have been missed. No assertion here certifies publication priority or independently verifies the proofs of external papers.
