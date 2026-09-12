# Primary-literature anchors for the opening

Checked online on 12 September 2026. These are narrow source checks for the narrative, not an exhaustive priority audit. Use the repository's fuller literature register and exact theorem contracts when drafting. No third-party PDF is redistributed here.

## Lewis--Overton: phenomenon and the exact open challenge

A. S. Lewis and M. L. Overton, *Nonsmooth optimization via quasi-Newton methods*, Mathematical Programming 141 (2013), 135–163.

Author's published manuscript:
https://cs.nyu.edu/overton/papers/pdffiles/nsoquasi.pdf

Relevant locations: introduction, Section 4 (particularly Algorithm 4.6), and Section 7, Challenge 7.1 (printed p. 160).

The challenge fixes a line search and asks for probability-one behavior under absolutely continuous initialization for locally Lipschitz semialgebraic objectives with bounded sublevels. It includes stationarity of cluster points, behavior of the trial values, nonbreakdown and a spectral-subspace statement. The paper's observations motivate the general question; its special analyses do not establish the general conjecture.

Narrative consequence: use the challenge to establish the research problem, then distinguish our deterministic counterexamples and positive convex subclasses. Neither exceptional bad starts nor the nonsemialgebraic local accumulation construction establishes a refutation of the full almost-sure challenge.

## Guo--Lewis: a precise before/after comparison

J. Guo and A. S. Lewis, *Nonsmooth variants of Powell's BFGS convergence theorem*, SIAM Journal on Optimization 28(2) (2018), 1301–1311; DOI 10.1137/17M1121883.

Author's manuscript:
https://people.orie.cornell.edu/aslewis/publications/18-nonsmooth.pdf
Publisher:
https://epubs.siam.org/doi/10.1137/17M1121883

Theorems 3.2, 4.1 and 4.3 develop extensions of Powell's argument, including convex smooth replacements that preserve the objective on specified regions. Corollary 4.2 gives Euclidean-norm convergence in arbitrary dimension. Corollary 4.4 gives, for u^2+|v|, a subsequence converging to a point on v=0. The paragraph immediately after Corollary 4.4 explicitly leaves convergence of all BFGS sequences to zero open.

Narrative consequence: the whole-sequence mixed-benchmark result deserves explicit prominence. Credit the broader Guo--Lewis method, not just its norm corollary. Explain what new outcome is obtained, rather than suggesting that earlier work had no theorem or universally assumed matrix convergence.

## Xie--Wächter: two-piece escape is an independent stronger conclusion

Y. Xie and A. Wächter, *On the convergence of BFGS on a class of piecewise linear non-smooth functions*, arXiv:1712.08571, 2017.

https://arxiv.org/abs/1712.08571

Relevant locations in the supplied v1: Theorem II.1 (affine invariance), Theorem IV.1 and associated remarks (finite escape for the two-piece class).

Narrative consequence: our homogeneous/many-piece theory broadens the family and distinguishes successful convergence from nonstationary stagnation, but a statement about an infinite run's values does not replace finite detection of an unbounded direction. Use the precise original line-search and differentiability conventions.

## Gebken: the gap is still concrete in recent work

B. Gebken, *Technical Results on the Convergence of Quasi-Newton Methods for Nonsmooth Optimization*, Journal of Optimization Theory and Applications 209, article 57 (2026).

https://link.springer.com/article/10.1007/s10957-026-03008-z
Preprint version:
https://arxiv.org/html/2511.03296v1

The published introduction identifies u^2+|v| as still not understood. The abstract explicitly says the criticality analysis assumes observed matrix behavior. The published main Theorem 3.1 invokes assumption (B1); consult its components when comparing hypotheses. Published numbering differs from the preprint.

Narrative consequence: a positive theorem that derives convergence from objective structure without assumed iterate/spectral behavior makes a specific advance. It is not automatically a generalization of every nonconvex or piecewise-smooth theorem in that paper.

## Classical matrix-method lineage

Use the already delivered foundation literature packet. It distinguishes classical smooth-BFGS convergence, determinant/trace potentials and standard Gram/Schur algebra from the adjacent-degree principal-minor inequality and its specific reciprocal-growth consequences. Its Nocedal 1992 author-manuscript reading is relevant; the packet records original-source access limits for other classical references.

Nocedal author manuscript identified in the existing audit:
https://users.iems.northwestern.edu/~nocedal/PDFfiles/acta.pdf

This handoff did not newly inspect that complete manuscript. Do not label it a fresh read. A useful article sentence should credit the matrix-potential tradition and then say exactly what the new hierarchy permits; it should not disclaim ownership of every elementary inequality.

## How to use these anchors

Build a short internal table with: exact prior theorem; objective/search assumptions; outcome; gap relevant here; exact current theorem/proof; publication/version locator. Convert that table into integrated prose. Use confident theorem-specific contribution statements after reviewing the exact correspondence. Do not turn a bounded search into a blanket claim of firstness or domination over all previous results.
