# Initial literature matches and scope boundary

The first comparison establishes that the report cannot be presented as an
entirely new body of results or proof techniques. Some special cases were
published previously, several geometric ingredients have direct precedents,
and the specified deterministic search is an existing algorithm. The complete
claim-by-claim comparison remains in progress.

The comparison target is the corrected edition at commit
`e297b135bd7895fd181999235240bb2636bd4201`. Its mathematical verification status
is separate from publication priority. The source identities are recorded in
`BASELINE.json`; none of that edition is edited by this audit.

| Report item | Confirmed comparison | Consequence for attribution |
|---|---|---|
| Euclidean-norm specialization of the homogeneous/gauge results | Guo–Lewis, Corollary 4.2, proves convergence in arbitrary dimension. | Cite as an existing special case, not a newly discovered example. |
| Scalar absolute-value BFGS | Lewis–Overton, §5.1, analyzes this case. | Separate the general scalar theorem and new certificate examples from this established case. |
| D/L deterministic doubling/bisection search | D already cites Lewis–Overton Algorithm 4.6. | Its use is established, irrespective of whether the new failure construction is original. |
| A/C/U active-gradient geometry | Gebken's published Theorem 3.1 assumes behavior (B1), including iterate convergence and spectral/annihilation conditions. | Close precedent, but these conditional results do not establish the report's unconditional BFGS conclusions. |
| A finite affine-critical values | The projection formula in Bolte–Daniilidis–Lewis–Shiota suggests a direct standard corollary for the affine-critical variant. | Record the implication explicitly; do not claim the background geometric conclusion as safely novel. Final comparison will supply the argument. |
| M matrix potential arguments | Classical trace/determinant analysis is described by Nocedal, §5, with attribution to Powell and Byrd–Nocedal. | Credit the established matrix-analysis method; separately investigate the full principal-minor hierarchy and reciprocal growth. |

Guo–Lewis is absent from the corrected edition's nine external bibliography
entries and is an essential addition to the literature discussion. Gebken's
entry needs its journal publication metadata: *Journal of Optimization Theory
and Applications* 209, article 57, published 8 May 2026; the 2025 arXiv posting is
an earlier public version, not the only publication record.

A recent preprint by Rui Diao, submitted 9 September 2026, also concerns BFGS
counterexamples. Its stated smooth nonconvex setting and exact-search orbit must
be distinguished from convex nonsmooth failure with a prescribed deterministic
bracketing implementation. It falls before the search cutoff and will be
included in the final comparison, without treating preprint posting as journal
publication.

These findings establish mathematical precedents, not how an AI system actually
produced the report. Existing citations show acknowledged connections. Similar
identities, algorithms or construction strategies support a possible technique
connection; they do not establish copying or causal source use.

## Primary sources examined

1. J. Guo and A. S. Lewis, [BFGS convergence to nonsmooth minimizers of convex functions](https://optimization-online.org/2017/03/5912/), first public repository posting 19 March 2017; *Journal of Nonsmooth Analysis and Optimization* 1 (2018), Corollaries 4.2 and 4.4.
2. A. S. Lewis and M. L. Overton, [Nonsmooth optimization via quasi-Newton methods](https://cs.nyu.edu/overton/papers/pdffiles/nsoquasi.pdf), *Mathematical Programming* 141 (2013), 135–163; §2, Algorithm 4.6 and §5.1.
3. B. Gebken, [Technical Results on the Convergence of Quasi-Newton Methods for Nonsmooth Optimization](https://link.springer.com/article/10.1007/s10957-026-03008-z), *JOTA* 209:57 (2026), behavior (B1), Lemma 3.5 and Theorem 3.1. The arXiv manuscript uses different numbering.
4. J. Bolte, A. Daniilidis, A. S. Lewis and M. Shiota, [Clarke subgradients of stratifiable functions](https://arxiv.org/abs/math/0601530), first posted 22 January 2006; Proposition 4 and definable stratification results.
5. J. Nocedal, [Theory of algorithms for unconstrained optimization](https://users.iems.northwestern.edu/~nocedal/PDFfiles/acta.pdf), *Acta Numerica* 1 (1992), 199–242, §5 (author manuscript pp. 16–21). Author-hosted manuscript read.
6. R. H. Byrd and J. Nocedal, [A Tool for the Analysis of Quasi-Newton Methods with Application to Unconstrained Minimization](https://epubs.siam.org/doi/10.1137/0726042), *SIAM Journal on Numerical Analysis* 26(3) (1989), 727–739. Publisher abstract/metadata accessed; original full text was not available through this page.
7. R. Diao, [Counterexamples for BFGS-type methods under arbitrary strong Wolfe constants](https://arxiv.org/abs/2609.09686), preprint, submitted 9 September 2026.

Locator correction after full-text inspection: the matrix analysis in the Nocedal author manuscript is §5, not the initially recorded §4.1. This corrects a citation locator, not the mathematical comparison.
