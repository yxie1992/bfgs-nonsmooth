# Literature comparison: R, families, H, and scalar G

Research date: 11 September 2026. This packet compares substantive results in the corrected edition with primary literature. It does not change or recertify the Lean proofs. The [JSON register](positive_R_F_H_G.json) contains 31 claim records, report span and line locators, input hashes, source-access statements, detailed comparisons, and search records. G spans 2–7 are covered by the other packet.

## Principal findings

**Some report subclaims are already published.** Guo–Lewis, Corollary 4.2, proves arbitrary-dimensional full-BFGS convergence on the Euclidean norm. Its Corollary 4.4 gives a weaker result for the quadratic-plus-absolute-value example. The report should cite this paper when discussing the broader centered-family claim; it is absent from the edition bibliography. [Guo–Lewis, published manuscript](https://people.orie.cornell.edu/aslewis/publications/18-nonsmooth.pdf)

The nuclear-norm example's optimizer is the direct two-by-two specialization of singular-value thresholding. The report's radial obstruction is a separate assertion and should not be credited as a new optimizer calculation. [Cai–Candès–Shen, Theorem 2.1](https://arxiv.org/html/0810.3286v1)

**The closest recent nonsmooth paper is now published.** Gebken's article appeared on 8 May 2026, after its November 2025 preprint. Its convergence argument assumes an iterate limit and specific inverse-matrix behavior. It therefore does not establish the report's unconditional claims. Journal theorem numbering differs from the preprint. [Gebken, JOTA 209, article 57](https://link.springer.com/article/10.1007/s10957-026-03008-z)

**Positive results need precise scope comparisons.** Xie–Wächter already proves finite termination exposing unboundedness for the two-piece common-tilt example. The report's many-piece infinite-run assertion is broader in the family and weaker on that specialization. Invertible affine invariance is also explicit in that paper. [Xie–Wächter, Theorems II.1 and IV.1](https://arxiv.org/html/1712.08571v1)

The report's all-ray obstruction concerns full-space differentiability at the accepted point. Scalar ray differentiability in a line-search existence theorem does not supply that condition. The report's scalar existence example is within established scalar Armijo–weak-Wolfe theory. Its arbitrary-positive-metric scalar convergence and accumulating-kink certificate example were not located in exact published form. [Lewis–Overton, Theorem 4.5 and Proposition 4.11](https://cs.nyu.edu/overton/papers/pdffiles/nsoquasi.pdf)

## Claim register

`existing_result` means an identified existing result. `known_special_case` means a direct specialization. `possible_extension` means the closest inspected work proves a narrower conclusion under different scope or hypotheses. `no_exact_match_found` reports a search outcome, **not novelty**. `unresolved` marks a concrete remaining priority comparison.

| ID suffix | Edition span(s) | Classification | Report claim being compared |
| --- | --- | --- | --- |
| R-BREGMAN | R 2 | `existing_result` | Standard Bregman/supporting-plane expression and symmetrization |
| R-RS-IR | R 3, R 4, R 5 | `no_exact_match_found` | Radial smoothness and inward quadratic error equivalence |
| R-CENTRAL | R 6 | `no_exact_match_found` | Central-difference formulation on nested bands |
| R-SP | R 7 | `no_exact_match_found` | Supporting-plane intercept and radial identity |
| R-HOMOGENEOUS-IDENTITY | R 7, H 9 | `existing_result` | Euler identity and zero radial correction |
| R-FOURPIECE-SP | R 7 | `no_exact_match_found` | Four-piece failure of supporting-plane criterion |
| R-PLQ | R 8 | `possible_extension` | Finite polyhedral C1,1 pieces and local BFGS convergence |
| R-GAUGES | R 10 | `possible_extension` | Centered gauges and mixed powers |
| R-RESIDUALS | R 11, R 12, F 4 | `possible_extension` | Residual and affine-group families |
| R-BRANCH | R 13 | `no_exact_match_found` | Finite-branch radial compatibility and obstruction |
| R-PARABOLA | R 15 | `no_exact_match_found` | Curved switching surface obstructs radial certificate |
| R-SPECTRAL-OPTIMUM | R 16 | `known_special_case` | Two-by-two nuclear-norm proximal optimizer |
| R-SPECTRAL-OBSTRUCTION | R 16 | `no_exact_match_found` | Nuclear/spectral rotated-pair noncoverage |
| F-CENTERED | F 1 | `possible_extension` | Global centered smooth-plus-sublinear family |
| F-TRANSFORM | F 2 | `possible_extension` | Increasing smooth profile of coercive gauge |
| F-BASIN | F 3 | `no_exact_match_found` | Explicit inactive-cell objective basin |
| F-LIFT | F 4, H 16 | `unresolved` | Rectangular reduction and metric-selected affine-fiber limit |
| F-RATES | F 5 | `no_exact_match_found` | Three accepted-iteration rate bounds |
| F-MATRIX | F 6 | `no_exact_match_found` | Explicit matrix limit on geometric vertical run |
| F-LINE-EXISTENCE | F 6 | `known_special_case` | Tilted scalar absolute-value line-search existence |
| F-LINE-OBSTRUCTION | F 6 | `no_exact_match_found` | Five-piece failure of differentiable all-ray acceptance |
| H-VALUE | H 3, H 10, H 11, H 12 | `possible_extension` | Homogeneous values converge to zero or minus infinity |
| H-EUCLIDEAN | H 12, R 10 | `existing_result` | All-dimensional Euclidean norm convergence |
| H-AFFINE | H 4, H 13, H 14 | `possible_extension` | Origin in affine span of recurrent slopes |
| H-PLANAR | H 5, H 17, H 18, H 19 | `no_exact_match_found` | Planar/rank-two finite-value iterate convergence |
| H-FLAT | H 20 | `unresolved` | Relative-interior slope hull and noncompact flat-fiber limit |
| G-SCALAR-CERT | G 8 | `no_exact_match_found` | Scalar certificate equivalent to eligible-pair quotient bound |
| G-SCALAR-CONV | G 9 | `possible_extension` | Scalar AW convergence for every positive metric |
| G-SHIFTED | G 9 | `no_exact_match_found` | Shifted absolute-value failure of certificate necessity |
| G-ACCUMULATING | G 10 | `no_exact_match_found` | Accumulating-kink example defeats every local certificate |
| G-FINITE | G 11 | `no_exact_match_found` | Finite samples cannot refute freely quantified continuum certificate |

The homogeneous value theorem does not prove general iterate convergence in effective gradient rank three or higher. The geometric and spectral examples disprove stated certificates; they do not establish BFGS trajectory failure. The family-rate claims count accepted iterations, while numerical function trials and particular line-search rules can have different rates. These distinctions are preserved in the JSON comparisons.

## Proof-technique antecedents

The centered-family proof uses the established convex smooth-gradient cocoercivity inequality. An accessible primary proof is [Wachsmuth–Wachsmuth, Theorem 2.5](https://arxiv.org/html/2204.00282v1). This is a component of the argument, not evidence that the resulting nonsmooth BFGS theorem was previously established.

Guo–Lewis's proof extends the objective smoothly while preserving its values on a band and then applies Powell. The report instead uses its radial/certificate and matrix-summability chain. Similar compact-band localization is an antecedent, but the proof routes must not be identified without this distinction. [Guo–Lewis, Theorem 4.1](https://people.orie.cornell.edu/aslewis/publications/18-nonsmooth.pdf)

The reflected-matrix calculations and scalar recurrences in the two-piece analysis are concrete predecessors for studying recurrent slopes with full BFGS. Their existing finite-termination argument should be credited independently of the report's many-piece affine-span derivation. [Xie–Wächter, §§III–IV](https://arxiv.org/html/1712.08571v1)

The existing R citation agrees with Banerjee et al., Definition 1, for the Bregman expression; the report only needs a differentiable second endpoint and ordinary convexity. This is established supporting-plane calculus. [Primary definition](https://www.jmlr.org/papers/volume6/banerjee05b/banerjee05b.pdf)

Standard Bregman terminology, convex supporting planes, homogeneous Euler identities, positive-semidefinite kernel arguments, and finite-extremum bounds should be treated as background. Similarity to established arguments does **not** determine which sources generated AI-produced text. Historical dependence cannot be recovered from mathematical similarity alone.

## Bibliographic and access corrections

- Guo–Lewis: first located public posting 19 March 2017; journal publication 8 May 2018, DOI 10.1137/17M1121883. [Publication record](https://epubs.siam.org/doi/10.1137/17M1121883)
- Lewis–Overton: the final article is *Nonsmooth optimization via quasi-Newton methods*, online 16 February 2012, journal volume 141 (2013), DOI 10.1007/s10107-012-0514-2. Older predecessor numbering is different. [Publisher record](https://link.springer.com/article/10.1007/s10107-012-0514-2)
- Gebken: replace a preprint-only bibliography entry with the 2026 publication while retaining version-specific locators. [Publisher record](https://link.springer.com/article/10.1007/s10957-026-03008-z)
- The 2018 Lewis–Liang arXiv version of *Partial smoothness and constant rank* has two authors. The published successor adds **Tonghua Tian**: SIAM Journal on Optimization 32(1), 276–291, online 17 March 2022, DOI 10.1137/19M1237909. Do not transfer theorem numbering between versions without checking. [Publisher record](https://epubs.siam.org/doi/10.1137/19M1237909)

Griewank's March 1991 paper is a relevant differentiable predecessor. Its abstract discusses partitioned BFGS, Lipschitz gradients, a Byrd–Nocedal potential, and damping for singular elements. The earlier 1987 report's “semi-smooth” title does not establish convergence on objectives with gradient jumps. Only the publisher abstract and bibliographic history were available, so precise theorem-level comparison of the smooth subclass remains open. [Griewank, primary publisher](https://link.springer.com/article/10.1007/BF01594933)

The Schöpfer access limitation is now resolved using the full institutional manuscript. Theorem 3.7 has smooth restricted-strong-convex hypotheses and concludes linear value gap and distance to the solution set; its trace/determinant/AM–GM proof is a technique antecedent. Theorem 3.4 additionally assumes uniform matrix control for iterate convergence. Neither identifies the report's metric selector. The two selector-priority entries remain `unresolved`. [Schöpfer, full primary manuscript](https://uol.de/f/5/inst/mathe/Preprints/2016-03.pdf)

Subgradient-based subBFGS/subLBFGS methods are modified algorithms and cannot substitute for the report's actual-gradient full-BFGS premise. This screening is based on the primary abstract, not a complete proof audit. [Yu–Vishwanathan–Günter–Schraudolph](https://www.jmlr.org/papers/v11/yu10a.html)

## Evidence and limits

The JSON records existing report citations separately: R cites BB and XW; H cites XW, including its stronger two-piece conclusion; G cites XW and LL. These are observed citations, not inferred provenance. The existing bibliography's Gebken entry is outside these chapter-local citation observations.

Primary theorem/proof readings cover the closest Guo–Lewis, Lewis–Overton, Gebken, Xie–Wächter, Schöpfer, smooth-gradient, and nuclear-norm results. Abstract-only leads and inaccessible proofs are explicitly marked. No third-party full text or PDF is redistributed in this packet. No paper has been inserted as a Lean axiom. Search results establish neither exhaustive historical coverage nor novelty; the exact rank-deficient metric-selection antecedent remains a concrete open literature check.

Peer-review refinements on 2026-09-11 clarify profile smoothness only on positive arguments, nonnegative powered gauges, and neighborhood regularity of the centered smooth summand. LO13’s accumulating-corner line-search example is now recorded as a technique antecedent for G; its conclusion is different. S16 full-text access was resolved after the first packet version.
