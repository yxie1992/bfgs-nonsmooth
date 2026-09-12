# Publication and proof-technique audit of the corrected BFGS master report

**Cutoff: 11 September 2026, America/Los_Angeles.** The target is the corrected report at commit `e297b135bd7895fd181999235240bb2636bd4201`, identified by the hashes in [BASELINE.json](BASELINE.json).

The report contains both established mathematics and possible extensions of published BFGS results. It should not present every retained claim or proof ingredient as new. The strongest confirmed overlaps are Euclidean-norm convergence, the classical two-piece unboundedness result, affine-subgradient geometry, and standard convex/matrix calculations. The semialgebraic affine-critical-value statement also follows from established stratified projection and critical-value machinery, through the explicit argument below.

No exact match was found for the complete deterministic convex counterexamples in D/L, the principal-minor/reciprocal-growth chain in M, or the full set of objective convergence theorems in T/C/Q/U and the broader R/F/H families. This is the outcome of a documented search, not a certification of novelty. Two related questions about the precise metric-selected limit on an affine fiber remain uncertain as matters of publication priority.

The proof techniques have substantial antecedents. Some are already explicitly cited in the report; others need citations. Mathematical resemblance cannot establish which sources influenced an AI generation. This audit distinguishes observed citations, known mathematical precedents, and unknown causal provenance.

## Scope and evidence

The comparison covers **75 result and technique groups**. Every one of the corrected edition's **172 claim spans** is accounted for: 147 connect to research comparisons, and 25 are headings, notation, or execution/editorial records. Repeated inventory and verification summaries point back to the corresponding substantive results. This is not a claim that each Lean declaration is a distinct research contribution or was independently searched as one.

The [claim register](CLAIMS.json) provides statement summaries, report locations, closest sources, distinctions, confidence, and limits. The [source register](SOURCES.json) preserves version-specific access and theorem locators, including duplicate records when different packets inspected different versions of one work. The [search ledger](SEARCH_LOG.json) records executed queries. Detailed comparisons appear in the four [research packets](README.md#detailed-comparisons).

An exact comparison checks the objective class, ordinary full update, initialization, line-search conditions, differentiability requirements, iteration quantifier, and conclusion. A theorem for a modified, proximal, memoryless, partitioned, or stochastic method does not establish a theorem about unmodified full BFGS. Similarly, value convergence, distance to the solution set, and convergence to a particular point are different conclusions.

The substantive positive results concern admissible infinite runs with differentiable accepted points and fixed Armijo–weak-Wolfe constants. They do not automatically guarantee differentiable acceptance on every search ray. The negative constructions make stronger implementation-specific assertions about accepted and rejected queries. Neither matrix convergence nor an iterate limit may be imported as an extra assumption into a comparison that claims to establish them.

## Results with established precedents

| Report content | Finding | Attribution consequence |
|---|---|---|
| Euclidean norm in arbitrary finite dimension, included in H/R | Guo–Lewis, Corollary 4.2, already gives full-BFGS convergence | Credit the existing special case; reserve any extension claim for the broader theorem. |
| Absolute value and two-piece common-tilt examples | Lewis–Overton treats absolute value; Xie–Wächter gives finite detection of unbounded descent in the relevant two-piece class | Preserve the earlier conclusions and their algorithmic quantifiers. |
| Equal-rate descent and common tangential subgradient | Established VU/partial-smoothness geometry | Present this as background used in later BFGS analysis. |
| Semialgebraic affine-critical-value finiteness | Standard consequence of stratified subgradient projection plus definable critical-value finiteness | Explain the affine-hull inference; do not claim a new Sard phenomenon. |
| Two-by-two nuclear-norm proximal optimizer | Specialization of singular-value thresholding | Separate the known optimizer from the report's radial-certificate obstruction. |
| BFGS update identities, Bregman expression, Euler identity and elementary quadratic-form deductions | Established algebra and convex analysis | A new formal proof does not establish mathematical priority. |

The first comparison is supported by [Guo–Lewis, Corollary 4.2](https://people.orie.cornell.edu/aslewis/publications/18-nonsmooth.pdf); the scalar and two-piece comparisons by [Lewis–Overton, §5.1](https://cs.nyu.edu/overton/papers/pdffiles/nsoquasi.pdf) and [Xie–Wächter, Theorem IV.1](https://arxiv.org/html/1712.08571v1). The geometry and nuclear-norm comparisons are developed in the [geometry packet](packets/geometry_C_Q_U_A.md) and [positive-families packet](packets/positive_R_F_H_G.md), with primary theorem locators.

### The affine-critical-value inference

The distinction between Clarke criticality and affine criticality matters. For a finite convex function, zero in the affine hull of the subdifferential need not lie in the subdifferential itself. Therefore a theorem about Clarke critical values cannot simply be quoted with “affine” substituted.

The needed deduction instead uses a compatible finite definable stratification. At a point on a stratum, every subgradient has the same tangential projection: the gradient of the smooth restriction of the objective to that stratum. If an affine combination of subgradients is zero, projecting the combination shows that this stratum gradient is zero. Definable critical-value finiteness on finitely many strata then gives finitely many affine-critical values. Constancy on critical components follows using definable paths and a compatible subdivision. The low-value gap is the separation of a finite set of values from the attained minimum. This is our explicit inference from [Bolte–Daniilidis–Lewis–Shiota, Proposition 4, Lemma 8 and the Corollary 9 argument](https://arxiv.org/pdf/math/0601530), rather than an assertion that their printed corollary literally uses affine criticality.

## Negative results: exact assumptions prevent false matches

D and L make different claims and must remain separate.

D constructs one coercive maximum of four globally convex C²,¹ branches, with a unique nonsmooth minimizer and bad starts arbitrarily near it under fixed identity initialization. The actual unit-first doubling/bisection search has differentiable accepted and rejected queries and nonstationary limits. Its constants cover fixed pairs with `0 < c1 ≤ 1/3` and `c1 < c2 < 1`. There is no uniform positive lower-curvature bound.

L supplies a strongly convex local-failure construction with four C¹,¹ branches and a common initial matrix, reducible once to identity. The first three branches lack second differentiability at the accumulation point; the fourth is a smooth quadratic-plus-affine branch. A separate version has a countable piecewise-affine nonsmooth part and a constant positive definite classical Hessian wherever it exists. L uses the fixed pair `(c1,c2) = (10⁻⁴, 1/2)`. These statements do not combine into local failure for a strongly convex maximum of finitely many C² branches.

The simpler global examples are also distinct: D retains a coercive affine maximum, while L retains a positive quadratic plus a three-affine maximum. A nonstationary limit in the latter example is not a failure arbitrarily close to its true minimizer.

| Earlier negative result | Material difference from D/L |
|---|---|
| Lewis–Overton's 2008 convex polyhedral example | A conceptual subgradient/exact-search extension permits nondifferentiable and null steps and singular later matrices. |
| Lewis–Zhang's stationary limit with descent directions | The limit remains Clarke stationary; this is not convex nonstationary convergence. Exact proof comparison is access-limited. |
| Asl–Overton's fixed-bracketing failure | Scaled memoryless BFGS, rather than the full update. |
| Mascarenhas and Dai smooth counterexamples | Global nonconvexity and differing orbit/search constructions. Compact sublevels or search-line convexity do not imply global convexity. |
| Diao's September 2026 planar example | Smooth nonconvex objective, an escaping trajectory and unbounded sublevels, with first-local-minimizer exact search. |

Primary links, precise versions, theorem locators and access limits for this table are in the [negative packet](packets/negative_D_L.md). Diao's preprint was first submitted on **9 September 2026**, within the cutoff. Its neighboring result is relevant recent work, but does not duplicate the convex deterministic constructions. [Diao, Theorem 1 and §5.2](https://arxiv.org/html/2609.09686v1)

The construction strategy itself has precedents. Prescribing a finite algebraic seed or periodic/scaled orbit, imposing update identities, and then building an objective realizing it is prominent in [Mascarenhas's divergence constructions](https://www.scielo.br/j/cam/a/JBFzLzr4PNdcqKHJRRS4mHf/). The precise convex interpolation, all-query containment, and local accumulation properties require their own comparison. Likewise, a stable-manifold argument is classical and already acknowledged by L's Dyatlov citation; it is not a newly invented proof principle.

These existential bad starts also do not settle the stronger almost-sure random-initialization question posed in Lewis–Overton's final discussion. No exact D/L theorem match was located, but “first counterexample to nonsmooth BFGS convergence” would be an inaccurate description of the historical landscape.

## Positive results: broader theorem versus known special case

### Matrix and certificate mechanisms

M's principal-minor hierarchy must be compared at the matrix level. Its special determinant endpoint is classical. The proposed additional content is the adjacent-degree inequality for actual principal determinants in arbitrary dimension and its quantitative consequences. For infinite admissible full-BFGS runs with bounded accepted gradients and fixed weak-Wolfe parameters, vanishing predicted decreases give reciprocal-mean divergence; summability gives a finite-horizon estimate and superquadratic reciprocal-sum growth. An assumed scalar hierarchy would not establish that chain for BFGS.

No exact matching chain was found. Its ingredients are established: Gram determinants, Schur complements, Cauchy–Binet, weighted potentials, AM–GM and tail-limit arguments. Trace and determinant reasoning in BFGS long predates this report. [Nocedal, §5](https://users.iems.northwestern.edu/~nocedal/PDFfiles/acta.pdf) is a directly inspected primary exposition; the [foundation packet](packets/foundation_M_T_G.md) records the older and modern comparisons without transferring smooth hypotheses.

The moving-frame identity is algebraic, while the visibility, secant, transport and residual-energy bounds are substantive conditions. T's objective theorem derives convergence from a PSD comparison field on positive bands. The field may be singular, discontinuous and unbounded, and transport is projected away from the executed step. No exact theorem with these quantifiers was found. Its normalization has a standard multiplicative-error antecedent in [Combettes–Vũ, Lemmas 2.2–2.3](https://pcombet.math.ncsu.edu/nonan3.pdf), whose own metric convergence theorem has additional coercivity/boundedness conditions.

G's pointwise feasibility and incoming-jump arguments explain limitations of that certificate. Elementary polar-set and PSD-seminorm calculations should be identified as such. A proof that every field in one certificate class fails is not a counterexample to BFGS convergence. A proof that one canonical field fails is narrower still.

### Objective families and geometry

| Report family or mechanism | Closest comparison and current assessment |
|---|---|
| R radial smoothness, inward-error equivalence, finite C¹,¹ partitions and mixed gauges | Exact radial formulations were not located. Broader objective applications include known norm cases and use established convex estimates. |
| F centered smooth-plus-sublinear objectives | Possible extension. For `u² + |v|`, Guo–Lewis gives only a weaker subsequential conclusion, explicitly leaving full convergence open there. |
| F increasing gauge profiles, explicit inactive-cell basins and accepted-iteration rates | No complete matching package found. A smooth-rate result on a narrower class is not the same nonsmooth theorem. |
| H finite convex degree-one homogeneous objectives | The value dichotomy is broader than the known Euclidean and two-piece cases. General noncompact iterate convergence in higher effective rank remains outside the report's theorem. |
| C planar affine-critical clustering and local convergence | Possible extension of existing nonsmooth geometry. No matching unconditional full-BFGS statement found. |
| Q arbitrary finite parabolic maximum, including flat contours | No exact full-family convergence/certificate theorem found. |
| U fixed-normal and tangentially smooth classes | Existing VU/partial-smoothness geometry is relevant; the report derives restricted matrix control instead of assuming identification or matrix convergence. |
| Scalar G and the examples outside radial/transported certificates | The general positive-metric scalar result and the exact obstruction examples were not found in matching published form. Known absolute-value convergence must still be cited. |

The weaker result for `u² + |v|` is [Guo–Lewis, Corollary 4.4](https://people.orie.cornell.edu/aslewis/publications/18-nonsmooth.pdf). This comparison concerns what that paper proves; an old open-question statement does not certify the absence of all later work.

The closest recent nonsmooth quasi-Newton article is now a journal publication: [Gebken, May 2026](https://link.springer.com/article/10.1007/s10957-026-03008-z). Its final Theorem 3.1 assumes an iterate limit and specified matrix behavior. It therefore cannot replace a proof that derives these conclusions. Its normal-space analysis is nevertheless relevant intellectual background. The report's C/U geometric arguments also connect to established partial smoothness and newer active-manifold regularity, while bundle Newton and proximal VU algorithms perform additional operations. Those distinctions are detailed in the [geometry packet](packets/geometry_C_Q_U_A.md).

### Noncompact smooth antecedents and the fiber question

Schöpfer's 2016 full-BFGS result is a meaningful antecedent that permits nonunique and unbounded minimizer sets. The institutional manuscript was obtained and its relevant proof inspected after an initial abstract-only comparison. Under its Lipschitz-gradient and restricted-strong-convexity assumptions, Theorem 3.7 proves linear objective-gap and distance-to-solution-set bounds. It does not give the report's explicit initialization-dependent affine-fiber selector. The stronger iterate statement in Theorem 3.4 requires uniform matrix and inverse bounds. [Schöpfer, §3](https://uol.de/f/5/inst/mathe/Preprints/2016-03.pdf)

F/H's rectangular projection and metric-selection formula is a natural extension of affine invariance. Whether the exact selector was already stated elsewhere remains unresolved. This is an uncertainty about priority, not a missing Lean proof or a reason to describe a known smooth theorem as identical to the nonsmooth result.

## Technique lineage and citation changes

The following distinctions should appear in a future bibliographic edition. The concrete location-by-location proposals are in [CITATION_PLAN.md](CITATION_PLAN.md).

| Technique | Existing lineage | What may remain specific to this report |
|---|---|---|
| Full-BFGS trace/determinant potentials | Powell; Byrd–Nocedal; Nocedal; recent Jin–Jiang–Mokhtari and Schöpfer analyses | All-principal-minor hierarchy and its precise reciprocal-budget consequences. |
| Smooth convex secant estimates | Baillon–Haddad/cocoercivity | Deriving objective-specific radial or tangential bounds with the correct local domain. |
| Summable transport expansion | Classical multiplicative-error/product normalization | The singular projected PSD-field criterion and its applications. |
| Common tangent projection and normal gradient jumps | VU decomposition and partial smoothness | BFGS-specific transport, accessibility and residual estimates. |
| Stable positive multipliers | Nondegenerate smooth-max geometry | The resulting unconditional BFGS basin theorem. |
| Stratified critical-value arguments | Bolte–Daniilidis–Lewis–Shiota | A disclosed affine-hull corollary/reproof. |
| Normal-angle formulas | Classical support-function geometry | Gluing the comparison field and controlling transport near planar corners. |
| Algebraic orbit followed by objective construction | Mascarenhas and related divergence work | The exact convex branches, deterministic query tree and local bad-start embedding. |
| Hyperbolic stable manifold | Classical dynamics, including the cited Dyatlov notes | The concrete normalized BFGS return map and certified constants. |
| Preconditioned residual/box validation | Established validated numerics, including Rump | The exact rational seed certificate and its Lean implementation. |

The audit found actual citations for several ingredients, including Lewis–Overton's line search, Xie–Wächter's formulation and special case, Dyatlov's dynamics, partial smoothness, and Bregman terminology. These are observed acknowledgments. For newly identified precedents, attribution is justified by mathematical relationship; a claim that an AI copied or relied on a particular paper is not justified by the available evidence.

## Recent work and bibliographic corrections

The bibliography needs more than additional titles. Versions, authors and publication dates matter:

- Guo–Lewis is a published 2018 article, with a March 2017 public precursor, and should be added for the norm and smooth-extension comparisons.
- Gebken's November 2025 preprint now has a **May 2026** JOTA publication. The final main theorem is numbered 3.1; the inspected preprint uses 3.10.
- The published successor to the two-author Lewis–Liang 2018 preprint has **Lewis, Liang and Tian** as authors (2022). Preprint theorem numbers must remain version-specific. [Publisher record](https://epubs.siam.org/doi/10.1137/19M1237909)
- The modern exact-line-search rate paper appeared online in August 2025 and is assigned to a 2026 journal volume. The Armijo–Wolfe rate paper is NeurIPS 2024. Both concern smooth objectives. [Exact-search publication](https://link.springer.com/article/10.1007/s10107-025-02256-7), [Armijo–Wolfe paper](https://proceedings.neurips.cc/paper_files/paper/2024/file/1e269abc604816c35f600ae14b354efd-Paper-Conference.pdf)
- Diao's September 2026 preprint belongs in current negative related work, with its preprint status retained.

Publisher digitization dates must not be mistaken for original publication dates. Nocedal's article is from 1992 and Byrd–Nocedal's from 1989 despite much later online dates on publisher pages. Internal labels such as `[SM]`, `[SD]` and `[SU]` identify report topics, not independently published historical sources.

## Classification and remaining uncertainty

The register uses six labels. `existing_result` identifies an established result; `known_special_case` identifies a justified specialization or corollary; `standard_deduction` identifies elementary mathematics without claiming an exact published formulation. `possible_extension` records a narrower related theorem and a material additional scope in the report. `no_exact_match_found` records a search outcome. `unresolved` is reserved for a specific undecided comparison or an explicitly open report question. Confidence applies to the stated comparison, not to proof of historical completeness.

Searches covered primary author papers, publisher articles, arXiv, institutional manuscripts and references in the closest works, including 2025–2026 material. Original full proofs were unavailable for some classical or adjacent records, including Powell 1976, Byrd–Nocedal 1989, Griewank 1991, and portions of the older negative literature. Access levels are explicit; no unread proof is used to assert exact equivalence. Unindexed manuscripts, dissertations, other languages and subscription archives may contain further precedents.

The audit completes the documented comparison of the corrected report. It does not certify publication priority, independently prove every external paper, establish Lean's consistency, or reconstruct AI training/source history. The frozen report, Lean sources and verification records remain unchanged. This literature supplement supplies the attribution evidence and cautious claim wording needed for subsequent scholarly use.
