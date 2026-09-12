# Literature and technique audit: C, Q, U and A

As of 2026-09-11. This is a bounded online comparison of the corrected report, not a certification of novelty or of the causal provenance of AI-generated text. Report hashes, exact claim-span links, search queries and source locators are in [the JSON packet](geometry_C_Q_U_A.json). No report or Lean source was changed.

The clearest existing material is the VU/partial-smoothness geometry, positive-multiplier stability, cocoercivity, and the stratified critical-value argument. No exact published theorem was found for the complete C, Q or U full-BFGS statements with all their current hypotheses and run quantifiers. That is a search outcome, not a priority claim.

## Primary sources and exact inspection scope

- **geom_Gebken2026** — Bennet Gebken, [Technical Results on the Convergence of Quasi-Newton Methods for Nonsmooth Optimization](https://link.springer.com/article/10.1007/s10957-026-03008-z). First public date established here: 2025-11-05; journal date: 2026-05-08. DOI: `10.1007/s10957-026-03008-z`. Inspected: Published Assumptions (A1), (A2.1)-(A2.2), Behavior (B1.1)-(B1.5); Published Lemmas 3.1-3.5 and Theorem 3.1; arXiv v1 main criticality cross-reference Theorem 3.10; Published Section 4 exploration theorem; arXiv v1 Theorem 4.15; Remark 3.1 / arXiv Remark 1 links normal space to VU theory and partial smoothness.
- **geom_GuoLewis2018** — Jiayi Guo, Adrian S. Lewis, [Nonsmooth Variants of Powell’s BFGS Convergence Theorem](https://arxiv.org/pdf/1703.06690v1). First located public date: 2017-03-19 on Optimization Online; arXiv v1: 2017-03-20; journal publication: 2018-05-08. The following locators refer to arXiv v1. DOI: `10.1137/17M1121883`. Inspected: Definition 2.1 and equations (2.2)-(2.5), pp. 2-3; Theorem 3.3, Corollaries 3.5-3.6, pp. 4-7; Theorem 4.1 and Corollary 4.2, pp. 7-9.
- **geom_LewisWylie2019** — Adrian S. Lewis, Calvin Wylie, [A simple Newton method for local nonsmooth optimization](https://arxiv.org/pdf/1907.11742). First public date established here: 2019-07-26; journal date: not established. DOI: `10.48550/arXiv.1907.11742`. Inspected: Definition 5.2, pp. 13-14; Propositions 5.5-5.6 and their proofs, pp. 15-16 in PDF one-based pagination; Algorithm 2.2; Theorem 5.11, pp. 18-19; Section 3.6 and Theorem 4.1 (SQP interpretation).
- **geom_Lewis2002** — Adrian S. Lewis, [Active Sets, Nonsmoothness, and Sensitivity](https://people.orie.cornell.edu/aslewis/publications/03-active.pdf). First public date established here: 2002-11-14 (electronic publication; earlier public draft not established); journal date: 2002-11-14 online; volume 13(3), 702-725 often cited as 2003. DOI: `10.1137/S1052623401387623`. Inspected: Propositions 2.1, 2.2 and 2.4, journal pp. 706-708; Definition 2.7 and Note 2.9, journal pp. 708-709; Theorem 6.1 (U–V decomposition), journal pp. 720-721.
- **geom_LewisLiang2018** — Adrian S. Lewis, Jingwei Liang, [Partial smoothness and constant rank](https://people.orie.cornell.edu/aslewis/publications/1807.03134.pdf). First public date established here: 2018-07-09. Published successor: Lewis–Liang–Tian, SIAM Journal on Optimization 32(1), 276–291, online 2022-03-17, DOI `10.1137/19M1237909`. The following locators remain for the two-author preprint. DOI: `10.48550/arXiv.1807.03134`. Inspected: Introduction equation (1.1), pp. 1-2; Proposition 3.4 (identifiability); Definition 5.4 and Theorem 5.5, pp. 12-13; Section 6 (primal-dual splitting).
- **geom_BDLS2007** — Jérôme Bolte, Aris Daniilidis, Adrian S. Lewis, Masahiro Shiota, [Clarke Subgradients of Stratifiable Functions](https://arxiv.org/pdf/math/0601530). First public date established here: 2006-01-22; journal date: 2007-05-29 online; SIAM Journal on Optimization 18(2), 556-572. DOI: `10.1137/060670080`. Inspected: Proposition 4 (projection formula), pp. 6-7; Remark 4 and Corollary 5, pp. 7-8; Lemma 8 and Corollary 9, pp. 9-10; Corollary 9 proof and its cited smooth definable critical-value argument.
- **geom_LSS2019** — Shuai Liu, Claudia Sagastizábal, Mikhail Solodov, [Subdifferential Enlargements and Continuity Properties of the VU-Decomposition in Convex Optimization](https://pages.cs.wisc.edu/~solodov/sss17isnm.pdf). First public date established here: not established; journal date: 2019-03-30 (book chapter publication). DOI: `10.1007/978-3-030-11370-4_4`. Inspected: Section 2.1 equations (2.1), common U-gradient, pp. 3-4; Section 3.1 Proposition 3.1 and Remark 3.2, pp. 7-8; Section 3.2 opening discussion, p. 8; Publisher acknowledgments credit Alfredo N. Iusem for the two Remark 3.2 counterexamples.
- **geom_BauschkeCombettes2010** — Heinz H. Bauschke, Patrick L. Combettes, [The Baillon–Haddad Theorem Revisited](https://arxiv.org/pdf/0906.0807). First public date established here: 2009-06-04; journal date: 2010, Journal of Convex Analysis 17(3-4), 781-787; exact day not established. DOI: `10.48550/arXiv.0906.0807`. Inspected: Theorem 1.1; Theorem 2.1; Theorem 3.3 (open convex domain, C²), p. 6; Remark 3.5.
- **geom_Bogosel2023** — Beniamin Bogosel, [Numerical Shape Optimization Among Convex Sets](https://arxiv.org/pdf/2203.06981). First public date established here: 2022-03-14; journal date: 2022-11-07 online; Applied Mathematics & Optimization 87, article 1 (2023). DOI: `10.1007/s00245-022-09920-w`. Inspected: Section 2, equation (4) and the following derivative identity, p. 5; Reference to Schneider, Convex Bodies, Section 1.7.

The source summaries and access qualifications are recorded once in JSON. Particularly, Gebken is a **published May 2026 article**, not merely a November 2025 preprint. Its final criticality theorem is numbered 3.1; the arXiv cross-reference uses 3.10. The Lewis–Liang 2018 preprint is distinguished from the [published Lewis–Liang–Tian 2022 successor](https://epubs.siam.org/doi/10.1137/19M1237909); preprint theorem numbers are not assigned to the final version.

## Claim-level comparison

| Claim | Corrected spans | Assessment |
|---|---|---|
| geom_A_equal_rate | A.span.1, C.span.3 | existing_result |
| geom_A_rank_loss | A.span.2 | possible_extension |
| geom_A_local_correctness | A.span.3, C.span.11 | known_special_case |
| geom_A_finite_values | A.span.4 | known_special_case |
| geom_A_conjecture | A.span.5 | unresolved |
| geom_C_cluster | C.span.2, C.span.4, C.span.9, C.span.10 | possible_extension |
| geom_C_local_convergence | C.span.2, C.span.11 | possible_extension |
| geom_C_tame_basin | C.span.12 | possible_extension |
| geom_C_field | C.span.5, C.span.6, C.span.7, C.span.8, C.span.9 | possible_extension |
| geom_C_any_dim | C.span.15 | known_special_case |
| geom_C_transport_warning | C.span.15 | no_exact_match_found |
| geom_C_quadratic_basin | C.span.13 | no_exact_match_found |
| geom_C_RS_separation | C.span.14 | no_exact_match_found |
| geom_Q_family | Q.span.2 | no_exact_match_found |
| geom_Q_certificate | Q.span.3, Q.span.4, Q.span.5, Q.span.6 | no_exact_match_found |
| geom_Q_RS_separation | Q.span.7 | no_exact_match_found |
| geom_U_single_interface | U.span.2 | possible_extension |
| geom_U_parallel_interfaces | U.span.4 | possible_extension |
| geom_U_composite | U.span.3, U.span.11 | possible_extension |
| geom_U_frame_proof | U.span.5, U.span.6, U.span.7, U.span.8, U.span.9, U.span.10 | no_exact_match_found |
| geom_U_spikes | U.span.12, U.span.13 | no_exact_match_found |
| geom_U_nonsplitting | U.span.14 | no_exact_match_found |

The JSON gives the exact statement, comparison, source IDs, techniques, confidence, and limits for every row. Four distinctions deserve explicit mathematical explanation.

## Why the affine-critical Sard result is already a standard corollary

For a finite convex semialgebraic F, take a finite compatible definable stratification on which the projection formula holds. At p in a stratum X, each subgradient g has the same tangential projection ∇(F|X)(p). If Σ λ_i g_i=0 and Σ λ_i=1, linearity of projection gives 0=Σ λ_i ∇(F|X)(p)=∇(F|X)(p). Thus every affine-critical point is a critical point of a smooth stratum restriction. Finite definable stratification together with definable critical-value finiteness yields finitely many such objective values. A compatible subdivision into finitely many path-connected pieces, or the report’s lifted-path argument, also yields constancy along critical components. The low-level gap follows by separating the finite set of values above the attained minimum.

This is an inference from [BDLS Proposition 4, Lemma 8 and Corollary 9](https://arxiv.org/pdf/math/0601530). The published corollary literally says Clarke critical values; using only that narrower assertion would leave a gap because zero in an affine hull need not belong to the convex subdifferential. The linear-projection argument is what justifies the affine-critical upgrade. Accordingly A.span.4 should be credited as a corollary/reproof of established tame geometry, not marketed as an independent new Sard phenomenon.

## Known ingredients versus candidate new BFGS applications

A.span.1 uses the established VU decomposition. A.span.3 and the nondegenerate part of C use stable augmented gradient systems and strict complementarity; compare [Lewis–Wylie Propositions 5.5–5.6](https://arxiv.org/pdf/1907.11742). Those elementary geometric facts must be credited even though their use inside a full-BFGS contradiction may be different.

C.span.7–8 uses the classical angular expression h n+hθ T and its tangential derivative. [Bogosel Section 2, equation (4)](https://arxiv.org/pdf/2203.06981) is a readily checkable modern primary reference recalling this formula. C constructs h as a glued comparison function and does not claim it is a convex support function; that qualification is mathematically significant. The candidate extra content is joining the corner velocities on the whole cluster neighborhood and controlling log determinant transport by d.

C.span.15 combines rank-stable affine projection, partitions of unity and a buffered convex gradient estimate. Those are established analytical mechanisms. Its smooth three-dimensional warning correctly excludes only the canonical rank-one field, and cannot refute convergence of BFGS on the same positive-definite quadratic. The projection removes just the executed-step direction, so tangent-space invariance alone cannot supply transport in higher dimension.

C.span.13 belongs to a familiar strongly convex maximum-of-quadratics model, while its exact coefficients and certified 1/100 basin were not found. C.span.14 proves nonnecessity of the report’s RS criterion on eligible crossing pairs. Q.span.7 gives a similar statement for each allowed Armijo–weak-Wolfe parameter pair, with different initial metrics for different epsilon. Neither is an infinite bad BFGS trajectory or a separation from every published theory.

U’s fixed tangent space recalls VU/partial smoothness, but standard identification results cannot simply be applied: they require suitable graph/subgradient convergence, and a differentiable accepted sequence approaching |v| need not have gradients tending to zero. U derives restricted matrix control and allows its full normal curvature to blow up. Its spike examples are not proof that every prior geometric certificate fails; they establish the stated RS separation. The coupled nonsplitting example excludes differentiable S(u,v)+h(v) only when c is nonzero; it does not exclude nonlinear composite or partly smooth representations.

## Closest algorithmic literature does not settle the same statement

The compared settings are intentionally different. The corrected report uses finite convex objectives, differentiable accepted points, fixed 0<c1<c2<1, the ordinary full update, and arbitrary SPD initialization. C/U infer convergence or a cluster conclusion, whereas [Gebken’s theorem](https://link.springer.com/article/10.1007/s10957-026-03008-z) assumes the limit and matrix behavior. A bundle Newton or VU method uses additional operations and is a different algorithm. Guo–Lewis’s smooth-region and exact smooth-band-agreement routes do not immediately cover nonoptimal nonsmooth interfaces. An internal “earlier finite-polyhedral-partition theorem” in the report is not an external published priority claim; this packet did not locate an external source matching it.

## Additional recent geometric and algorithmic neighbors

[Davis–Drusvyatskiy–Jiang](https://arxiv.org/pdf/2108.11832v2), first posted in 2021 and published online in January 2025 (2026 journal volume), gives a quantitative tangential projection formula in Theorem 3.6. Inference for U: on its flat interface, the common Lipschitz field A gives the strong-(a) estimate directly from A(x)-A(y). The source’s algorithmic conclusions use stochastic subgradient/proximal iterations with noise and other qualifications, rather than the report’s deterministic full update. Exact v2 locators and final publication metadata are in `geom_DDJ2026`.

[Liu–Sagastizábal–Solodov’s 2025 PGVU paper](https://pages.cs.wisc.edu/~solodov/lss24UV.pdf) is another recent adjacent result. Its Algorithm 3.1 adds a U-space correction after a proximal-gradient step. Theorems 3.3 and 4.4 impose bounded matrices and further assumptions for superlinear rates. This is relevant VU technique history and a different algorithm; it does not verify C or U. The author-manuscript numbering is kept separate from the publisher metadata in `geom_LSS2025`.

## Attribution changes recommended for the next scholarly edition

- Credit VU decomposition and partial smoothness when introducing the affine subgradient geometry; include Lewis and the Lemaréchal–Oustry–Sagastizábal lineage, with the latter’s original work accessed/checked separately before assigning precise theorem locators.
- Credit Lewis–Wylie and the exact published Gebken geometric lemma for nondegenerate multiplier stability. Explain the distinct algorithm and conditional assumptions.
- Call the semialgebraic affine-critical gap a corollary of established stratified projection/Sard machinery, with the above inference stated explicitly.
- Credit Liu–Sagastizábal–Solodov, Section 3.1, for the affine-hull discontinuity mechanism; reserve any novelty claim for the extra properties of the concrete finite strongly convex example.
- Credit Baillon–Haddad/cocoercivity for smooth secant estimates, retaining local buffer and domain qualifications.
- Identify normal-angle support-function algebra as classical; distinguish it from C’s application-specific gluing and transport proof.
- Use “no exact match found in the searched literature” for the remaining theorem/counterexample combinations until broader specialist review supports a stronger priority statement.

No resemblance finding establishes whether an AI generator actually read, memorized or borrowed from a particular work. Citation is warranted for mathematical antecedents regardless of whether such causal provenance can be reconstructed.

Peer review on 2026-09-11 corrected Guo–Lewis chronology/version binding and clarified the U.1 neighborhood-Lipschitz premise in JSON. See [independent review](../review/geometry_peer_review.md). No classification was changed.
