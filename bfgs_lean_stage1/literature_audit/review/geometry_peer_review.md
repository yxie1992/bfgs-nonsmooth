# Independent review of geometry_C_Q_U_A

Reviewed on 11 September 2026 by the positive-results literature reviewer. Scope: substantive classification and hypothesis comparison, especially A affine critical values and C/U versus Gebken and partial smoothness. This is not a fresh Lean or entire-proof audit.

## Assessment

The principal classifications are justified as bounded literature comparisons. I found no case in which a cited conditional or modified-algorithm theorem establishes the full C/U claim. The packet properly identifies geometric antecedents without calling them proofs of unmodified full BFGS. Two clear metadata/scope corrections were made below; no classification change was needed.

**A.span.4:** The `known_special_case` classification is justified as an explicitly derived corollary. I independently read BDLS Proposition 4 and Lemma 8/Corollary 9. For finite convex semialgebraic F, a finite compatible stratification has a common tangential subgradient projection. Projecting an affine combination equal to zero gives zero gradient of the stratum restriction because its coefficients sum to one. Smooth definable critical-value finiteness then supplies the finite set of affine-critical values. Continuity maps a connected component into a connected subset of this finite set, hence a singleton; an attained minimum gives the low-level gap. [BDLS primary text](https://arxiv.org/html/math/0601530)

The distinction from Clarke criticality is essential: for max{x,2x} at zero, the affine hull of the subdifferential contains zero but its convex subdifferential does not. Thus bare finite Clarke critical values would not justify A. The packet states the missing projection step and labels it an inference, correctly.

**C/U versus Gebken:** I independently rechecked published Behavior B1.2–B1.5 and the surrounding argument. Those assumptions include iterate convergence, recurrent selections, a spectral gap/bound, and annihilation of gradient differences. C’s cluster-set contradiction and U’s derived restricted matrix control have different premises. The `possible_extension` classifications are defensible; they do not establish novelty. [Gebken, published full text](https://link.springer.com/article/10.1007/s10957-026-03008-z)

**Partial smoothness and identification:** The packet correctly distinguishes common tangent/normal geometry from an algorithmic identification theorem. Convergence of differentiable iterates alone does not give convergence of subgradients to the graph point required by identification. The report also allows an exceptional hyperplane to contain differentiable points lacking local gradient-Lipschitz regularity; U.1 cannot be reduced literally to U.2. Neither a proximal VU algorithm nor a bundle Newton result is interchangeable with the report’s update.

**Known ingredients:** The classifications for stable positive multipliers and rank-stable common-rate fields are reasonable corollary/ingredient attributions. They should retain the JSON qualification that the exact packaged C.span.15 lemma was not found verbatim. The support-function formula is an antecedent only for its algebra; it does not establish the complete glued field or determinant transport. Certificate counterexamples remain distinct from BFGS divergence claims.

## Corrections made to the packet

1. `geom_U_single_interface` said “globally Lipschitz.” U.1 assumes Lipschitz continuity on an open convex neighborhood of its compact initial sublevel. I replaced the statement with that scope. Strong convexity is likewise used on that neighborhood.
2. `geom_GuoLewis2018` now records the earlier 19 March 2017 Optimization Online posting and 8 May 2018 journal publication. The theorem3.3/corollary3.6 locators are explicitly bound to arXiv v1, whose title and numbering differ from the journal manuscript. [Early posting](https://optimization-online.org/2017/03/5912/), [journal record](https://epubs.siam.org/doi/10.1137/17M1121883)

The existing Gebken2026 metadata and Lewis–Liang2018 versus Lewis–Liang–Tian2022 distinction agree with independently checked primary records. Other listed publication histories were screened for internal consistency but not all re-fetched during this peer pass.

## Review limits

I read the packet, the actual A chapter, C’s theorem premises, and U’s two main theorem premises, and re-read the closest BDLS, Gebken and Guo–Lewis source passages. I did not reproduce all proof calculations in Q or the U spike construction. Exact historical novelty remains unproved. Changes are confined to literature packet metadata/text and this review; the sealed report and Lean sources were untouched.
