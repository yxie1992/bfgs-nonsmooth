# Independent peer review: negative D/L literature packet

Reviewer: geometry subagent, 2026-09-11. Review target: the packet snapshots hashed below. This is a comparison and overclaim review, not an independent Lean build or a full correctness audit of every external proof.

**Outcome: no material overclaim identified in the core D/L overlap classifications.** The five `no_exact_match_found` assessments are appropriately limited to the searched literature and exact combinations of objective class, initialization, line search, oracle differentiability and failure quantifiers. They should remain bounded-search findings, never assertions of priority or causal AI provenance.

## Independent checks

- Read the current D main theorem and its C2,1 regularity argument, and the L global/local theorem statements, normalized return map and branch regularity discussion. D’s C2,1 description is supported by its later construction even though the main theorem initially says C2. L correctly separates the four-C1,1 local example from a finite uniformly positively curved C2 local counterexample, which it does not prove. The positive quadratic plus three-affine maximum is failure near the wrong vertex, not arbitrarily near that objective’s true minimizer.
- Independently read [Lewis–Overton §2, Examples 3.1/3.3 and Proposition 3.2](https://cs.nyu.edu/overton/papers/pdffiles/bfgs_exactLS.pdf). The accepted exact minimizers may be nonsmooth; the conceptual extension selects subgradients and admits zero steps and singular matrices. This does not duplicate D/L’s differentiable-query, positive-step ordinary update. Section 4 equation (4.1) directly supports the prior scale/shape normalization technique.
- Independently read [Mascarenhas Theorems 1–4 and relevant proofs](https://www.ime.usp.br/~walterfm/orientacao/bfgs.pdf). Its algebraic orbit plus interpolation supplies a real methodological antecedent. Smooth nonconvex three-dimensional octagonal behavior is materially different from D/L’s convex planar shrinking orbits. Attributing the broad construction technique while reserving comparison of the particular convex seed is reasonable.
- Independently checked [Diao Theorem 1 and §7](https://arxiv.org/html/2609.09686v1). The statement uses a parameter-specific smooth nonconvex objective and first-local-minimizer search; the orbit escapes to infinity. The packet preserves these distinctions and labels it a fresh preprint, not an independently certified result. Do not import the preprint’s broad introductory priority claims into this audit.
- Independently checked [Lewis–Zhang’s publisher statement](https://link.springer.com/article/10.1007/s10957-014-0622-7). Its stationary-but-descending nonsmooth limit is correctly distinguished from convex nonstationarity. The author-PDF retry failed, so the packet’s incomplete-proof-access qualification remains necessary. The Asl–Overton publisher endpoint also failed on this peer retry; that comparison relies on the original reviewer’s documented full-text inspection, not on a second independent full proof read.
- Gebken’s published theorem and assumptions were already read independently in the geometry audit. The packet correctly excludes unconditional subsumption: B1 includes an iterate limit and matrix behavior. It also correctly keeps full BFGS separate from scaled memoryless BFGS and avoids treating a selected bad initial state as a positive-measure failure basin.

## Precision improvements recommended for synthesis

1. Carry the line-search constants into any standalone claim catalog: D gives the same example and decisions for `0<c1<=1/3` and `c1<c2<1`; L is stated for `c1=10^-4,c2=1/2`. The packet’s short JSON descriptions omit the values but do not claim all constants. A summary must not silently expand these quantifiers.
2. Keep three layers separate: D’s local C2,1 example has no positive lower curvature; L’s local four-C1,1 example is strongly convex; L’s countable-polyhedral alternative is not a finite smooth maximum. The packet already maintains these boundaries.
3. `TECH_SEED` calls the broad seed/scaling technique established while classifying its report application `possible_extension`. This is defensible from its comparison text, but an integrated catalog could split an `existing_result` technique row from the `no_exact_match_found` concrete construction row to avoid suggesting that orbit interpolation itself is new.
4. Preserve access qualifiers for Dai and Lewis–Zhang, and preprint/correctness qualifiers for Diao. No classification should be strengthened using only an abstract, an inaccessible proof or the external author’s own novelty statement.
5. Keep the exact-search/null-step older failure in the bibliography despite non-equivalence: it is genuine preceding work on convex nonsmooth BFGS behavior and directly relevant to the question the report addresses.

No original report, Lean file or negative packet was edited during this peer review. These are editorial precision recommendations; none requires weakening the five current bounded-search classifications.

## Reviewed snapshot hashes

- `bfgs_lean_stage1/literature_audit/packets/negative_D_L.json`: `f5016df2e778e70b981b3a6886032b6ad01c7ac9ed43ca1d844fa25436798eee`
- `bfgs_lean_stage1/literature_audit/packets/negative_D_L.md`: `4b582464a524104b24001536e6ebe2cfc4b312c2799dc865f6f58267d5f9bfa4`
- `bfgs_lean_stage1/master_report/latex/chapters/D.tex`: `677d06b3d0ec9ae763e3fcf10bfee8d54494c278759f4d932b3882720b927fe7`
- `bfgs_lean_stage1/master_report/latex/chapters/L.tex`: `edee0bff0e5a6484aab9637c142d1f0b646afd2cc1f7cd18710021cb61059fc3`
