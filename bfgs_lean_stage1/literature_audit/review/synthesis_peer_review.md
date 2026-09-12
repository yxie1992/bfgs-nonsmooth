# Independent review of the literature synthesis

Reviewed 2026-09-11 America/Los_Angeles (2026-09-12 UTC). This was a bounded review of `REPORT.md` against all four current packets and their claim records, with targeted reinspection of the corrected D/L/H statements and the earlier reviewed M/T/G formulas. No search scope was added.

## Verdict

The synthesis is consistent with the packets and does not overstate publication priority or causal AI provenance. No substantive false equivalence between an external theorem and a corrected-report theorem was found. Two precise wording corrections were made directly to `REPORT.md`; neither changes a mathematical claim or a literature classification.

## Corrections applied

1. L's collective wording that its branches are not C² was too broad: the fourth branch is quadratic plus affine. The synthesis now says that the first three branches lack second differentiability at the accumulation point and identifies the smooth fourth branch. This follows directly from L's scalar regularity proof and equation `L:eq:embedding`.
2. The M overview now states bounded accepted gradients and fixed weak-Wolfe parameters explicitly. It separates reciprocal-mean divergence under vanishing predicted decrease from the finite-horizon and superquadratic consequences under summability. These agree with `M:average` and `M:superquadratic` and avoid suggesting summability alone supplies the conclusions.

## Quantifiers and comparisons checked

- D uses one objective and identity initialization, with bad starts approaching its actual unique nonsmooth minimizer. The same trial decisions work throughout its stated c1/c2 range. L has its own fixed parameter pair and a different regularity conclusion. The synthesis does not combine these into the unproved local strongly-convex finite-C²-branch theorem.
- L's global quadratic-plus-three-affine example converges to the wrong vertex; approaching that vertex does not supply local failure near the true optimizer. Its local construction and its countable-polyhedral variant remain distinct.
- All-query differentiability in D/L is retained. It is not inferred merely from differentiable accepted points or scalar ray differentiability.
- The historical negatives remain distinguished by nonconvexity, memory restriction, conceptual subgradient/null steps, stationarity notion, and search rule. Diao's verified September 9, 2026 submission precedes the cutoff; it remains identified as a neighboring preprint rather than independently certified mathematics.
- Guo–Lewis special cases, Xie–Wächter finite unboundedness detection, and the conditional Gebken theorem are described consistently with their inspected source records. The Schöpfer update is consistent with the positive packet's completed manuscript inspection.
- The affine-critical-value paragraph discloses the projection inference rather than replacing Clarke criticality by affine criticality without justification. G's certificate obstructions are not presented as BFGS failures.
- F/H's two selector entries are unresolved historical comparisons for proved report statements. H's higher-rank noncompact limitation is separately qualified, and the additional relative-interior theorem is not omitted from the selector discussion.
- Source and theorem locators in the synthesis agree with the detailed packets. Access-limited records are not upgraded to full proof inspections. Standard deductions are distinguished from exact published formulations by the six-label glossary.

## Evidence limits and validation

The register currently contains 75 research/technique groups and 172 covered spans: 147 research comparisons and 25 scope/execution entries, matching the synthesis. All 18 baseline report hashes remain unchanged. Only the literature synthesis and this review were edited in this review pass.

This review checks synthesis fidelity and cautious attribution. It does not exhaust the historical literature, certify priority, reprove external papers, or repeat the Lean axiom audit. No blocking issue remains within this bounded review.
