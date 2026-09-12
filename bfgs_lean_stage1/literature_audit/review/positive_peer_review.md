# Independent peer review: positive R/F/H/G literature packet

Reviewer: geometry subagent, 2026-09-11. This reviews the corrected report and the positive literature packet’s priority classifications and scope comparisons. It does not recompile Lean or certify external proofs. The reviewed report spans are in the packet; packet snapshots are hashed below.

**Outcome: the principal classifications are supported by the inspected primary sources.** Norm convergence and the nuclear optimizer have identified antecedents. Broader family results are appropriately marked provisional. The flat-fiber selector’s priority remains unresolved even after obtaining the closest smooth predecessor’s full text. Several statement and attribution refinements were sent to the packet owner; their resolution status is recorded at the end.

## Primary comparisons independently checked

**Euclidean norm versus quadratic plus absolute value.** Read [Guo–Lewis Corollaries 4.2 and 4.4 and their proofs](https://people.orie.cornell.edu/aslewis/publications/18-nonsmooth.pdf), together with the BFGS sequence convention. Corollary 4.2 covers arbitrary finite-dimensional Euclidean norms under that ordinary full-update Armijo–Wolfe formulation, including the one-dimensional absolute value. Corollary 4.4 proves only an axis-reaching subsequence for u²+|v| and explicitly leaves complete convergence open in that paper. The report’s centered-family convergence is stronger on this example. Its exact vertical matrix run is an additional illustration; it does not disprove existence of matrix limits for other runs. The packet correctly separates these conclusions and the earlier exact-search planar norm analysis.

**Gauge and smooth-part hypotheses.** Read R’s finite-cell and powered-gauge sections and the first four sections of families.tex. The complete centered theorem needs a minimizer at the chosen center and a compact initial sublevel; its smooth part is convex and locally C1,1 on an open convex neighborhood. The original smooth and sublinear summands need not separately minimize at the center. Powered noninteger gauges must be nonnegative. The individual powered terms need not be coercive, but the combined objective retains the stated minimizer/compact-basin requirements. The transformed-gauge theorem assumes coercivity, a continuous convex strictly increasing profile on [0,infinity), normalized at zero, C2 only on (0,infinity), and positive derivative there. Its second derivative may blow up at zero. These details should remain in standalone summaries. No nonlinear objective-transformation invariance is being asserted.

**Nuclear-norm optimizer.** Read [Cai–Candès–Shen Theorem 2.1 and its subgradient proof](https://arxiv.org/html/0810.3286v1). Thresholding the singular values (2,0) by one gives (1,0); the optimizer is a direct known specialization. It remains feasible in the report’s symmetric subspace, so restriction introduces no new optimizer theorem. R’s rotated nearby-pair computation concerns failure of RS near that optimizer. It is logically separate from optimizer identification and from any actual failure of BFGS. The packet handles this correctly.

**Two-piece finite termination versus many-piece infinite runs.** Read [Xie–Wächter Assumption II.1, Theorems II.1 and IV.1, and the main proof and remarks](https://arxiv.org/html/1712.08571v1). Differentiable accepted iterates are explicit. Their result eventually encounters a search ray with no acceptable curvature step, exposing unboundedness. H’s common-tilt claim says that any infinite admissible many-piece run must have values tending to minus infinity. On the two-piece specialization the old finite-termination theorem excludes such an infinite history; H does not replace or strengthen it. The affine-invariance theorem is for invertible square changes of variables, so the rectangular lifting formula is not literally its statement. The packet preserves these distinctions.

**Scalar line-search existence.** Read [Lewis–Overton Assumption 4.1, Theorem 4.5, Proposition 4.11 and relevant proofs](https://cs.nyu.edu/overton/papers/pdffiles/nsoquasi.pdf). Those results guarantee scalar-ray acceptable steps, not full-space differentiability on every ray. The report’s five-piece obstruction therefore does not refute them. Existing absolute-value results and special line-search trial rates do not by themselves establish the report’s all-positive-metric scalar result or its accepted-iteration family rates.

**Flat fibers and Schöpfer’s smooth theorem.** The full [2016 primary preprint](https://uol.de/f/5/inst/mathe/Preprints/2016-03.pdf) is now accessible. Independently read Assumption 3.1, Theorems 3.4 and 3.7, and the relevant proofs. The full-BFGS theorem gives linear function-value and distance-to-solution-set convergence under Lipschitz-gradient and restricted-strong-convexity assumptions; it does not display the report’s metric-selected limit. The general iterate-convergence theorem imposes matrix controls. This source cannot settle the nonsmooth homogeneous flat-fiber result, but neither does non-equivalence prove the selector new. Keep `unresolved` for exact selector priority, replacing the old inaccessible-source explanation with the actual remaining comparison.

## Attribution and wording refinements

1. For the transformed-gauge statement, specify continuity at zero and C2 on the positive half-line. For powered gauges specify nonnegativity. For the centered smooth part specify local C1,1 on the relevant open convex neighborhood. These improve statement matching without changing the classifications.
2. Add an explicit technique antecedent for G’s accumulating-kink construction: [Lewis–Overton §4.2](https://cs.nyu.edu/overton/papers/pdffiles/nsoquasi.pdf), journal p.149, constructs a convex ray function with geometrically accumulating corners to defeat its trial procedure. G instead uses a strongly convex hinge series and diverging certificate quotients while admissible accepted runs converge. Thus the exact result remains distinct, while the general adversarial accumulating-corner device has an earlier precedent.
3. Existing-result and known-special-case rows should not inherit the boilerplate sentence “No exact match ...”. Their search limits concern exhaustive historical priority, not absence of the very match recorded in the row.
4. Call Xie–Wächter’s argument an existing 2017 preprint result unless a journal publication is verified. Avoid wording that inadvertently asserts a journal publication when its source record leaves that date unset.
5. Preserve the difference between a local unique-minimizer theorem, a global compact-initial-sublevel theorem, and an affine-fiber theorem conditional on the projected limit. Preserve accepted-iteration rather than oracle-trial counting, and no claim of optimal rate sharpness.

None of these comparisons establishes which sources influenced the AI-generated research text. No source was inserted into Lean as an axiom, and no original report or positive packet was edited by this reviewer.

## Resolution status

All five requested wording/attribution refinements and the Schöpfer full-text comparison were applied by the positive-packet owner and rechecked. No principal priority classification changed. The exact metric-selector priority remains explicitly unresolved for substantive literature reasons, not missing access to S16.

## Initially reviewed packet hashes

- `bfgs_lean_stage1/literature_audit/packets/positive_R_F_H_G.json`: `228ea794a2df07b57dfdc8f73918f554a158d29f3b92e4f1962e7f08af074691`
- `bfgs_lean_stage1/literature_audit/packets/positive_R_F_H_G.md`: `9667bba5be707387baf9dbd33089e865e142b1a19115c70df724f546dfe8f7d3`

## Final rechecked packet hashes

- `bfgs_lean_stage1/literature_audit/packets/positive_R_F_H_G.json`: `228ea794a2df07b57dfdc8f73918f554a158d29f3b92e4f1962e7f08af074691`
- `bfgs_lean_stage1/literature_audit/packets/positive_R_F_H_G.md`: `9667bba5be707387baf9dbd33089e865e142b1a19115c70df724f546dfe8f7d3`
