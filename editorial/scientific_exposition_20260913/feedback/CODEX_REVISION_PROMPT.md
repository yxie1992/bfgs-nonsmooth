# Execute a focused scientific-exposition revision of the BFGS manuscripts

You are in the author's existing Git repository. Review the accompanying `REVIEW.md`, `EVIDENCE.md`, and `REVIEW_CHECKS.json`. The reviewed source archive reports commit `91d30dadcfd0980472c3896be0c9fd83fc7d4db1`; discover the current repository state first and preserve any newer work and unrelated user edits.

## Goal

The latest narrative rebuild largely succeeded. **Keep the current paper's theorem selection and seven-section architecture.** This is not a request for another wholesale rewrite, another theorem inventory, a new formalization campaign, or a negative-only article. Produce an author-review-ready revision that explains the historical increment, geometric assumptions, and failure mechanism more directly.

The article currently builds to 46 pages and the companion to 107. Those are baseline observations, not new hard page limits. Keep all main claims self-contained through the article and its own appendices. Do not remove the strong positive achievements merely to return to the old length. Do not insert all companion families into the main article.

Work through the tasks below, revise, rebuild and inspect until the acceptance tests are met. Do not stop after a plan or one green build. Routine editorial choices do not need repeated approval. If an external blocker or execution limit genuinely prevents completion, finish unblocked work, commit a precise checkpoint, report the blocker and next command, and do not claim the revision is complete or promise unattended work.

## Preserve what already works

- The explicit Guo–Lewis benchmark comparison in the introduction, including the difference between approaching `v=0` on a subsequence and convergence of the whole sequence to `(0,0)`.
- The account of Xie–Wächter's finite escape and Gebken's conditional analysis, without pretending the new convex results subsume all other settings.
- The distinction between the paper's deterministic statements and the almost-sure Lewis–Overton challenge.
- Complete in-article centered/homogeneous and finite-partition results.
- The planar theorem, its nondegenerate smooth-max corollary, the nonradial three-quadratic example, and Appendix B's proof. This already closes the earlier “general certificate without payoff” issue; do not add a different theorem simply to obey an old illustrative suggestion.
- The negative cycle design, actual line-search decisions, scaling covariance, all-query containment, and the independent regularity regimes.
- The companion's broader incomparable statements and formal/source evidence.

## N1. Complete the historical-to-novelty comparison early

Use the repository's inspected primary-source literature audit. Move a concise version of the earlier-counterexample distinctions currently at `paper/sections/failure.tex:54–64` into the introduction. The reader should know before page 23 why prior smooth nonconvex, exact-search/subgradient, or limited-memory failures do not establish this convex deterministic local claim.

At the end of the introductory lineage, make explicit the step supplied by each contribution: the mixed benchmark and broader structured convergence; objective-only rather than presumed iterate/matrix behavior in the stated classes; actual deterministic convex failure with the exact locality/initialization properties; adjacent-degree principal-minor control beyond the trace/determinant baseline.

Use complete theorem comparisons, not blanket superiority or “first-ever” claims. Any new literature claim must be verified against a primary source and recorded. A special case can be new, known or unresolved in attribution; do not decide by assertion. No new search is needed merely to restate a supported existing comparison.

Acceptance: for each contribution the introduction identifies a relevant antecedent, the limitation relevant here, and the precise additional conclusion. Existing scope restrictions are retained.

## N2. Close the conceptual link between positives and negatives

After the negative proofs or in the synthesis, explain explicitly why the actual counterexamples evade the positive hypotheses:

- The homogeneous bad seed is unbounded below; its coercive cap has an affine intercept. Neither contradicts the coercive homogeneous theorem.
- The local embeddings place wrong vertices at every shrinking scale, not in a finite locally resolved polyhedral-cell pattern.
- At the optimizer of the smoother-branch construction the active branch gradients are `0,0,0,(0,1)`. The lower-curvature construction has the same pattern before the fixed coordinate change, and its equivalent afterward. Affine independence and the strictly positive optimal weights of the planar corollary fail. Check the displayed construction and existing formal contracts for this newly explicit comparison.

Use the exact model decomposition `y = mu s + (g_j-g_i)` to explain why positive branch curvature does not remove the jump-driven mechanism as the steps shrink. Link this explanation to the certified trajectory, not to a claim that every branch change causes failure.

Explain what this establishes and no more: these are sufficient hypotheses distinguishing our positive theorem from our examples, not necessary conditions for every convergent BFGS run. Do not claim that every nonoptimal affine-critical point or accumulating singularity causes failure.

Acceptance: a reader can explain, using objective data, why the strong-convexity negative result does not contradict the nondegenerate planar positive corollary.

## N3. Teach the planar field's construction in the main text

Before the invocation of the Appendix B field lemma, add a concise proof overview drawn from its existing proof. Explain `f_1(p_j(t))=f_2(p_j(t))=t` and the level velocity `grad f_i^T p_j'=1`. Explain why strict contours separate the supporting-normal arcs, allowing the local directions to be joined. Explain the tangent-preserving derivative and why the one-dimensional planar tangent matters. Finish with the transport cost being charged to objective decrease rather than unproved finite path length.

Do not copy all cutoff or one-sided-derivative details into the main text; keep Appendix B complete. Do not treat a nonlinear change of coordinates as preserving BFGS, or equate local common pairing with an automatically valid global certificate. A diagram may show the primal contour, interface tangent and comparison direction, with gradient-space panels kept clearly distinct.

Acceptance: without reading Appendix B, a reader understands where the direction comes from, why joining is possible, and why the proof is restricted to the plane.

## N4. Make the breadth recognizable without adding theorem families

Improve Table 1 or its surrounding prose with explicit examples. Name `l1` or `l_infinity` among the arbitrary-dimensional norm corollaries and contrast nonisolated nonsmoothness with the attributed Euclidean case. Do not turn that illustration into an unverified novelty claim.

Add one short worked local reduction, such as a squared smooth loss plus `lambda||x||_1`, under `lambda>0` and uniqueness of the minimizer. Nonzero optimal coordinates have locally fixed signs; zero coordinates produce centered absolute values. Tie this to the existing theorem and local scope. Do not assert uniqueness or global convergence for all such problems without the relevant hypotheses.

Acceptance: a reader sees familiar important models and can identify which assumption supplies the local/unique conclusion, rather than only recognizing abstract class names.

## N5. Finish the explanatory graphics and trial table

Add the missing schematic of one fixed objective with `p_j -> x_*`, local model neighborhoods of width `O(a_j)`, and copied complete query orbits of width `O(a_j^2)`. Use an enlarged inset and label it as schematic. Preserve all-query containment and the fixed-objective quantifier.

The prior and current `cycle_trials.pdf` are byte-identical. Improve the crowded near-corner labels or provide a zoom. Label accepted lengths as well as rejections; distinguish the two phase rays in grayscale. Keep any nonuniform drawing-scale disclosure.

Make Table 2's decision logic understandable by including old phase values or accepted actual-to-predicted decrease ratios. Retain the rigorous enclosures in Appendix C if moved. A rounded displayed value is not a certificate premise. Never present numerical shooting as proof of stable-manifold membership.

Optional: a two-row scaling table can replace repeated prose, with `(lambda,sigma)=(a_j^2,a_j^4)` versus `(a_j,a_j^2)`, both giving matrix factor one.

Acceptance: at final print size the visuals explain both the finite implementation and the local-failure quantifier, rather than merely decorate the proof.

## N6. Perform a controlled prose and notation compression

Do not cut the scientific lineage or positive achievements to save pages. Remove duplicate reminders and audit-specific qualifications that do not change the mathematical statement. Examples are “These are actual principal determinants” immediately after their definition and the paragraph converting an arbitrary real secant constant to a nonnegative one. Keep accepted differentiability and exact quantifiers in theorem/algorithm statements.

Use the benchmark inward-remainder display once and cross-reference it instead of proving the same identity twice. Avoid repeating the full scope warning after every corollary.

Resolve article notation collisions while leaving formal declaration names unchanged: the PSD remainder versus seed inverse matrices both called `M`; Wolfe margin versus slope coordinate `c`; dimension versus scale index `n`; seed point `z_2` versus the second coordinate `z_2`; and direction versus bad-limit `p`. Maintain a notation-to-formal alias map.

If needed, move scalar ramp formulas and their verification to an article appendix while retaining their design, precise lemma and embedding proof in the main text. Do not outsource essential proofs only to the companion.

Keep an honest substantive AI-use disclosure and concise formal-verification/reproducibility paragraph. Future instructions to human authors, declaration-count history and detailed axiom-audit explanations belong in the editorial record or companion, not the scientific conclusion. Never assert human approval, peer review or deposit that has not occurred.

Acceptance: the article reads as a mathematical contribution, with auditable but unobtrusive formal support. Its hypotheses and proofs are unchanged unless a documented mathematical correction is genuinely needed.

## Companion and source/formal consistency

Preserve the improved companion opening and reading routes. Do not rewrite 107 pages unnecessarily. Fix stale hard-coded references or current/historical audit presentation where encountered. Keep the article/companion result map synchronized with actual selection. The compact source ZIP intentionally excluded Lean and audit databases; that is not a reason to reconstruct or invent missing evidence.

Inspect exact current formal contracts for any newly explicit deduction or changed mathematical wording. Reuse verified conclusions; compile any genuinely new formal supplement if needed. Do not add custom axioms, weaken contracts, or mark a proof as checked based on prose. Routine copyediting should not trigger an unrelated expansion of the formal project.

Provide a stable versioned reference to the companion/research archive once the author has authorized the relevant metadata. Do not create a DOI, public deposit or submission without authorization.

## Git milestones and persistence

This is the existing authorized Git workflow. Inspect status and remotes, preserve user changes, and commit and push task-related major milestones. Suggested milestones:

1. Introductory comparisons and the explicit positive/negative synthesis.
2. Planar proof overview, recognizable examples, figures/table and notation/prose revision.
3. Built and visually inspected article/companion, updated correspondence and completed review response.

Use meaningful commits on the working branch and the configured remote; verify each push. No force-push, destructive reset, remote invention, secret staging, dependency caches or unrelated changes. If a remote operation fails, keep the local commit, record the exact failure, continue unblocked work, and report it honestly.

## Completion gates

Create a response table `editorial/<current-review>/RESPONSE.md` for N1–N6, with the actual edited paths, final page locations and evidence that each acceptance test is met. Document a justified alternative when a suggestion would make the manuscript worse; do not simply mark it done without implementation.

Complete three distinct self-review passes: historical/novelty framing; mathematical scope and explanatory logic; and build/visual/readability. These are author-side automated passes, not independent human refereeing. Rebuild both PDFs, inspect all article pages and changed companion pages, verify references and relevant correspondence, and update release metadata consistently.

Stop when these predefined gates are satisfied, not after another outline or a single PASS log. Report final documents/page counts, substantive changes, checks actually executed, commit and push outcomes, and only genuine unresolved author actions. Preserve the stronger mathematical content and finish this focused revision rather than reopening the paper's entire architecture.
