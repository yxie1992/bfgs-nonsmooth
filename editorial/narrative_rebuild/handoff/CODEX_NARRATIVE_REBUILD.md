# Execute a research-story revision, not another theorem-inventory revision

## Mission

Revise the paper and align the companion around the scientific significance of this work. The author explicitly rejects a paper that is merely a collection of results, even if the collection is logically ordered and formally checked.

The article must make the reader understand, quickly and accurately:

1. What the longstanding unmodified nonsmooth-BFGS question is.
2. What preceding research actually established, and what remained unresolved.
3. Which claims our negative results rule out.
4. Which important positive questions our theorems settle, under exactly what objective assumptions.
5. What new analytical capability makes these advances possible.

The three contributions are coequal: **strong counterexamples; broad global/local convergence theorems resolving concrete questions; reusable full-BFGS analysis.** Do not reduce the positive theory to a modest contrast accompanying a large negative-construction paper. Do not make formal verification the scientific plot.

Use the current corrected source and exact Lean contracts as authoritative. This brief is editorial, not permission to invent new theorems or priority claims. Existing mathematical-scope and implementation safeguards continue to apply.

## Work continuously to a completed revision

Inspect repository instructions, current Git state, operative manuscripts, proof/source mappings and literature audit. Preserve existing user changes and original corrected source snapshots. Then execute the rewrite, not just a plan. Work through the entire article, companion alignment, source/attribution correspondence, builds, rendered review, and revisions until the completion criteria below hold. Do not stop after adding a related-work paragraph, rewriting the abstract, making another table, or recording another set of PASS checks.

This is an existing Git repository. Commit and push major milestones to the configured authorized remote and working branch, following repository conventions. Suggested milestones: (1) scientific-positioning and section redesign; (2) complete narrative rewrite with proof-complete main claims; (3) checked, rendered, reconciled author-review release. Inspect diffs, stage only task-related files, do not force-push or discard changes, and record actual commit/push outcomes. If pushing is externally blocked, preserve the local commit, log the error, and continue unblocked work. Do not claim human review or journal readiness beyond what actually occurred.

## 1. Repair the paper's positioning before rearranging its proofs

The main problem is not simply whether finite polyhedral partitions are better than finite smooth maxima. That is an important conclusion, but a narrower viewpoint than the full contribution.

The governing question is:

> What global or local convergence can one expect from ordinary full BFGS on convex nonsmooth functions, and how can it be proved without assuming the desired behavior of its iterates or matrices?

The paper's answer is two-sided. Convexity and strong regularity alone cannot support unrestricted deterministic guarantees; nevertheless, broad identifiable geometries admit convergence, encompassing explicit previously unresolved examples. A new matrix/energy framework makes the positive analysis possible while accommodating degeneracy of the learned metric.

Use this logic throughout:

**observed phenomenon -> existing mathematical progress -> precise unresolved gap -> complementary answers -> common analytical mechanism -> consequences and remaining boundary.**

The current introduction begins with our finite-partition contrast and formal theorem statements before establishing the literature's problem. Reverse that priority. Integrate the essential lineage into the opening rather than relegating it to a subsection after the main theorems. A later related-work subsection can provide secondary comparisons.

## 2. Build an accurate, purposeful academic lineage

Use `PRIMARY_LITERATURE_ANCHORS.md` and the existing audit, checking exact primary versions and any new claims. For each major precursor write: **what it established; why that did not settle the present target; what our theorem adds or changes.** Do not present a neutral list of authors. Do not disparage earlier results or describe all previous work as conditional.

Essential lineage:

- Classical smooth-convex BFGS convergence and trace/determinant analysis: the baseline and methodological ancestry.
- Lewis--Overton: empirical nonsmooth effectiveness, the inexact search, special analyses, and Challenge 7.1. Explain why gradient jumps and inverse-matrix degeneracy obstruct a straightforward transfer of smooth theory.
- Guo--Lewis: not just a Euclidean-norm example. Explain the broader smooth-extension/Powell framework, its Euclidean-norm corollary, and the precise partial conclusion for u^2+|v|. Corollary 4.4 only supplies a subsequence approaching a point of v=0; the paper expressly leaves convergence of every BFGS sequence to zero open.
- Xie--Wächter: the two-piece unbounded affine model and finite detection of unbounded descent. Our arbitrary-many-piece or homogeneous results are broader in function class, but do not supersede that finite-termination conclusion on its special case.
- Gebken: the published 2026 work analyzes criticality under assumed iterate and matrix behavior. Distinguish its objective setting from ours; our advantage is deriving convergence for specified convex families without assuming those asymptotics, not a claim to dominate its whole theorem.

A particularly effective benchmark is u^2+|v|: it was explicitly unresolved in Guo--Lewis and still identified as not understood in Gebken's 2026 introduction. Our whole-sequence global convergence conclusion belongs in the introduction and as a named corollary, not in a short paragraph deep in the applications section.

State the relation to Challenge 7.1 accurately. It concerns almost-sure behavior for locally Lipschitz semialgebraic objectives with bounded sublevels, including more than mere cluster-point stationarity. Our specially chosen deterministic failures do not establish a positive-measure failure set, and the local accumulating examples are not finite semialgebraic descriptions. Do not say we disprove that full challenge. Say precisely which unrestricted deterministic alternatives we disprove and which convex classes we settle.

Maintain a concise prior-result/current-result comparison with exact theorem locators and hypotheses. Use the paper's citations conventionally. New results may be stated confidently as "we prove"; claims such as "first," "strongest known," and "resolves all previous conjectures" require evidence and must not be inferred from a failed search. Attribution of tools must not become repetitive disclaimers that bury the contribution.

## 3. Establish the contributions in three explicit paragraphs

Write three clearly distinguished introduction paragraphs, not an unranked list of theorem labels.

### Negative contribution: limits of deterministic convergence

Describe the actual fixed unit-first Armijo--weak-Wolfe implementation, convergence to a nonstationary point, and how close-to-minimizer bad starts for one fixed function refute a local neighborhood guarantee. State the two regularity regimes separately. Explain the global polyhedral/quadratic examples as simpler consequences with different significance. Do not quietly strengthen to strong Wolfe, a different routine, all starts, or positive-measure failure.

### Positive contribution: a substantial expansion of convergence theory

Name the actual families and conclusions. Foreground global convergence for the mixed benchmark and centered smooth--sublinear class, and coercive degree-one homogeneous objectives including compact-sublevel maxima of linear functions. Distinguish bounded-below noncompact value convergence from whole-iterate convergence. Then give local results for smooth convex plus finite polyhedral terms and finite polyhedral smooth-piece partitions. Show at least one genuinely nonradial extension with a complete proof or an explicitly limited article scope.

Avoid ambiguous "max of linear functions converges": homogeneous linear maxima, general affine maxima, compact versus noncompact cases, and value versus iterate conclusions differ. State the retained exact result.

Not every example was separately a published open problem. Distinguish "resolves the conjecture stated for u^2+|v|" from "also covers the following families." Recovering the Euclidean norm is an attributed corollary, not the novelty claim.

### Methodological contribution: analysis that tolerates matrix degeneration

Explain that the adjacent-degree principal-minor hierarchy derives restrictions on the actual BFGS update without requiring eigenvalue convergence or a bounded condition number. Reciprocal growth and comparison energies convert those restrictions into convergence under objective-level assumptions. Credit the classical determinant/trace tradition; identify the specific added inequality and consequences. Do not call the entire concept of matrix potentials new.

## 4. Use this revised article architecture

Adapt details for complete arguments and readability, but preserve the following flow.

### 1. Introduction: the problem, its history, and what changes here

Give a compelling, accurate account before formal machinery. The first two pages must identify the unresolved benchmark, the conditional-versus-objective distinction, and all three contribution axes. Follow with precise main-result statements or a concise statement map; avoid leading with three dense negative theorem blocks.

### 2. What the results say about nonsmooth BFGS

Explain the conceptual comparison using u^2+|v| and the actual wrong-corner construction. State what the counterexamples exclude and what the sufficient conditions accomplish. Preview the positive cases in a small global/local/outcome table. Introduce affine criticality only when it helps explain an actual theorem, not as a conjecturally complete organizing principle.

### 3. The analytical framework

Motivate the reference energy before the principal-minor algebra. Explain its negative progress term and positive secant correction, then prove the hierarchy, reciprocal consequences, and certificate principle used by the article. Keep a complete proof chain in the article and its appendices. Present the method as reusable but do not claim extensions to different quasi-Newton updates without proof.

### 4. Global convergence: homogeneous and mixed geometry

Prove the article's global theorems and their explicit consequences. Include the whole-sequence u^2+|v| result and an exact comparison with Guo--Lewis. Explain why homogeneous inward modeling is exact and why a smooth convex term can be added. Give the compact max-linear/norm/gauge conclusions precisely. Include the noncompact homogeneous value theorem in the article if advertised as a main contribution; otherwise summarize it with an explicit companion reference and do not count it as independently proved in the article.

### 5. Local convergence: objective geometry, conditions, and examples

Develop local finite-partition and polyhedral results through actual localization, not unexplained technical hypotheses. Treat moving comparison geometry as a genuine relaxation with a complete nonradial application. Retain the independent planar, fixed-normal and flat-contour hypotheses when selecting an extension. No main-text "beyond radial" catalogue may substitute for a proved main contribution. Prefer a smaller number of well-explained complete theorems to many brief announcements, but do not demote the breadth of the positive theory from the paper's scientific claim.

### 6. Failure: a mechanism, deterministic realization, and local embeddings

Prove the negative results after readers understand their meaning. Explain how one designs the cycle, forces the actual trial tree, and transfers the orbit into smooth local models. Present the two embeddings along their different regularity axes. End with the precise statements ruled out and the additional structural/generic alternatives not ruled out.

### 7. Synthesis, formal verification, and boundaries

Return to the original questions. State which benchmark and family questions are answered, which deterministic assertions are false, and which form of the Lewis--Overton challenge remains outside the results. Explain formal verification briefly; do not lead with declaration counts, audit machinery, or historical editing claims.

Move lengthy routine algebra, interval certificates, interpolation formulas and repeated examples to article appendices where needed. Preserve all strongest incomparable results in the complete companion. Essential proofs of the article's own principal claims cannot be replaced by companion citations, executable checks, or a Lean declaration. If length forces a change, reduce peripheral examples and repetition before removing the scientific context, the main positive achievements, or geometric explanations.

## 5. Explain every sufficient condition in five steps

For each main positive theorem, write an integrated discussion answering:

1. What obstruction is this condition intended to control?
2. What does it mean in function values, level geometry, or active first-order models?
3. Which familiar families satisfy it, and how is it checked there?
4. Where is it used in the proof and what freedom does it leave to H_k and x_k?
5. Which stronger claim is not implied; is it sufficient only, and what known successful examples lie outside it?

For inward radial smoothness, say that first-order modeling stays quadratically accurate toward the minimizer even if derivatives jump transversely. Explain positive-band constants and why optimal nonsmoothness is permitted. Show the error t^2 u^2 for u^2+|v|. Do not imply that BFGS actually takes radial steps.

For a finite local polyhedral partition, explain that after shrinking a neighborhood the remaining cells contain x_* and inward segments stay inside one cell. This is the geometric reason for the estimate. The algorithm need not identify a cell or manifold.

For transported certificates, explain visibility, gradient-jump control, and change of comparison geometry in that order before giving the PSD inequalities. The field is analytical, not an input to BFGS. Show a concrete nonradial certificate and explain its design.

For affine-critical results, distinguish a common-rate descent direction from arbitrary descent and distinguish a geometric necessary obstruction in certain proofs from a universal failure criterion. For fixed normals, explain the actual dimension-independent freedom and the rotating-normal limitation.

## 6. Explain every counterexample in five steps

1. State the tempting deterministic theorem it refutes, including its quantifiers.
2. Show the geometric/dynamical mechanism: an actual full-BFGS cycle reduces scale while approaching a nonstationary configuration.
3. Show why the accepted lengths are outputs of the stated search, with all rejected queries accounted for.
4. Explain the scaling and regularity design before listing constants and spline formulas.
5. State what is still possible: a different objective subclass, generic rather than every-start guarantee, or another algorithm/search. Do not conclude that our particular sufficient condition is necessary.

A useful shared lemma, already implicit in the existing proofs, is the matched scaling F(p+lambda z)=C+sigma G(z), H_F=(lambda^2/sigma)H_G, with all-query containment. Repackage it only with a reviewed formal correspondence. It makes the identity initialization across shrinking copies understandable. Retain exact versus schematic distinctions in figures and do not simulate stable-manifold membership from rounded data.

## 7. Review and completion gates

This is a substantive rewrite. Fix all affected transitions, abstracts, conclusions, citations, theorem names, notation, source/formal maps, companion references and release metadata. Do not just insert a longer related-work subsection into the old architecture.

Keep all theorem assumptions and corrections intact. Do not merge incomparable negatives, universalize finite-family examples, or assume the H_k behavior being explained. Preserve the current no-placeholder/no-custom-mathematical-axiom policy; rerun the appropriate affected builds and audits and report exactly what ran.

Completion requires three distinct recorded passes:

- **Scientific significance:** a reader of the introduction can state the unresolved problem, the precise prior limitations, the new benchmark/family results, the refuted convergence assertions, and the new technical idea.
- **Mathematical exposition:** every main condition and construction has motivation, examples, a proof role and a scope boundary. All headline theorems have complete proofs in the article/its appendices and match the corrected contracts.
- **Publication integrity:** citations are exact and readable, all references resolve, figures are reproducible and legible, both PDFs build, all pages are inspected, companion and claim ledgers agree, and Git milestones/push outcomes are recorded.

Deliver the revised article and companion sources/PDFs plus a short response showing where each narrative requirement was implemented. Do not present new audits as substitutes for reader-facing improvements. The article should read as an original optimization contribution situated in an academic lineage, not as a repaired technical report or a formalization progress report.
