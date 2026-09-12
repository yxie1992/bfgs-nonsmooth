# Journal article: narrative and architecture

This is an editorial proposal based on the corrected LaTeX source, not a new theorem or a completed priority audit. Validate all statement scope against the current repository and formal contracts.

## The one-sentence story

**For unmodified BFGS on convex nonsmooth objectives, smoothness inside the pieces is not enough for local convergence, while identifiable compatibility between gradient jumps and remaining descent yields substantial positive results.**

The article should explain a phenomenon, not display an inventory. The central tension is between local convergence on finite polyhedral geometry with smooth extensions and actual deterministic local failure with finitely many highly smooth convex branch formulas. A finite number of formulas does not imply a finite local geometric partition.

“Preserved descent” is a useful explanation, not a necessary-and-sufficient characterization. Neither affine criticality nor the transported certificate has been shown to classify every objective. Do not convert the intuition into a universal theorem about collapse of H_k or its eigenvectors.

## Three reader takeaways

A reader who remembers only three things should remember:

1. An unrestricted regularity-only deterministic local-convergence guarantee is false in the precisely stated classes.
2. Several objective geometries support convergence without assuming that BFGS matrices or iterates already behave favorably.
3. A common comparison-energy analysis explains the positive results, while exact cycles and embeddings explain the negative ones.

The Lean development makes the mathematical record checkable. It is an important assurance mechanism, not the reason an optimization reader should care about the theorem.

## Opening contrast and running examples

Begin with `u^2 + |v|`. At a nonoptimal ridge point, the limiting gradients `(2u,1)` and `(2u,-1)` differ normally but retain horizontal descent. Contrast this with the *specific certified* nonoptimal corner. Do not claim that every full-dimensional subgradient hull causes failure, or that all accessible jumps always span all active differences.

State the positive finite-partition theorem and the deterministic smooth-branch local counterexample in accessible terms early. Then make their quantifiers precise. The lower-curvature construction belongs in a separate statement/table, not an extra clause appended to the first example.

Suggested opening paragraph to revise after checking scope:

> Convexity rules out nonoptimal local minima, but it does not prevent an optimization algorithm from converging to a nonstationary point. For BFGS applied to a nonsmooth objective, successive gradients reflect both ordinary curvature and changes of the active first-order model. These changes can be compatible with progress toward the solution, or they can participate in a contracting trajectory around the wrong point. We study this distinction for unmodified full BFGS with Armijo–weak-Wolfe line searches, giving both local convergence guarantees and deterministic local-failure constructions.

Follow with concrete results, not another paragraph of broad motivation.

## Recommended section architecture

### 1. Introduction and main results

**Question:** What was unknown, what is now ruled out, and what can be guaranteed instead?

- Define the scope sufficiently to avoid ambiguity about full BFGS and weak Wolfe.
- State headline positive and negative conclusions within two pages.
- Use a small assumptions/conclusions table, not a dozen numbered contributions.
- Place related work in three or four coherent paragraphs, followed by a proof strategy and road map.
- Explain that a universal local theorem and almost-sure/generic convergence are different questions.

### 2. Geometry of progress and stagnation

**Question:** Why can the same update succeed on one nonsmooth geometry and fail on another?

- Give the mixed-ridge example before U/V notation.
- Explain supporting gradients, common components, and affine versus convex balance.
- Use a gradient-space figure, explicitly tying the negative geometry to the constructed cycle.
- Distinguish a distant wrong corner from a sequence of wrong configurations approaching the optimizer.
- Avoid making this section a second introduction. Each picture must motivate a later proof step.

### 3. A common BFGS energy principle

**Question:** What does the update force even without matrix convergence?

Introduce the reference energy

    E_k = (x_k-x_*)^T H_k^{-1}(x_k-x_*),
    q_k = g_k^T H_k g_k,
    R_k = [y_k^T(x_{k+1}-x_*)]^2/(y_k^T s_k),
    E_{k+1}=E_k-[g_k^T(x_k-x_*)]^2/q_k+R_k.

Explain the negative term and the secant correction before introducing principal minors. Then prove the actual hierarchy, normalized recurrence, and needed reciprocal-growth result. Give the determinant/Gram algebra a clear lemma statement and complete appendix proof if it disrupts the exposition.

Build the certificate in this order: visible descent, controlled secant correction, controlled movement. Explain why changes parallel to s_k are harmless. Do not lead with the PSD-field definition before explaining its purpose.

### 4. Geometries guaranteeing local convergence

**Question:** Which familiar objectives satisfy the sufficient conditions?

- Start with centered homogeneous/sublinear geometry and its zero inward modeling error.
- Add smooth terms, then pass to finite local polyhedral partitions.
- Show how nonzero optimal residuals become locally smooth and zero residuals produce centered terms under the actual hypotheses.
- State PLQ using finite polyhedral cells; never equate it with an arbitrary maximum of quadratics.
- Present only a few meaningful examples in the article; preserve the rest in the companion.

### 5. Beyond radial geometry

**Question:** Are the guarantees limited to rays and flat partitions?

- Lead with the planar affine-critical-cluster theorem and its local smooth-max corollary if the complete proof fits the article's scope.
- State strict positive contours, switching regularity, dimension, and initialization explicitly.
- Introduce no-false-affine-criticality as a bridge to optimality, not as a general proved characterization.
- The fixed-normal multidimensional result addresses a different issue: imperfect transport can be paid for in fixed smooth directions. Rotating normals remain unresolved.
- The flat-contour parabolic family is not subsumed by the strictly-convex-contour planar theorem.

If space requires a narrower article, move an entire independent extension to the companion, including its theorem and proof, and do not advertise it as a proved main result of the shorter article. Keep a precise, clearly labeled pointer rather than a proof-free theorem section.

### 6. Deterministic local failure despite regularity

**Question:** Why cannot regularity-only assumptions replace the positive geometric assumptions?

- State the exact deterministic algorithm.
- Explain the finite algebraic cycle before its coefficient list.
- Show the accepted/rejected trial table and the strict margins.
- Prove that exact scaling repeats the full line-search decision tree, not only accepted endpoints.
- Explain how scaled copies give one fixed function with failing starts at every scale.
- Give the scalar interpolation and all-trial containment proof in full, in article appendices if necessary.
- Treat persistence under a positive quadratic and the lower-curvature embedding as a separate theorem and proof route.

Do not draw a rounded stable-manifold initial state and label it an exact orbit. Explain where formal interval certificates and analytic existence theorems enter.

### 7. Verification and the remaining boundary

**Question:** What exactly is checked, and what remains undecided?

A short formalization/reproducibility section should name the checked theorem scope, pinned release, correspondence route, and foundational trust assumptions. Keep declaration counts, import details, and the correction diary in the companion.

Conclude with the false universal theorem, the true geometric theorems, and a few precise remaining questions. Avoid “ends the field,” “complete characterization,” and any inference from exceptional exact failure to routine numerical unreliability.

## Length and proof completeness

The default is a Mathematical Programming-style regular article. Roughly 30–35 pages is an initial editorial budget, not a journal rule. Apply the live policy check before selecting a class or final length. The earlier proposed 35–45-page outline was a broad outline, not a SIOPT-compliant plan.

All mathematical dependencies indispensable to advertised article results must have proofs in the article, its in-document appendices, or genuinely established external references. An unpublished companion written for this same project is not a device for making the article's central proof optional. Computer-assisted proofs may cite deposited code for reproducibility, but the mathematical objects, certificate soundness argument, verified bounds and deduction must be readable in the paper.

If the complete set does not fit, select a coherent core rather than using tiny fonts or removing arguments. Every incomparable omitted result remains fully developed in the companion. Do not silently split into a series of journal submissions.

## Abstract specification

Use a single paragraph, 150–250 words, predominantly prose. State the algorithm, the headline negative quantifiers, the positive geometry, the methodological contribution, and the formal-verification scope actually available. Do not overload it with every extension or numerical constant. Distinguish the two negative regularity regimes in one sentence if both are article results.

Possible final sentence: “These results separate strong regularity within smooth branches from the geometric conditions that enable convergence, without providing a necessary-and-sufficient classification.”

## Reader tests

- A graduate student in optimization can explain the positive/negative contrast after Section 2.
- A specialist can find the exact hypotheses of every main theorem without opening Lean.
- An auditor can reach the exact Lean contracts and proof dependencies from the companion ledger.
- Removing the companion from the reading desk does not break the article's main mathematical argument.
