# Introduction storyboard: establish the question before the theorem inventory

This is an editorial model, not a paste-ready proof statement. Insert normal bibliography citations and exact article theorem references; use current corrected contracts for all claims. The paper can use its existing title or a broader accurate title such as “BFGS on Convex Nonsmooth Functions: Convergence, Failure, and Geometric Conditions.” Avoid “complete characterization.”

## Paragraph 1 — The problem that the community recognizes

Start from unmodified BFGS as an algorithm designed around smooth gradient changes, yet empirically successful on nonsmooth objectives. Connect to the smooth-convex theory, then state why gradient jumps make that transfer nontrivial. The question is whether ordinary BFGS still finds minimizers and what makes the successful behavior possible.

Do not begin with our notation, formalization counts, finite-cell definitions, or a catalogue of exceptions.

## Paragraph 2 — The challenge and its actual meaning

Explain Lewis--Overton's observations and their broad challenge. Keep almost-sure initialization and semialgebraic scope explicit in a compact sentence. The paper studies deterministic convergence/failure in the convex setting; this is an important part of the landscape, not a claimed resolution of all parts of their challenge.

## Paragraph 3 — Real progress and the remaining bottleneck

Connect Guo--Lewis's smooth-extension/Powell approach, Euclidean-norm result and partial mixed-benchmark conclusion; Xie--Wächter's two-piece escape; and the more recent conditional analysis of Gebken. Do not imply the same assumptions occur in every paper. The remaining difficulty is deriving the needed behavior from objective assumptions instead of assuming iterate/matrix asymptotics or relying on very special structure.

## Paragraph 4 — The memorable unresolved example

Display F(u,v)=u^2+|v|. Explain why convergence to some point of v=0 is not convergence to the minimizer: u still has to approach zero. The new whole-sequence conclusion should be explicit and cited to our theorem. Mention that it follows from a family result rather than a one-off two-dimensional recurrence.

## Paragraph 5 — What this paper changes

A possible transition:

> This paper gives complementary answers to the convergence question. We construct convex objectives for which a fixed Armijo--weak-Wolfe implementation of full BFGS converges to nonstationary points, even from starting points arbitrarily close to a unique minimizer. At the same time, we establish global and local convergence for broad classes of nonsmooth convex objectives, including the mixed quadratic--absolute-value benchmark. The positive results follow from objective-level conditions and do not assume convergence of the iterates, bounded condition numbers, or a prescribed spectral limit of the BFGS matrices.

Use “objective-level conditions” rather than “no assumptions”: admissibility, convexity and the relevant compactness/geometric assumptions remain.

## Paragraphs 6–8 — Three contributions, each with a consequence

### Failure and its significance

State the deterministic global and local conclusions and the two incomparable regularity regimes in readable prose. Explain what theorem each example rules out. State once that the exceptions need not have positive measure and thus do not settle the full Lewis--Overton challenge. Put technical parameter ranges in the precise theorem statements.

### Positive theory and the questions it answers

Name the global centered smooth--sublinear theorem, the compact homogeneous/max-linear consequence, and the local finite-partition/polyhedral theorem. Select and prove a nonradial extension in the article if the general transported framework is a headline. Make the u^2+|v| resolution explicit. Distinguish newly settled cases from known corollaries such as the Euclidean norm. Use “local” and “global” deliberately, not interchangeably.

### A reusable analytical approach

State the connection from adjacent principal-minor degrees to reciprocal metric-gradient growth and comparison-energy bounds. The new strategy accommodates singular metric behavior rather than establishing or assuming a full spectral description. Credit classical matrix-potential analysis while naming the specific added result.

## Paragraph 9 — The unifying insight

Possible wording:

> The positive and negative results concern the same tension. Gradient jumps can dominate secant information even when the smooth branches have controlled curvature. In the successful classes, a comparison direction—or a suitably varying comparison geometry—continues to measure the remaining objective gap without incurring an uncontrollable secant correction. In the counterexamples, an explicitly realized sequence of branch changes supports contraction around a nonstationary configuration. The results therefore distinguish several geometries that guarantee progress from regularity assumptions that do not guarantee it; they do not assert a complete success/failure classification.

This interpretation must remain tied to the established results. Do not infer that every corner with a full jump span fails or that every successful run admits the chosen certificate.

## Paragraph 10 — Reader roadmap and formalization

Give a short roadmap reflecting the new article structure. One sentence can announce the Lean-checked companion and exact correspondence. Formal verification supports confidence in the proofs; it does not substitute for the mathematical story, readable arguments, or literature positioning.

## Before/after example of contribution language

Too weak:

> Our assumptions differ from earlier work, and the companion contains several additional results.

Better:

> Guo--Lewis established the existence of a subsequence approaching the nonsmooth line for u^2+|v|. Our centered-composite theorem proves convergence of the entire sequence to its unique minimizer, for every admissible full-BFGS run and arbitrary positive-definite initialization. The same argument applies in arbitrary dimension to the stated smooth--sublinear class.

Too broad:

> We disprove the Lewis--Overton conjecture and characterize convex nonsmooth BFGS.

Better:

> The counterexamples disprove unrestricted deterministic global and local guarantees for the specified regularity classes and line search. They do not establish positive-probability failure in the semialgebraic setting of the Lewis--Overton challenge.

Too machinery-led:

> Assume there exists a positive-semidefinite field satisfying (V), (S), and (T).

Better before the formal statement:

> A comparison geometry must retain information about nonoptimality, control the secant changes seen in its directions, and move without introducing an excessive energy cost. The next theorem formulates these three requirements using only objective data and eligible endpoint pairs.
