# Remaining semialgebraic affine-critical-value infrastructure

The compact affine-gap paragraph is now independently compiler-checked in the six-file main tranche described by `audit/A_AFFINE_GAP_VERIFICATION.md`. The next unproved retained claim in Module A is proposition `A:semialgebraic`: a finite convex semialgebraic objective attaining its minimum has an interval above that value containing no nonoptimal affine-critical values. This claim must not be replaced by an assumed finite decomposition or by an assumed finite set of critical values.

## Precise source proof dependencies

1. A genuine semialgebraic-set definition for finite-dimensional real spaces, preferably finite Boolean combinations of polynomial equalities and strict inequalities, and a function predicate using the actual graph.
2. Closure under coordinate projections, equivalently a proved real-closed-field quantifier-elimination theorem. The actual subgradient graph uses the quantified inequality `∀z, F(z) ≥ F(x)+g·(z−x)`, so Boolean operations alone do not supply this step. A pointwise representation of the graph of F must also be substituted without assuming F is polynomial or globally smooth.
3. A proved finite affine representation lemma with at most n+1 actual subgradients for each point of the affine hull. Coefficients may be negative, so ordinary convex Carathéodory cannot simply be substituted. This algebraic dimension bound is separately tractable using a finite affine basis.
4. Projection closure applied to that bounded affine representation gives semialgebraicity of the actual affine-critical set, including all degenerate subdifferentials.
5. Finite semialgebraic path-connected decomposition, with piecewise C¹ paths, and piecewise C¹ regularity of the composition with a semialgebraic scalar objective. Ordinary topological connected components alone do not give either finiteness or the differentiable path/composition required here. This is a substantial real-algebraic geometry layer; a declaration requiring these properties as inputs is only conditional infrastructure.
6. The ordinary calculus bridge: along a differentiable path where F composed with the path is differentiable, the two-sided supporting-plane inequality forces its derivative to equal g·p′ for **every** actual support g. Affine zero then forces the derivative to vanish. Finite piecewise C¹ intervals and continuity give constancy along each path component.
7. A finite-image real-order argument picks a positive gap above the attained optimal value (or any positive gap if the critical-value image contains no larger value). Convexity converts optimal value into actual zero subgradient membership.

## Pinned-library assessment

The source search is recorded in `audit/scratch/affine_gap/semialgebraic_search.log`, against the project's pinned mathlib. It finds no semialgebraic-set/o-minimal/cell-decomposition/real-closed-field quantifier-elimination API furnishing steps 1, 2, or 5. Existing `ModelTheory/Definability.lean`, ring definability, and the basic algebraically closed field files provide general first-order infrastructure, not these ordered-real geometric theorems. Existing polynomial and ordered-field decision tactics can verify fixed polynomial identities and inequalities; they do not establish projection closure or a finite path decomposition for arbitrary semialgebraic sets.

The obstacle is therefore an absent geometric proof layer, not a missing compiler or a need for unchecked numerical computation. Encoding “semialgebraic” as “has a finite smooth path decomposition” would silently strengthen the source hypothesis and is not an acceptable completion. Using an external symbolic/CAD computation without a checked proof certificate would also fail the project's verification contract.

## Constructive next tranches

The next bounded implementation can prove steps 3, 6, and 7 as independent ordinary Lean theorems with explicit inputs and clearly conditional status. The source predicate can then be introduced with Boolean polynomial syntax and its elementary closure laws, without any axioms. Completing the unconditional proposition subsequently requires an actual projection/elimination construction and the associated finite semialgebraic path regularity theorem, or importing a separately kernel-verified development with compatible definitions and pinned dependencies. A second route via a nonsmooth definable Sard theorem has the same missing definability/stratification burden and is not a shortcut unless those theorems are proved.

No new mathematical assumption, external oracle, decomposition axiom, or unconditional semialgebraic theorem has been added in the present tranche. The separate general-dimensional BFGS conjecture at the end of Module A remains outside the retained proved results, even after finite critical values are eventually established.
