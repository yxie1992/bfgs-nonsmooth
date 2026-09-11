# Incoming-jump obstruction peer review

Reviewed `BfgsVerification/IncomingJumpObstruction.lean` and its definitions in
`TransportedCertificateDefinitions.lean` against Module G, Section 2,
Proposition `G:prop:star` and its basis-limit corollary. This is a statement and
proof dependency review; comprehensive root compilation and environment-wide
axiom enumeration are recorded separately.

Verdict: no mathematical or quantifier defect found in the reviewed tranche.

## Exact pair and field quantifiers

- `EligiblePair` includes actual `HasFDerivAt` facts at both endpoints, positive
  predicted decrease, both decrease inequalities, and the weak-Wolfe curvature
  inequality. Every predecessor is `x a j`; every pair shares the same actual
  target `z a` and gradient `h a`. The jumps and curvature products are computed
  as `h a - g a j` and their dot products with `z a - x a j`.
- The target and every predecessor lie in one fixed band. The finite family is
  indexed by `Fin r`. The general nontrivial filter formulation includes the
  source's epsilon limit and sequences. It cannot infer a contradiction from
  a trivial filter, since the obstruction explicitly requires `[NeBot l]`.
- Predicted decreases tend to zero separately for each predecessor. A finite
  intersection derives a common tail where all decreases are below the
  candidate certificate's positive threshold. No threshold is chosen in
  advance or permitted to vary with a predecessor or target parameter.
- `VisibilitySecantCertificate` contains precisely the relevant field, positive
  visibility constant, finite real secant constant, positive threshold, PSD,
  visibility, and all-small-eligible-pair suppression conditions. The exclusion
  of `BandCertificate` follows by forgetting its transport field. The proof
  never calls or assumes transport.
- The theorem does not need the source's ambient compactness, convexity,
  attained-minimum hypotheses, or eta positivity once the exact pair/band data
  are supplied. Their omission makes this local obstruction more general and
  does not strengthen its premises. The source's `c₂<1` is retained to derive
  positive curvature from eligible positive predicted decrease.

## Algebra and possible hidden regularity

The proof factors each individual finite PSD matrix as `Aᵀ A` and proves the
seminorm finite-sum triangle inequality through the Euclidean norm. There is no
selection regularity premise on this factorization. Singular matrices and an
empty family are permitted; an empty representation makes visibility fail
directly. The weight estimate uses `sqrt(max C 0)`, handling every finite real
secant constant without adding a sign assumption on C. Nonnegative curvature
justifies this replacement.

The representation is an eventual exact equality, not a limiting approximation.
The weighted coefficient sum is assumed to tend to zero exactly as in the
source. Its product with the fixed suppression constant tends to zero, whereas
visibility keeps the same seminorm at least `sqrt(m)>0`. No boundedness,
continuity, matrix convergence, rank, or positive definiteness of W is assumed.
No common BFGS history is required or silently added.

## Basis-limit coefficient construction

The actual jump matrix has these incoming jumps as columns. Columnwise
convergence gives matrix convergence to the supplied basis matrix; the basis
proves a nonzero determinant. The code derives eventual invertibility by
determinant continuity and inverse convergence by the matrix-inverse theorem.
It defines the coefficients by the actual inverse matrix applied to the target
gradient and proves the exact representation on that tail.

A fixed bound on target gradients gives coordinate bounds. Convergent inverse
entries then bound each coefficient; each curvature tends to zero, and the
finite sum of coefficient-weighted square roots tends to zero by squeezing.
There is no target-gradient limit premise. The stored `Vec` norm is the finite
Pi norm; a Euclidean bound from the source gives the needed coordinate bound,
and the proof requires no additional norm control. The full basis corollary
therefore derives the coefficient hypothesis rather than assuming it.

The parent source paragraph's separate first-step realizability construction
and the later pointwise-feasibility equivalence are not proved by this file and
must remain separate coverage items. This does not affect the incoming-jump
proposition or its basis-limit corollary.
