# Independent author-side review of the positive article proofs

Reviewer: a separate AI agent from the proof author, working in the same
project. This is a mathematical and source review, not human peer review and
not a Lean build or an axiom audit. The accompanying JSON fixes the exact
reviewed source hashes. The current article proves only the inward-to-radial
implication; the converse is explicitly retained in the companion.

**Finding:** no blocking mathematical gap identified in the reviewed positive
proof chain. The essential planar field construction, endpoint estimates and
nonradial example are proved in the article. They are not outsourced to a
script, Lean declaration or companion theorem. Formal correspondence remains
a separate release check; this review does not certify every transitive Lean
dependency.

## Global results and localization

The inward model argument applies the estimate at the correct endpoint in
both signs of the radial numerator. Its auxiliary scalar is bounded by twice
the product of the gradient and radius bounds; the small-step and threshold
choices yield the displayed uniform positive-band constant, including zero
model constant. The radial rank-one field retains the gap by convexity, and
its projection is unchanged after adding the actual step. No radial BFGS
step is assumed.

For the centered family, the compact initial sublevel is contained in the
open representation region. A finite local Lipschitz cover and subdivision
of segments give a uniform gradient bound for the smooth term there. The
homogeneous term's directional derivative cancels its inward remainder.
Neither summand must have its own minimum at the center. The mixed benchmark
has the exact remainder stated in the proof, compact sublevels and a unique
minimizer. The homogeneous examples have no affine intercepts; coercivity or
the stated bounded-sublevel hypothesis rules out a nonpositive value on a
nonzero ray.

The localization lemma correctly uses uniqueness and compactness of a sphere
to obtain linear growth outside a ball. Consequently a finite convex
objective with an attained unique minimizer has compact sublevels. The
finite-cell proof keeps inward segments in a surviving closed convex cell
and needs only radial equality of derivatives at cell boundaries. The smooth
extensions themselves need not be convex. Residual norms that do not vanish
at the minimizer are smooth nearby; vanishing residuals are centered
sublinear terms, as claimed.

## Planar cluster argument: the length-local scope is essential

Strict positive contours exclude a nontrivial limiting accepted chord:
supporting and convex upper bounds force the entire chord onto one positive
level. Such a level is on the boundary because the objective has a lower
attained minimum. This proves that step lengths tend to zero before the field
estimates are applied.

The planar lemma gives estimates for sufficiently short endpoint distances.
It does **not** claim a global certificate merely from a small predicted
decrease. The cluster proof correctly applies the lemma to the full compact
cluster set, proves the iterates eventually lie in its neighborhood, and
uses the separately proved short-step property. Its energy recurrence keeps
the nonnegative projected quadratic form intact when the multiplier bound
is used. Product normalization is justified by the summable predicted
decreases; it contradicts arithmetic-mean divergence of the reciprocal
metric-gradient quantity. No convergence to one cluster point or metric
limit is assumed in constructing the field.

## Construction of one field and all its endpoint estimates

1. **Finite corner geometry.** An invertible two-branch value map gives
   exactly one nonsmooth point of the selected level in each regular corner
   chart. Smooth charts contain none. A finite buffered cover of the compact
   regular set therefore leaves finitely many corner curves. Shrinking the
   common level interval and neighborhood captures nearby corners on those
   curves, without assuming finitely many later algorithmic switches.
2. **Compatible normal arcs.** Two different corners cannot share a
   supporting normal, because its exposed face would contain their boundary
   segment. The finitely many compact normal arcs are separated. Their
   positive pairing with the corner velocity permits fixed disjoint angular
   cutoff supports after shrinking the level interval. The resulting height
   function is uniformly positive; it is not asserted to be a convex support
   function.
3. **Regularity and visibility.** On each cutoff plateau the angular formula
   equals the corner velocity evaluated at the objective value on both
   smooth sides. This gives a locally Lipschitz extension across the jump,
   equal pairing with all active subgradients, and uniform visibility on a
   compact buffer. At smooth points the gap and bounded distance to a
   minimizer give the required gradient bound away from zero.
4. **Uniform transversality.** A sequence of failing short pairs coalesces
   on the compact buffer. Closedness of the convex subdifferential graph and
   common positive pairing force the step limit to be the negative field
   direction. The predicted decrease divided by step length then has a
   positive limit, whereas the secant curvature divided by length tends to
   zero. This contradicts weak Wolfe. It controls every point of the segment.
5. **Signed determinant transport.** In the oriented basis used by the
   manuscript the determinant has the displayed sign. Angular cancellation
   makes the field derivative triangular. Its determinant derivative divided
   by the nonzero determinant is bounded by a constant times the absolute
   directional value derivative. At switches the corner formula supplies
   the one-sided chain rule. Convexity gives the lower derivative bound
   needed to charge total motion to the endpoint decrease. The proof of the
   one-sided comparison principle is valid and does not presume finitely
   many switching intersections. The determinant keeps one sign, so the
   transport multiplier is positive and the logarithmic bound yields the
   required multiplicative energy estimate.
6. **Same-field secant estimate.** In a smooth chart the tangent-subtracted
   descent step stays in a larger convex buffer for close endpoints and gives
   the one-sided Bregman estimate. With different branches, the leading
   gradient jump pairs to zero at a segment tie point. Lipschitz bounds then
   leave a quantity of order step length. The uniformly invertible two-row
   gradient matrix, weak Wolfe and absorption of the quadratic remainder
   bound curvature below by a constant times step length. A finite buffered
   cover makes all constants and distance thresholds uniform.

## Smooth maxima and the explicit nonradial basin

The augmented gradient matrix has full column rank near the minimizer.
Its least-squares expression is continuous and coincides with the strictly
positive multiplier vector when the affine equation is solvable. An affine
balance using only active gradients, padded with zero coefficients, must
therefore use every retained branch and be a convex balance. The proof of
the finite smooth-maximum subdifferential formula includes the needed
local-to-global support argument and the separating-direction converse.
In the plane, at most three affinely independent branches remain; a
non-affine-critical point has at most two active branches, and a distinct
dependent pair would have an affine line containing zero. Thus the stated
regular two-branch geometry follows. Localization and strict contours are
chosen from the objective, before the initial metric and line-search constants.

For the three quadratic branches, the Hessian bounds, averaged quadratic,
augmented determinant, multiplier numerators and their exact lower bounds
on the radius-1/10 box are correct. The sublevel at 1/100 lies in that box.
The same positive-coefficient argument establishes affine correctness and
regularity there, so the explicit numerical basin follows from the planar
theorem, not merely from an unspecified local basin.

For the radial obstruction, the displayed square-root curve satisfies the
tie equation and has ratio v/u tending to one. The third branch is inactive
for sufficiently small positive u. The radial jump divided by u squared
tends to minus one half and is therefore nonzero. Opposite nearby endpoints
have exactly the displayed predicted decrease, curvature and value decrease.
Their limiting ratios ensure eligibility for the stated fixed constants.
Fixing one sufficiently small positive u before letting the transverse
separation vanish yields one positive band with an unbounded radial quotient.
Then choosing u arbitrarily small places such an obstruction in every
neighborhood. This is a family of eligible endpoint pairs, not a purported
full-BFGS trajectory.

## Reproducible independent algebra check and limits of this review

Run `python3 editorial/narrative_rebuild/narrative_positive_algebra_check.py`.
The adjacent JSON output records the checker and reviewed local-source
hashes. It uses standard-library rational arithmetic and sparse polynomial
identities to check the displayed Hessians, multiplier identities, box
bounds, radial jump modulo the tie relation, and eligible-pair formulas.
Its result is **PASS**. This computation is an independent audit aid; the
paper supplies the mathematics and does not invoke this program as a proof.
Analytical compactness, limiting and square-root arguments were reviewed
directly, not inferred from numerical sampling.

The proof author reports that the new benchmark wrapper compiled and that
the example calculations are linked to the complete C.span.13/C.span.14
exports. Those reports are tracked by the integrated formal-correspondence
review. I did not independently rerun Lean in this bounded review, and do
not treat that reported result as a substitute for inspecting theorem
contracts or axiom dependencies.
