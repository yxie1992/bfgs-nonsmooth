# Module H.B / H.C proof design after checked H.A

Source H.tex was read in full. No new Lean files were created during the frozen
milestone audit. This document records proposed exact APIs and dependencies;
it does not claim that the later obligations have been verified.

## Recommended next bounded coding tranche: H.B

1. `HomogeneousMaxLinear.lean`: finite nonempty maxima of actual dot products,
   convexity/homogeneity, active-slope support, and derivative/active-slope
   identities. A representation can use a nonempty `Finset (Vec n)` and
   `Finset.sup'`, keeping duplicate original indices irrelevant.
2. `HomogeneousAffineGeometry.lean`: an affine-separation-to-common-component
   lemma and finite-range recurrence facts, independent of BFGS.
3. `HomogeneousAffineObstruction.lean`: fixed-normal Hessian energy contradiction,
   followed by recurrent-affine-zero and full-slope common-tilt escape exports.

The smallest immediately useful subtask is (1): it supplies actual accepted
finite-gradient alphabets to both H.B and H.C without assuming a gradient oracle
returns a slope.

## Finite maximum / differentiability APIs

Propose `finiteMaxLinear A hA x := A.sup' hA (fun a => dot a x)`.
Needed conclusions:

- The finite maximum is real-valued, convex on all space, and positively
  homogeneous, including scalar zero and zero-dimensional ambient spaces.
- Every point has an active slope (`Finset.exists_mem_eq_sup'`).
- Every active slope a supports the maximum globally and attains its value at x.
- If the maximum has derivative `gradientFunctional g` at x, every active slope
  equals g, hence g belongs to A. Do not replace this with an assumed finite
  alphabet. A direct proof applies Fermat to `F(z)-dot a z`, which has a global
  minimum zero at x; `IsLocalMin.hasFDerivAt_eq_zero` then identifies the linear
  functionals. Coordinate evaluation at `Pi.single i 1` identifies their vectors.
- Conversely, if all active slopes coincide as vectors, the finite maximum
  equals that linear form on a neighborhood and is differentiable there. Finiteness
  gives a positive margin against inactive slopes. This converse is useful when
  constructing the actual projected run after discarding nonrecurrent slopes.

There is no need to assume unique active *index*: duplicate slopes are harmless.
The source's current-gradient pairing bounds should remain actual dot products.

## Affine separation and recurrent gradients

Define recurrent gradients by `frequently` at the natural-number atTop filter:
`G := {v | ∃ᶠ k in atTop, g k = v}`. Available mathlib facts include
`Nat.frequently_atTop_iff_infinite` and `Set.Finite.eventually_all`.
For a finite range of g, prove that G is nonempty, G is a subset of that range,
and eventually every g_k lies in G. For each nonrecurrent range element,
non-frequent equality gives eventual inequality; take the finite intersection.

Required affine lemma:

```
S.Nonempty → (0 : Vec n) ∉ affineSpan ℝ S →
  ∃ v : Vec n, ∀ g ∈ S, dot v g = 1
```

A proof route avoids analytic separation. Choose g0 in S and let D be the
direction submodule of its affine span. If zero is outside the affine span,
g0 is outside D. `Submodule.exists_dual_map_eq_bot_of_nmem` supplies a linear
functional f annihilating D with f(g0)≠0 (the quotient over ℝ is free). Every
`g-g0` lies in D by `AffineSubspace.vsub_mem_direction`, so normalize f by f(g0).
Represent the resulting functional by its values on `Pi.single i 1` to obtain
an actual vector and dot product. This route requires no closedness assumption.

For the matrix contradiction, retain a reusable algebraic lemma on
`FullBFGSRun`: positive fixed beta bound and summable d, plus a fixed vector v
with v·g_k=1 on a tail, are incompatible. Prove the actual inverse-Hessian
identity using the existing `hessianUpdate` theorem. Then v·y=0 and

```
metricEnergy (H_{k+1}⁻¹) v = metricEnergy (H_k⁻¹) v - 1/q_k.
```

Positive energy bounds reciprocal sums, contradicting the verified matrix
reciprocal theorem. Objective-level Armijo/lower-bound wrappers discharge
summability. This keeps the source's observation that H.3 does not actually
need homogeneity or convexity visible in the algebraic API; a theorem only over
`AdmissibleBFGSRun` would unnecessarily obscure that generality.

For finite max-linear objectives, derivative membership yields finite range;
`0∉affineSpan A` implies `0∉affineSpan G` by monotonicity, so a finite value limit
is impossible. Objective antitonicity then proves value escape. The common-tilt
family can use its explicit fixed last-coordinate vector. No finite termination
claim is justified. The |G|≥r+1 corollary needs the dimension of the span of
differences, not just a count of gradient values.

## Effective-subspace reduction: exact matrices first

For a tail gradient subspace with orthonormal column matrix U, prove:

- hatted gradient/step matrices are actual Uᵀ projections; compressed
  `Hhat_k=Uᵀ H_k U` is SPD.
- The projected full inverse-BFGS update is exact when g_k and y_k lie in range U;
  q, d, t and accepted-value inequalities are preserved.
- All tail steps lie in the fixed image `H_K range(U)`. One useful stronger
  invariant is `H_k U = L_K (Uᵀ H_k U)` with
  `L_K=H_K U (Uᵀ H_K U)⁻¹`. Establish it by the actual inverse update, then
  telescope `s_k=L_K(Uᵀs_k)` to get H.7.1 and H.7.2.
- Never replace the compressed inverse `(Uᵀ H_k U)⁻¹` by `Uᵀ H_k⁻¹ U`.

If the projected objective is reconstructed from recurrent slopes only, prove
that it has exactly the original accepted objective values: the current gradient
is recurrent and active; every recurrent slope is an original supporting slope.
The derivative converse above then supplies actual differentiability of the
projected maximum. Alternatively, the planar endpoint arguments can operate on
original values and projected pairings without first packaging a new run.

## H.C and general planar finite-limit branch

H.A supplies strictly positive values and d→0. Euler and the accepted-step
identity give the two endpoint pairings tending to zero. For each independent
pair of slopes in dimension two, form the actual 2×2 row matrix and its inverse.
Finiteness of the slope set gives a uniform bound over independent pairs; if
there are no independent pairs, enter the fixed-line case rather than taking a
maximum over an empty set.

Prove separately:

- Identical nonzero consecutive gradients violate weak Wolfe.
- Distinct positive multiples cannot both be active at positive-valued points;
  dependent nonzero planar transitions must therefore be opposite slopes.
- An opposite pair among global slopes makes their maximum nonnegative
  everywhere, excluding global unboundedness below.

Thus every transition is independent in the planar unbounded-below case, giving
point convergence to zero on the finite branch. The escaping branch's norm
limit can be proved from bounded homogeneous supports, or more generally from
finite-convex continuity and compactness of each bounded ball: objective values
tending to minus infinity eventually leave each such ball. No direction limit
should be added. Convexity rules out stationary points of an unbounded-below
objective.

For general planar finite-value branches, define anchor indices as endpoints of
independent transitions. On a block between consecutive anchors, all *starting*
gradients through the step arriving at the next anchor lie on one gradient line;
the final update may leave that line, but its next step is outside the block.
This indexing point is essential for the fixed-primal-line proof.

If the first dependent pair is g and −κg, κ>0, prove the exact identity
`d_a=f_a+f_{a+1}/κ`, the Armijo contraction, and the source interpolation bound
`0≤theta≤(1+1/κ)/c1`. The denominator has magnitude at least c1*f_a and f_a>0
is supplied by H.A. Finitely many opposite slope pairs yield one uniform theta
bound, irrespective of block lengths. With infinitely many anchors, bound all
points between sufficiently late consecutive anchors. With finitely many
anchors, the gradient line and primal line are fixed on a tail; finite nonzero
slope multipliers and SPD give a unique limiting intersection with the zero
slope hyperplane. Dimension zero is incompatible with nonzero gradients;
dimension one is this fixed-line case, and dimension two is the anchor argument.

## Section 8 / scope checks

Relative-interior zero in the convex hull of slopes, relative to their span,
must imply a positive Euclidean ball in that span and hence coercivity of the
projected support function. Then use H.A and exact lifting to obtain the metric
projection formula, including its independence from accepted lengths.
The recurrent-tail version needs the preceding reduced-objective bridge.

No gap was detected in the source's block argument on this design review, but
these steps are still obligations, not formally verified results. The open
source question for recurrent span at least three remains explicitly open.
