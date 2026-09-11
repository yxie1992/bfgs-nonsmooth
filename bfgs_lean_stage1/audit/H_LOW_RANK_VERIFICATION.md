# H.7.4 and remaining H source assertions — compiled scope

The final import is `BfgsVerification.HomogeneousSourceConsequences`. Thirteen
new modules contain 66 public theorems and four concrete definitions. The actual
pinned-toolchain build and all 70 transitive declaration closures are recorded
in `audit/homogeneous_lowrank_full_build.log` and
`audit/homogeneous_lowrank_axioms.log`. Every closure uses only `propext`,
`Classical.choice`, and `Quot.sound`. No source contains sorry/admit, a custom
mathematical axiom, native_decide, or unchecked external computation.

Reproduce after `source scripts/env.sh`:

```
lake build BfgsVerification.HomogeneousSourceConsequences
lake env lean audit/H_LowRankAxiomChecks.lean
```

## General planar finite-value branch

`HomogeneousBlockAlgebra` proves that dependent accepted transitions on a
positive homogeneous branch are between opposite gradients, derives the exact
Armijo contraction `(1-c1)/(1+c1/kappa)`, and proves the source interpolation
parameter bound. `HomogeneousBlockTransport` proves finite-prefix matrix/step
lifting. Gradients through N suffice for the point N+1: the final arriving
endpoint's new gradient need not lie on the old gradient line. This boundary
point is essential for consecutive independent-transition anchors.

`HomogeneousBlockControl` derives actual collinearity and the bound
`norm x_k <= (1+C) norm x_a + C norm x_b` throughout a finite dependent block.
`HomogeneousPlanarFiniteValue` derives a uniform C from the finite actual slope
alphabet using `abs (dot g g / dot g h) = 1/kappa` for an opposite pair. No bound
on the block length is imposed. Its actual independent anchors are uniformly
small by the previously checked two-endpoint pairings and finite inverse-pair
bounds. `HomogeneousBlockStitching` selects consecutive anchors around each
late index using a finite maximum and least future anchor. It proves whole
sequence convergence when anchors are cofinal, without a bounded-gap premise.

If anchors are not cofinal, all tail gradients lie on the actual initial tail
gradient line. `HomogeneousLowRankLine` derives a uniform inverse multiplier
bound from the finite nonzero gradient alphabet, hence the slope coordinate
converges to zero. The exact full-BFGS lift gives the tail's actual point limit.
The metric or points are never assumed bounded.

The final planar exports are `maxLinear_planar_zero_branch_has_limit`,
`maxLinear_planar_finite_value_has_limit`, and
`maxLinear_planar_lower_bound_has_limit`. A finite value L is proved zero before
the point theorem is applied. The lower-bound theorem assumes a bound only
along accepted values, not compactness or a finite limiting value.

## Recurrent effective rank at most two

`HomogeneousLowRankProjection` proves the exact finite-max representation after
orthonormal projection, including duplicate projected slopes. It also derives
orthonormal coordinates with their actual finrank. A genuinely projected
admissible run is constructed through the already checked derivative,
compression, SPD, and full-update bridge; its convergence is proved from the
one- or two-dimensional theorem. Rank zero is excluded by the actual nonzero
accepted gradient condition rather than a new rank assumption.

`HomogeneousLowRankConvergence` derives the recurrent finite tail and restricted
max-linear run using H.8's checked local-germ derivative preservation. Only the
restricted objective is globally projected. The original objective and its
recurrent restriction are identified at accepted points only. Original
F(limit)=0 follows by continuity of the original finite convex objective.

`maxLinear_recurrent_span_le_two_finite_value` takes the actual finite maximum,
an actual run, the exact hypothesis
`finrank (span (recurrentValues R.g)) <= 2`, and a finite value limit L. It proves
L=0 and an actual full ambient iterate limit with original F=0. The
`..._lower_bound` export derives convergence from a lower bound on accepted
values. The original limit is allowed to be nonzero, as required by H.7.4.

## Remaining H.8 scope and H.5.3 displayed deductions

`HomogeneousRelativeInteriorCharacterization` proves exactly:
zero lies in the relative interior of conv(A) in span(A) iff the actual finite
maximum is nonnegative and its zero fiber is a linear submodule. The reverse
implication derives strict positivity on the slope span. The interior ball is
then proved by coercivity plus continuous linear separation of the actual
finite convex hull; no ball, coercivity, or relative-interior premise is added.
`HomogeneousClassCorollaries` instantiates actual finite polyhedral seminorms,
even finite maxima, and nonnegative finite-max gauges with a linear zero fiber.
The gauge theorem includes the unique initial-H-inverse metric projection.
It also proves there is no infinite nonstationary run for an identically zero
objective, regardless of how that objective is written.

`HomogeneousPotentialConsequences` exports the H.5.3 inequalities that the
alternative H.A proof did not previously export: antitone potential, the exact
reference-energy bound Phi0-gamma L, finite and infinite weighted reciprocal
budgets, weighted summability, actual SPD metric Cauchy-Schwarz, and the displayed
pointwise F_k^2 <= (Phi0-gamma L) q_k. Only an actual accepted-value lower bound
is needed for these budgets.

`HomogeneousSubspaceProjection` separately closes H.7.1's algebraic distinction:
a genuine compressed `FullBFGSRun` and original accepted Armijo/Wolfe inequalities
are derived solely from gradient membership, even without global factorization
of the original objective. Actual q,d and curvature are preserved, and the
compressed matrices are SPD. The previously checked affine lift supplies the
fixed image and current-tail limit formula. The reduced Hessian is the inverse
of the compressed inverse-BFGS matrix.

`HomogeneousSourceConsequences` exports the source supporting-vector unit
normalization bound, exclusion of all opposing slope pairs in the globally
unbounded-below case, the exact h+ell curvature decomposition, both accepted
decrease inequalities, and positive actual recurrent-span rank.

## Full H source review and limits

H.tex was reread in full after these proofs. All internal retained mathematical
claims now have proofs: H.A, H.B and its cardinality/common-tilt consequences,
main planar H.C, the broader H.7.4 recurrent-rank theorem, H.8 and its class
specializations, and the displayed homogeneous energy deductions. No mathematical
correction to H.tex was needed and the original source is unchanged. The source's
unresolved zero-value iterate question for noncompact recurrent rank at least
three remains unresolved and is not promoted into a theorem.

Historical priority statements, the external two-piece finite-termination paper,
and references to an earlier exact three-gradient example remain provenance or
cross-module references, not new claims proved by H.tex. The current report-wide
status must continue to track those references and all other modules separately.
This scoped audit is not a claim that the entire research report is verified.
