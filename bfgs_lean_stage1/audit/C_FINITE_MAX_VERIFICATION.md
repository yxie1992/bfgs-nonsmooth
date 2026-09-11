# Module C nondegenerate finite-max application

This five-module tranche contains 13 explicit declarations and two exact targets, all freshly rebuilt under the pinned Lean toolchain. Complete actual types and standard transitive axioms, strict exact-target checks, and five unchanged source hashes passed; see `validation.log`, `source_hashes.json`, `build.log`, `axioms.log`, and `contracts.log`. The delivered main import is `BfgsVerification.PlanarFiniteMaxTargets`.

## Source `C:cor:max`

`planarFiniteMaxLocalBasin : PlanarFiniteMaxLocalBasinTarget` proves the actual source local-basin corollary. The objective is finite convex on the entire plane and has the stated unique minimizer. Only an actual local representation by finitely many convex C² branches is assumed. Only the gradients of the branches originally active at the minimizer need be affinely independent and admit strictly positive optimal weights. The other geometric hypothesis is precisely an interval of positive low sublevels whose boundary contains no nontrivial segment.

The proof removes the originally inactive branches by the existing proved local reduction, derives their actual coordinate gradients and continuity from C² regularity, and applies the actual augmented-Gram barycentric-stability theorem. This supplies local rank persistence and actual affine-critical correctness. No finite active alphabet or eventual fixed active set of the iterates is assumed.

The planar regularity bridge proves that at every non-affine-critical nearby point at most two independent gradients can be active. A singleton means the actual objective equals one C² branch on a neighborhood. Two active gradients are distinct; if their determinant vanished, their affine line would contain zero, contrary to the actual noncritical premise. The two-branch chart retains branch convexity and C² regularity on an actual open ball. This is the exact `ConvexTwoBranchRegularAt` contract used by the principal planar theorem.

The main planar local theorem then chooses the basin before every actual admissible full-BFGS run. Every SPD initial matrix and every fixed valid Armijo–weak-Wolfe parameter pair is included through the run structure. Both objective-value and full-iterate convergence are conclusions; there is no assumed convergence, condition-number bound, matrix limit, field, transport, or secant bound.

## Actual Hessian sufficient replacement

`planarFiniteMaxHessianBasin : PlanarFiniteMaxHessianBasinTarget` replaces the strict-contour hypothesis by a common μ>0 and the actual Loewner bound

`(RadialHessian.matrix (f i) x - μ • I).PosSemidef`

for only the originally active branches on a neighborhood. The matrix is constructed from the actual second Fréchet derivative; it is not a supplied Hessian approximation. No strict-contour premise remains in this target.

`ray_second_derivative_at` derives the actual second scalar derivative of a branch along every affine ray from its C² Fréchet derivative. Positive actual Hessian quadratic forms make each restriction strictly convex, hence make the branch strictly convex on every convex open chart. The common lower bound implies positivity for every nonzero direction using the Euclidean squared norm. The proof works in any finite dimension, including the vacuous nonzero-vector condition in dimension zero.

An actual finite maximum of these strict branches is strictly convex: select an actual attaining branch at each interior segment point and bound its endpoint values by the actual maximum. Localization then places an entire low sublevel in a convex ball carrying this representation. Continuity identifies each frontier point with the level value, so strict convexity rules out every nontrivial boundary segment. This supplies the source's sufficient strict-contour condition without claiming a false global lower Hessian bound on the full nonsmooth objective.

## Scope remaining

This tranche completes the finite-max local corollary and its common positive branch-Hessian replacement. It does not prove the semialgebraic alternative, the general-dimensional smooth-max conjecture, or the any-dimensional constant-rank visibility/secant partial construction. The explicit three-quadratic example and its RS separation are being verified separately. The canonical-field transport warning in the last section is also a separate retained concrete assertion. No original research source has been changed.

## Main integration verification

PASS: actual main pinned Lake build; 5 modules/13 explicit declarations; complete actual type and standard transitive-axiom reports; 2 strict exact-target checks; all 5 frozen main hashes unchanged; main proof text equals clean-rebuilt scratch except import prefixes.

Main evidence: `audit/c_finite_max_declarations.json`, `c_finite_max_axioms.log`, `c_finite_max_contracts.log`, `c_finite_max_validation.log`, and shared `audit/affine_gap_finite_max_build.log`. This is a post-tenth-release scoped integration, not a replacement of the released whole-project register.

Delivered-source reproduction is now available as `bash audit/verify_affine_gap_finite_max.sh`, with `audit/validate_affine_gap_finite_max.py`. Both depend only on the delivered main sources, manifests and audit drivers; no scratch source or scratch olean is required. The fresh rerun passed all main source hashes, declaration/standard-axiom checks and strict targets.
