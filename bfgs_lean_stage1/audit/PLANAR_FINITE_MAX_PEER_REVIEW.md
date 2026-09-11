# C nondegenerate finite-max corollary: independent peer review

Reviewed the five delivered files `PlanarMaxRegular`, `PlanarFiniteMaxBasin`, `HessianStrictConvex`, `PlanarMaxHessianBasin`, and `PlanarFiniteMaxTargets` against source `C.tex` lines 65–85 and its proof at lines 323–336. All 13 explicit declarations and both target definitions were read, together with the relevant actual subdifferential/barycentric interfaces. No mathematical or statement defect was found.

## Exact original-family hypotheses

The final local theorem uses an actual finite convex objective and an actual local finite maximum of convex C² branches. Only the originally active gradients at the minimizer are assumed affinely independent and supplied with strictly positive zero-combination weights. The code derives a neighborhood representation after discarding the originally inactive branches and applies the existing verified positive-barycentric stability theorem. Neither eventual active-set constancy nor a fixed alphabet for accepted iterates is assumed.

At a non-affine-critical point the actual active-gradient supports are first related to the actual full subdifferential. Planar cardinality excludes three independent active gradients. One active branch gives actual neighborhood equality and differentiability; two active branches give a nonzero actual determinant, since a zero determinant together with distinctness would put zero in their affine line. The resulting chart retains convexity, C² regularity, exact local attainment, and the source nonzero determinant. Empty active families are ruled out by actual maximum attainment, not by an unrecorded nonempty instance.

The source contour assumption appears as no nontrivial boundary segment over an interval of positive low levels. The local basin is chosen before every actual `AdmissibleBFGSRun`, independent of its initial matrix and line-search constants. Value and iterate convergence remain conclusions; no matrix limit, condition-number bound, convergence premise, transport field, or correction budget is imported as an input.

## Actual Hessian sufficient condition

The second target removes the contour assumption using a common positive lower bound on the actual second-Fréchet Hessian matrices of only the originally active branches. The auxiliary ray theorem proves existence-linked actual scalar second derivatives from C² regularity. Positive Hessian quadratic forms then make every nontrivial line restriction strictly convex. The finite-maximum proof selects an actual attaining branch at the interior segment point and bounds its endpoint values by the true maximum. A low-sublevel localization places the entire sublevel in the convex chart before strict convexity excludes boundary segments.

This does not impose a false classical Hessian on the nonsmooth maximum. The Euclidean squared norm in the lower bound is explicitly connected to the matrix quadratic form. The arbitrary-dimensional Hessian helper includes the zero-dimensional vacuous case without a hidden nonzero-vector assumption.

## Independent validation

The author main audit passed a pinned Lake build, all 13 complete type/transitive-axiom reports, two strict `Meta.isDefEq` contracts, and five frozen main hashes. Independently checked all 13 declaration names and standard transitive axiom sets, both exact-contract results, and correspondence with all five frozen reviewed scratch sources after import normalization. The exact main hashes are recorded in `audit/c_finite_max_peer_validation.log`.

The main axiom and strict contract drivers were additionally rerun independently; results are `audit/c_finite_max_peer_axioms.log` and `audit/c_finite_max_peer_contracts.log`. No external mathematical computation is involved in the structural checks.

Scope: this review covers the finite-max local corollary and the actual branch-Hessian sufficient replacement. The explicit three-quadratic example, semialgebraic alternative, general-dimensional constant-rank construction, and canonical-field transport warning are separate report assertions. Original research files were not edited.
