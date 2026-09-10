# Objective bridge: independent statement review

Review date: 10 September 2026. These are independent agent reviews inside this
formalization task, not external peer review. Compiler and axiom evidence is in
`STATUS.json`, `build.log`, `axioms.log`, and `declarations.json`.

Three bounded reviews covered the run definition, positive-update proof,
convex-analysis and descent-budget proofs, objective targets, and their exports.
No actionable mathematical or statement mismatch was found.

A separate audit-driver review confirmed complete theorem enumeration and exact
objective target checks. It found that an unmatched target could leave the
driver's exit code successful; this was corrected so incomplete targets return
a nonzero exit code. The driver also writes pending status before invoking Lean,
so an interrupted run does not retain the previous verified status as current.

## Assumptions and invariant propagation

`F` is real-valued everywhere and convex on the full coordinate space. Derivatives
are assumed only at accepted points, represented by the exact dot functional of
the stored gradient. The run requires `0<c₁<c₂<1`, positive lengths, and nonzero
gradients; this is the infinite nonstationary accepted-run branch.

The update is the original full inverse-BFGS update. Only initial SPD is a field.
Current SPD gives positive energy; current weak Wolfe gives positive curvature;
these imply next SPD. There is no circular assumption about the next matrix.
The step-form weak-Wolfe condition is equivalent to the direction form because
the step length is positive. Neither strong Wolfe nor damping is substituted.

`toFullBFGSRun` preserves the original matrices, gradients and lengths exactly.
Its q/d/beta equalities are definitional. Objective exports call the proved actual
matrix hierarchy through this bridge, with no assumed normalized hierarchy.

## Convexity, compactness, and summability

The supporting inequality uses the derivative at the current point along one
affine line. It needs no differentiability in a neighborhood. The compact-set
argument bounds every supporting vector via coordinate shifts of the compact
set. It does not assume bounded or continuous gradients, and handles empty
compact sets and zero dimension without hidden nonemptiness hypotheses.

The coordinate model uses the Pi norm, with the Euclidean dot functional and
squared norm defined explicitly. Finite-dimensional norm equivalence makes this
a faithful coordinate model. No separate type-transport theorem to
`EuclideanSpace` is exported.

Armijo supplies antitonicity and finite partial-sum bounds. A real lower bound
along the run yields summability and tail bounds. The finite-value-limit variant
derives such a lower bound, without identifying the limit with the minimum.
The compact-sublevel variants derive both the gradient bound and value bound;
the more general variants retain the explicitly stated bounds.

## Growth targets and limits of scope

The qualitative target keeps the weaker vanishing-decrease hypothesis. The
superquadratic target derives summability from Armijo in the lower-bound branch.
The finite-horizon target uses actual principal determinants, `c=1−c₂`, the
actual infinite predicted-decrease tail, and the source's constants. Its formal
block length `m+1`, with `m>0`, is the source's block length at least two.

No universal admissible-step existence, optimal-value convergence, iterate
convergence, matrix convergence, or global smoothness is asserted. No original
research statement or source was altered. Remaining research obligations are
listed separately in `PROOF_OBLIGATIONS.md` and the status register.
