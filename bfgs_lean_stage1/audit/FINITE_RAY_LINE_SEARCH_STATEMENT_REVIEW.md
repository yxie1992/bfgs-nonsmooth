# Finite ray singularities and an actual accepted BFGS step

Source: families.tex, final line-search discussion. Original source unchanged.
Seven theorems in FiniteRayLineSearch.lean are compiled and individually
axiom-audited; independent review is FINITE_RAY_LINE_SEARCH_PEER_REVIEW.md.

`acceptable_interval` derives a nonempty open interval of strict Armijo
acceptance from a finite convex scalar function, its actual negative derivative
at zero, ordinary 0<c1<c2<1, and a lower bound along the positive ray.
At every differentiable point in that interval, its actual derivative satisfies
strict weak Wolfe. The proof minimizes a tilted convex scalar objective on a
compact interval. Neither a finite-switching hypothesis nor a derivative at a
nonsmooth minimizer is used to construct the interval.

`finite_nondifferentiability_step` excludes finitely many times of *full-space*
nondifferentiability from that open interval, and constructs the actual full
Frechet gradient at the chosen point. It proves both strict inequalities for
the actual displacement. Scalar differentiability is not substituted for full
objective differentiability.

`fullBFGS_step_exists` derives strict descent from an actual SPD inverse matrix
and nonzero actual gradient, uses the literal unmodified full-BFGS direction,
and proves existence of a differentiable strict accepted positive step. Its
finite-bad-ray-times and bounded-below-ray premises are explicit source
hypotheses. No update, iterate convergence, or matrix convergence is assumed.

Scope: existence of a step is verified. The source's first right-derivative
threshold construction is replaced by the proved tilted-minimum argument;
its literal threshold formula is not exported. The listed objective families
still need their own finite-bad-ray-times bridges. This is not a deterministic
oracle termination or uniform trial-complexity theorem.
