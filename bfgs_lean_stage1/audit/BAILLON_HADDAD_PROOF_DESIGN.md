# Local cocoercivity dependency for Module F

Primary reference checked: [Wachsmuth and Wachsmuth, arXiv:2204.00282v1](https://arxiv.org/html/2204.00282), Lemmas 2.1/2.3 and Theorem 2.5 (2022).
This is a proof design, not a Lean verification or an imported mathematical axiom.

The paper proves the Hilbert-space result on open convex domains using first-order
calculus. Its route converts a two-sided Taylor remainder bound into a Lipschitz
derivative estimate through four nearby points and segment subdivision. Applied
to the derivative of a quadratically adjusted convex function, the resulting
nonexpansion inequality gives cocoercivity by expanding squared norms.

Planned formalization: use actual Euclidean norms, prove the Taylor estimate by
one-dimensional calculus, check the four-point algebra, retain an interior radius,
and prove finite segment subdivision before passing to arbitrary domain points.
The constant must be the source L, not a larger Banach-space bound. Separately,
compactness and local C1,1 regularity must supply one constant on a convex
neighborhood of the relevant compact sublevel. An IR-based proof can establish
the centered convergence conclusion earlier; it does not by itself verify the
source's explicit cocoercivity correction estimate.
