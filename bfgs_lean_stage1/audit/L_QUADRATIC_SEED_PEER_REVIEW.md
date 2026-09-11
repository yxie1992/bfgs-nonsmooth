# Independent review of the actual L quadratic seed

Root reviewed `LQuadraticSeed.lean` against L.tex's concrete objective and
minimizer calculation, including every one of the 56 explicit declarations and
the definitions used by the exact `QuadraticSeedTarget`. The source defines
Q_mu(x)=mu*||x||_2^2/2+G(x); it does not redefine the old seed orbit as a perturbed
orbit. The source hash and all type/axiom reports are independently checked in
`l_quadratic_seed_peer_validation.log`.

The least-norm point is exactly (1,-16)/257 with convex weights 129/257 and
128/257 on the first two source slopes. Its squared norm and all three support
pairings are derived; the third is strictly larger. Cauchy-Schwarz gives the
least Euclidean norm, and the equality case gives uniqueness. Completing the
square and checking the actual active maximum prove the unique optimizer
-gbar/mu and value -1/(514*mu). At it exactly branches 0 and 1 are active and
have different actual gradients, proving nonsmoothness.

Both the project's explicit Euclidean strong-convexity convention and mathlib's
standard Euclidean-space convention are proved. Actual second Frechet derivatives
identify each branch Hessian with mu I. Compact sublevels and coercivity are
consequences of the actual strongly convex function. The origin subdifferential
is the actual convex hull of the three source slopes, by the checked finite-max
subdifferential theorem; it excludes zero. All final claims quantify over every
mu>0, without any seed-limit or metric assumption.

No mathematical or statement defect was found. The unperturbed orbit is not an
orbit of this objective. Actual return-map agreement, spectrum, nonlinear
stable-orbit existence and L's local embeddings remain separate obligations.
The pinned compiler/axiom evidence is sufficient for this concrete prerequisite
only, not for the whole L persistence theorem.
