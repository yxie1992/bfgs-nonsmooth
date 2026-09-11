# D actual deterministic local embedding

The reviewed source is the preserved `report/chapters/D.tex`, especially D:main,
D:fullobjective, D:localcone and D:finalorbit. The two exact exported targets are
`DEmbedding.objectiveGeometry` and `DEmbedding.embeddingFailure`; their independent
proposition definitions are in `ReportEmbeddingTargets.lean`. The importing main
build, scoped declaration audit and independent peer review are recorded in the
corresponding `d_embedding_*` logs and `D_EMBEDDING_PEER_REVIEW.md`.

## Actual objective and derivatives

`DEmbeddingObjective` defines the four literal source branches from the already
checked actual scalar function phi. The third parameter is exactly 2c-32d, with
33<bStar<34 derived from the designated algebraic root. Actual Frechet gradients,
second derivatives and Hessian matrices are proved. Each branch is convex C2;
its Hessian is between zero and 64I globally. The explicit individual upper
bounds 51, 51*65/64<52, and <12 are also proved. The actual Euclidean operator-norm
Hessian difference has global Lipschitz constant 60000. The finite maximum has
compact sublevels, unique minimum zero and the actual directional derivative
max(0,h_2) there, so it is nonsmooth at its minimizer. No Hessian or differentiability
property is assumed as a premise of the final objective target.

## Literal local model and gradient transfer

`DScalarPlateauDerivative` derives an actual derivative on the interior of the
closed source plateau, using eventual equality with the affine formula.
`DEmbeddingLocal` proves the original three-slab local model at every n, including
n=0. The first two slabs imply |h_1|<=a_n/2 and |h_2|<=8a_n. The fourth branch is
strictly negative; the other three are at least a_n^3/2. Thus the actual finite
maximum equals a_n^3+a_n^2 G(h). Strict seed activity and the actual branch
continuity give an actual gradient on each strictly active embedded plateau.

Every actual accepted and base-table rejected seed query has the previously
proved PointCertificate. For n>=1, its offset a_n^2 z lies strictly inside all
three plateaus, because |g_i.z|<3 and a_n<=1/16. `DEmbedding.actualData` and
`actualOracleData` discharge every field of the explicit generic transfer
interfaces. Those interfaces are conditional helpers only; the D target has no
value, derivative, oracle-history or local-representation hypothesis.

## Actual unmodified matrices and actual search

`SeedEmbeddingRun` proves simultaneous positive scaling of the actual gradients
and displacements leaves the inverse-BFGS update unchanged. The physical stored
matrix is the original orbit matrix; there is no update modification. The
actual convex objective, nonzero gradients, accepted steps, initial I, full update
and Armijo/weak-Wolfe fields form an `AdmissibleBFGSRun`. All later SPD matrices
are derived by the earlier actual-update invariant theorem.

`SeedEmbeddingOracle` proves actual Armijo and weak-Wolfe predicates equivalent
to the true seed predicates by the positive factor a_n^4. It proves the coordinate
gradient at every trial is the actual gradient. `SeedEmbeddingSearch` evaluates
the specified recursive search and obtains precisely the histories [1],
[1,1/2,1/4], and [1,1/2,1/4,1/8,1/16]. The final target quantifies over every step
k and every corresponding table query, so an assigned-length sequence is not
being substituted for implementation verification. The same objective, points,
matrices and histories work for every 0<c1<=1/3 and c1<c2<1, including the printed
c1=1/10000 and c2=1/2.

## Derived limits and localization

The final trajectory is literally p_n+a_n^2*rho^m*z_j and H=rho^m*M_j at 3m+j.
Its iterate and value limits are derived from the checked geometric seed; they
are not run assumptions. Values strictly decrease to F(p_n)=a_n^3>0. Each p_n
is nonzero and nonstationary, and its actual right directional derivative in
(-1,16) is -a_n^2. Initial points and values approach zero. A single bound
80*a_n controls every accepted point and every actual trial, uniformly in the
entire infinite trajectory. Hence every neighborhood of zero eventually
contains whole trajectories; the small basin is not just an initial-point fact.

`DScalarSmallBounds` additionally proves the literal source right-zero orders
phi=O(x^3), phiFirst=O(x^2), phiSecond=O(x), with explicit interval bounds and the
actual right-neighborhood filter. `DEmbeddingBounds` records the half-height,
slab, active-center and actual trial-value identities explicitly.

No original research source was modified. All 136 new explicit declarations in
these thirteen D/scaling modules have actual scoped type and transitive axiom
reports (54 objective +74 transfer/embedding +8 supplemental). Only propext,
Classical.choice and Quot.sound occur. The two release wrapper declarations are
also covered by the full compiled-environment audit. This closes D's actual
construction; it does not prove L's perturbation-persistence claim.
