# Fresh positive-proof critique

**Result: no blocking or material mathematical issue found in the three assigned files.** This was a fresh reading of their current proofs and relevant actual Lean contracts, not an inference from earlier PASS records. It is a model-assisted review, not a claim of external human refereeing or a fresh kernel/axiom audit.

The only suggested edit is expository: at `paper/sections/local.tex:342`, identify `D=3(1+v-uv)` explicitly as the determinant of the augmented gradient matrix. The calculation is correct; naming the determinant makes the subsequent affine-independence inference immediately visible. No theorem needs to be weakened or given another hypothesis.

## Hardest checks

### Inward to radial

Location: `paper/sections/global.tex:57-94`.

Both endpoint probes use the same positive band because F(z)<=F(x). The reversed numerator is T-N and is bounded by 2GR through its expression at x. The scalar optimization handles M=0 and produces the printed max{2M,4GR/theta}. Inner samples are never differentiated.

Actual Lean contracts checked: `BfgsVerification.RadialCertificate.HasInwardTaylorBounds`, `BfgsVerification.RadialCertificate.inward_probe`, `BfgsVerification.RadialCertificate.inward_probe_quadratic_bound`, `BfgsVerification.RadialCertificate.radialNumerator_swap`, `BfgsVerification.RadialCertificate.radial_of_inward_on_compact`.

### Centered composite

Location: `paper/sections/global.tex:133-176`.

The minimizer belongs to the trapped sublevel and hence to U. A finite local gradient-Lipschitz cover plus subdivision of each segment gives a uniform constant on compact convex K. Differentiability of F and smoothness of psi imply differentiability of gamma only where needed; Euler homogeneity cancels its radial remainder. Neither summand is separately assumed minimized at the center. Distance-to-solution convergence uses compactness; uniqueness is added only for convergence to one point.

Actual Lean contracts checked: `BfgsVerification.CenteredSmoothSublinear.LocallyC11On`, `BfgsVerification.AdmissibleBFGSRun.centered_values`, `BfgsVerification.AdmissibleBFGSRun.centered_iterates`, `BfgsVerification.CenteredSmoothSublinear.local_centered_basin`.

### Homogeneous and mixed examples

Location: `paper/sections/global.tex:178-268`.

The mixed remainder is exactly tau^2*u^2, with compact sublevels and unique minimizer. Bounded homogeneous sublevels rule out any nonzero direction with nonpositive value; the sphere minimum then yields coercivity and whole-iterate convergence. The article expressly limits the claims to infinite admissible differentiable accepted runs. Noncompact conclusions and the reverse inward implication are identified as companion results rather than implicitly used.

### Localization and polyhedral cells

Location: `paper/sections/local.tex:16-128; paper/statements/positive_partition.tex`.

The sphere argument gives the stated linear coercive lower bound. The ambient n>=1 convention appears in admissible runs and in the polyhedral statement. Finiteness and closedness let one remove all cells missing the minimizer, then intersect the separate extension neighborhoods. Only radial derivative equality along the contained segment is required; convexity of cell extensions is not assumed. Low sublevels are chosen before every run, SPD matrix and line-search pair. PLQ is explicitly defined using a finite polyhedral cover and is not confused with arbitrary quadratic maxima.

Actual Lean contracts checked: `BfgsVerification.ConvexCellRadial.finite_polyhedral_basin`, `BfgsVerification.CenteredSmoothSublinear.local_centered_basin`.

### Whole cluster set argument

Location: `paper/sections/local.tex:162-234`.

A nonvanishing-step subsequence would force a positive-level boundary segment by the two support/convexity bounds. The proof therefore derives vanishing steps before invoking local pair estimates. Compactness makes the entire tail approach the cluster set. The BFGS residual quadratic is nonnegative, so multiplying its upper transport factor is legitimate; the summable product gives an O(N) reciprocal sum, contradicting the framework theorem without any matrix or iterate limit assumption.

Actual Lean contracts checked: `BfgsVerification.AdmissibleBFGSRun.planar_affineCritical_cluster_on_sublevel`, `BfgsVerification.AdmissibleBFGSRun.planar_convergence_on_sublevel`.

### Field construction and gluing

Location: `paper/appendices/planar_geometry.tex:40-123`.

The inverse function theorem isolates each level corner; smooth charts contain none, so a finite compact cover gives finitely many relevant corner curves. Common positive pairing confines each supporting-normal arc to an open semicircle. Strict contours separate arcs of distinct corners, permitting disjoint fixed cutoffs. The plateau formula makes w=v_j(F) on both sides and on each switching curve, supplying actual local Lipschitz gluing and common pairing. The angular derivative cancellation preserves the tangent line without requiring h to be a support function.

Actual Lean contracts checked: `BfgsVerification.PlanarCornerCharts.ConvexTwoBranchRegularAt`, `BfgsVerification.PlanarCornerCharts.exists_finite_convexCornerCharts`, `BfgsVerification.PlanarCornerCharts.ConvexCornerChart.common_pairing_near`, `BfgsVerification.PlanarAllPairs.exists_pairwise_structured_field`, `BfgsVerification.PlanarAllPairs.exists_all_endpoint_field`.

### All pair transversality and transport

Location: `paper/appendices/planar_geometry.tex:125-189`.

The compactness contradiction uses both endpoint gradient limits in the same subdifferential. Common positive pairing fixes the limiting step orientation and contradicts weak Wolfe. The signed determinant derivative is correct in the negatively oriented (T,n) basis. At corners the one-sided chain rule applies to v_j composed with convex F. Monotonicity of the convex right derivative gives |phi_right|<=phi_right+2d; the elementary one-sided comparison proof is valid even with infinitely many switches. Lambda is positive because the determinant never vanishes, and the linear square-factor estimate is restricted to d<=1.

Actual Lean contracts checked: `BfgsVerification.PlanarAllPairs.source_all_endpoint_estimates`, `BfgsVerification.PlanarAllPairs.sourceAllEndpointEstimates`.

### All pair secant control

Location: `paper/appendices/planar_geometry.tex:191-233`.

For same-branch pairs the descent probe stays in a larger convex chart because gradient differences are Lipschitz; subtracting the tangent plane makes the lower comparison valid locally. Its error is the actual F supporting error at the endpoint and is bounded by actual t. For different branches a tie point gives jump cancellation; uniform gradient-row invertibility and weak Wolfe imply t>=a0*norm(s), after absorbing the quadratic term. A finite buffered cover supplies one distance threshold, not one field per estimate.

Actual Lean contracts checked: `BfgsVerification.PlanarAllPairs.exists_all_endpoint_field`, `BfgsVerification.PlanarAllPairs.source_all_endpoint_estimates`.

### Finite max basin quantifiers

Location: `paper/sections/local.tex:254-312`.

Full column rank of the augmented active-gradient matrix persists. Its continuous least-squares expression is invoked as a solution only when the affine system is solvable. Strict positivity then forces any nearby affine balance to use all retained branches and hence be a convex balance. In the plane, three independent active gradients are affine critical, while two distinct dependent gradients have an affine line containing zero. The neighborhood and low sublevel are fixed before all admissible runs and their line-search constants.

Actual Lean contracts checked: `BfgsVerification.PlanarMaxRegular.finite_max_local_basin`, `BfgsVerification.PlanarConvergence.local_convergence_basin`.

### Explicit nonradial example

Location: `paper/sections/local.tex:320-384`.

The exact objective, coefficient determinant/balance, box bounds, d, t, Delta and radial numerator were independently recomputed with rational sparse polynomials. The limit argument first chooses a fixed sufficiently small positive u and then all sufficiently small positive e. Its positive value band is fixed before the quotient becomes unbounded. The actual Lean endpoint theorem additionally constructs a realizing SPD matrix; the article does not claim that the obstructing sequence itself is a full BFGS trajectory.

Actual Lean contracts checked: `BfgsVerification.PlanarQuadraticExample.coefficient_box_bounds`, `BfgsVerification.PlanarQuadraticExample.gradient_affineIndependent`, `BfgsVerification.PlanarQuadraticExample.fullBFGS_explicit_basin`, `BfgsVerification.PlanarQuadraticExample.eventually_eligible`, `BfgsVerification.PlanarQuadraticExample.eligible_radial_unbounded_on_neighborhood`.

## Independent arithmetic check

A fresh exact rational sparse-polynomial calculation returned zero remainders for the augmented determinant, coefficient sum and both gradient balances, mean-objective identity, predicted decrease, curvature, value difference on the tie, and radial numerator on the tie. The independent termwise box lower bounds were `267/100`, `23/100`, `49/100`, and `9/20=45/100`, agreeing with the article. The relevant actual Lean statements were also read. This calculation is a review aid; the article's symbolic argument and the Lean proof contracts remain the mathematical evidence. No floating-point plot or unchecked numerical computation is used to justify the conclusions.

## Scope and remaining limits

The review does not find an unspoken iterate/matrix convergence assumption, an all-ray acceptance assumption, or a switch from full BFGS to another update. The planar field is chosen once for the whole compact cluster set; the same field supplies all three endpoint estimates. The local basin is chosen before every run and initial metric, and the finite-max theorem also chooses it before line-search constants. The radial obstruction is an endpoint-pair obstruction, not an asserted bad infinite run for the convergent example.

No Lean build or transitive dependency audit was rerun here. I inspected actual relevant declaration types and their source arguments, but did not independently recheck every transitive proof term or the entire mathlib foundation. The analytical framework is an explicit dependency and has a separate assigned review. Bibliographic priority claims, negative constructions, PDF layout, and companion-only reverse/noncompact theorems were outside this assignment.

Only the two `positive_critique` records were written; TeX, Lean, original research sources, commits, and remotes were untouched.

## Reviewed file identities

- `paper/sections/global.tex`: SHA-256 `5a975788459ae7034212f2de56a811536fd01fd125bcd4dcff34f28f6d227a19` (268 lines).
- `paper/sections/local.tex`: SHA-256 `0706aac5e4ec88d782cc2a413eceaf4a0ce6e2275072fa305b46c072d9126eb0` (392 lines).
- `paper/appendices/planar_geometry.tex`: SHA-256 `7c0bc06f0e5c2618f67284d1fcc8b20da70d426ac30464e1b083d8c607652415` (234 lines).

The JSON record also contains the identities of the context and actual Lean sources inspected, exact declaration names, and the individual review checks.
