# Module F retained-claim inventory

Source `BFGS_MASTER_REPORT_LaTeX/report/chapters/families.tex` read in full. No
original source edited. This inventory records retained obligations. The third-tranche updates below
identify the compiled lifting and rate statements; other F claims remain open.

| Source claim | Precise obligation / dependencies |
|---|---|
| F:centered global compact-sublevel convergence | Actual objective representation psi(x)+gamma(x-star); convex psi locally C1,1 on open convex neighborhood of compact initial sublevel; finite convex degree-one gamma; star minimizes the sum, not necessarily its original summands; values and unique-iterate convergence |
| Centered correction estimate | Local cocoercivity on an open convex neighborhood, nonnegative smooth/homogeneous curvature pieces, Euler support, zero-denominator cases and weighted Cauchy–Schwarz; uniform bound LR²+2Ggamma R |
| Tangent-plane recentering | Optimality gives -gradient(psi)(star) supporting gamma at zero; transfer one affine functional between summands, preserving the original objective and proving both adjusted summands nonnegative |
| Centered local representation | Derive a low initial basin inside the representation neighborhood, quantified before all actual admissible runs and initial SPD matrices |
| F:transform | Coercive degree-one gamma; Phi continuous/convex/strictly increasing on nonnegative arguments, zero at zero, C² with positive derivative on strictly positive arguments; derive compact sublevels and actual convergence, without nonlinear-transform invariance |
| Transformed potential | Euler/chain rule at accepted points, inverse scalar profile Theta, bounded derivative on a positive value interval, exact correction≤constant times accepted decrease, including all stated constants |
| F:active max-affine identity | Finite active slopes at star; exclude inactive slopes locally with exact gaps/radii; parallel inactive pieces need no division by zero |
| F:basin explicit threshold | Extended-real infimum/minimum over inactive closed active regions, empty sets assigned +infinity; attainment where finite, strict gap above optimum, and every start below threshold converges; also actual-tail variant |
| Residual penalty classes | Local scalar sign/hinge decomposition, affine Euclidean norm smoothness away from zero, centered homogeneity at zero; check each summand and preserve nonzero-spectral-residual caveat |
| F:lifting | Actual projected objective gradients and full BFGS update, same accepted lengths and line-search inequalities, full row rank, exact invariant image and lift H0 Aᵀ(A H0 Aᵀ)⁻¹; derived iterate limit and metric projection characterization |
| Bounded correction rate | Actual energy finite bound and S_N/N²→infinity imply value gap=o(N^(-1/2)); also linear cumulative budget, no rate for arbitrary band-dependent certificates |
| Homogeneous rate | Source homogeneous potential supplies sum F_k²/q_k≤Phi0; value=o(N^(-1)), coercive Euclidean radius lower bound gives same iterate-norm order |
| Quadratic-plus-gauge correction | Split coordinates, actual SPD Q, coercive gauge bounds, uniform correction≤max(2,1+Lambda/mu) F_next, including zero curvature components |
| Quadratic-plus-gauge rates | Harmonic increment estimate, initial finite prefix, O(log N/N), then little-o harmonic increments and strengthened o(log N/N); accepted-iteration and fixed-instance scope |
| Matrix-limit qualification example | Exact u²+abs(v) objective, every actual iterate/update, arbitrary tangential A, accepted alpha=2rho, Armijo/Wolfe and displayed limiting matrix; this does not exhibit a divergent matrix sequence |
| Finite-ray-singularity step existence | Convex bounded-below line restriction with negative initial derivative, one-sided slopes and first threshold, strict Armijo interval, avoidance of finitely many full-space nondifferentiability times; no universal oracle complexity |
| No differentiable acceptable point example | Actual coercive five-piece max in R³, unique minimizer, initial derivative/direction at (-2,0,1), exact ray values and all three time regions; weak-Wolfe/Armijo failures and nondifferentiable middle interval; scale to arbitrary neighborhoods |

The existing M energy and localization theorems, H Euler/dichotomy, and R inward
sufficient criterion are dependencies, not a verification of these applications.
Projection/lifting overlaps H.C's planned invariant-subspace work and will be
shared rather than duplicated. The all-ray obstruction is a finite failure to
continue, not a counterexample consisting of an infinite admissible run.

Third tranche: F:lifting is proved by the genuine projected run and fixed affine/metric-fiber identity (see AFFINE_LIFTING_VERIFICATION.md). The first two rate paragraphs, including finite bounds, are proved in ObjectiveRates.lean. HarmonicRates/ObjectiveLogRates prove the logarithmic rate criterion from an actual correction bound; the quadratic-gauge derivation of that bound remains open. The centered and other structural families are not marked complete.

Fourth milestone: F:centered, exact correction, recentering and local-basin
clauses are compiled in Centered*.lean; the concrete quadratic-gauge correction
and rate chain are compiled in QuadraticGauge*.lean. The transformed-gauge,
max-affine basin, residual descriptions and line-search/matrix examples remain
separate obligations. See CENTERED_STATEMENT_REVIEW.md and
QUADRATIC_GAUGE_VERIFICATION.md.

Fifth milestone: F:transform, its exact scalar correction coefficient, actual
inverse/Theta derivative, endpoint gauge differentiability, compact sublevels
and coercivity are now proved in TransformedGauge/TransformedGaugeInverse.
The exact every-run target is transformedGaugeConvergence. Remaining F claims
are the max-affine basin, residual descriptions, matrix/line-search examples,
and source-linked powered-gauge classes in R. See
TRANSFORMED_GAUGE_STATEMENT_REVIEW.md.
