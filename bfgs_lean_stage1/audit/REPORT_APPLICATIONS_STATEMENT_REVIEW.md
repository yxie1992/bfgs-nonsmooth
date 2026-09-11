# Fourth report tranche: statement and dependency review

This review covers the eight explicit contracts in
`ReportApplicationsTargets.lean` and the additional family/geometry exports.
The full-project compiler and axiom logs, rather than this narrative, determine
the release status. No original research source is edited. Q's primary theorem,
other F/H applications, and the negative constructions remain separate work.

## T: invertible affine covariance

`affineCertificateCovariance` quantifies over every actual invertible square
matrix and every translation, with the image of the original set as its domain.
The transformed objective is F(A^{-1}(z-b)); the actual gradients are A^{-T}g and
the actual certificate is AWA^T. The eligibility predicate, decrease, curvature,
positive band and four certificate constants are preserved. Projected transport
is proved through its perpendicular quadratic characterization, not an invalid
claim that Euclidean projectors conjugate under every invertible map. The inverse
affine change proves the reverse implication. See the independent
`AFFINE_CERTIFICATE_STATEMENT_REVIEW.md` and complete scoped axiom log.

## F: centered smooth plus sublinear

The two registered contracts preserve the actual run, original open convex
neighborhood, local C1,1 derivative regularity, and compact initial sublevel.
The value conclusion does not require uniqueness. Uniqueness is used for point
convergence; the local theorem selects a positive level before quantifying over
all runs and all initial SPD matrices. The proof derives a uniform Euclidean
cocoercivity constant from local Taylor estimates and a compact cover, derives
the component gradients from actual endpoint derivatives, and proves the exact
LR^2+2G_gamma R bound including zero component curvatures. Root reviewed the two
permitted descent tests and the support/Taylor algebra in CenteredCocoercivity.
The chosen L is existential, as needed by the source theorem; an independent
sharp prescribed-L Baillon--Haddad theorem is not claimed.

Recentring derives -grad psi(star) as a support of gamma at zero from a one-sided
smooth surrogate and optimality of the sum. Neither F nor gamma is differentiated
at the minimizer. The exact rewrite, both nonnegativities, convexity, homogeneity
and preservation of local C1,1 are proved. This is an identity of the objective,
not a changed BFGS objective. See `CENTERED_STATEMENT_REVIEW.md` and the independent
explicit contracts in `CENTERED_CONTRACTS.lean`.

## F: quadratic plus coercive gauge

`quadraticGaugeRates` has the source's arbitrary finite coordinate blocks, SPD
quadratic matrix, finite convex homogeneous gauge and actual Euclidean bounds
with mu>0. It adds no sign assumption on Lambda and no pre-assumed correction,
gradient split, compactness, or convergence. The actual correction is derived
with the exact max(2,1+Lambda/mu). Root reviewed its slice support argument,
PSD Cauchy--Schwarz, both zero-weight cases, and actual-run substitution.

Compactness follows from the derived unique minimizer and finite convexity.
The actual M matrix theorem supplies reciprocal growth. The contract gives
both little-o and big-O logarithmic orders and actual value/iterate convergence.
Separate audited exports retain the exact finite-horizon budget, its square-root
bound and sqrt(A_N)/log N ->0. See `QUADRATIC_GAUGE_VERIFICATION.md`.

## H.C: planar unbounded-below finite max-linear runs

`planarHomogeneousEscape` uses the actual finite maximum and unboundedness below,
not a bounded trajectory or independent-pair premise. The result is exclusive:
points tend to zero with strictly positive strictly decreasing values tending to
zero, or values tend to minus infinity and the actual Euclidean norm tends to
infinity. No stationary support exists anywhere.

Root reviewed why a negative objective direction and distinct positive-active
supporting gradients force every planar transition to be independent. Curvature
gives distinct gradients; actual endpoint pairings tend to zero on the finite
value branch; finite inverse norms then imply endpoint convergence without a
bounded-run assumption. Value escape forces norm escape by the finite alphabet's
absolute linear bound. H.7.4 and H.8 are explicitly outside this contract.

## G: ellipsoids and pointwise capacity

`ellipsoidCertificateGeometry` uses the literal PSD-square-root image of the
actual Euclidean unit ball, its attained support and projected ellipsoid
inclusion iff projected Loewner order. Singular/zero matrices and arbitrary
projection matrices are included. Range assertions use actual matrix ranges.

`pointwiseCertificateCapacity` quantifies over every differentiable band target
and every eligible incoming predecessor at the specified delta. Its iff fixes
the same delta on the certificate side. ENNReal suprema/infima preserve empty
families and infinite capacity. Rank-one choices suffice for visibility and
suppression alone. No transport or regular field choice is inferred. In the
explicit contract the iff is parenthesized after both hypotheses, avoiding a
weaker implication-precedence statement; Lean rejects a mismatched contract.

The G.4 accessibility qualification is recorded separately by the geometry
review: accessible-jump annihilation only removes the accessible span. To remove
the whole active jump span requires a spanning condition. The all-active
projection/affine-hull equivalence is algebraically valid independently. A pure
algebraic countermodel distinguishes the spans and is not an objective/BFGS
counterexample. The source wording is preserved and must not be silently
strengthened into an unqualified theorem.

## Q: foundations and the derived denominator

`parabolicDenominator` is deliberately a foundation contract, not Q's convergence
contract. Family data retain all supplied branches, including duplicates,
redundancy, ties and zero normal slope. Actual convexity, compact sublevels and
the unique zero minimizer are derived; every active branch equals the actual
accepted gradient at a differentiable point.

The exact identities Q.9--Q.14 and weighted secant bound are checked. Compactness
and finite coefficients give constants before every eligible pair. The positive
old level and fixed-Wolfe curvature absorb the error for one positive uniform
delta, yielding d<=C|D|, |h|<=C|D| and D!=0. No division by b_i or by h, no adjacent
branch requirement, and no small normal displacement assumption occur. The
uniform unscaled visibility/secant bounds are proved separately. Envelope
calibration, compensated transport, the complete Q theorem and the literal
three-branch separation are still obligations. See the independent
`PARABOLIC_FOUNDATION_REVIEW.md`.

## Evidence and closure scope

All new declarations have scoped compiler/axiom logs, and the release gate also
checks the entire imported namespace, including generated theorem declarations.
Only propext, Classical.choice and Quot.sound are allowed. Exact run and field
definitions and every registered target are printed in Audit.lean. Conditional
generic criteria retain their assumptions, with concrete discharges recorded
for the actual families. Entire-report completion remains false.
