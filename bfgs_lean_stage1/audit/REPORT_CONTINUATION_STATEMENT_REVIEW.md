# Third report tranche: exact statement and dependency review

The ten new exact targets are in `ReportContinuationTargets.lean`, with inhabitants
in `ReportContinuationEndToEnd.lean`. All previous targets remain unchanged.
Original research sources are preserved. The full audit prints definitions,
exact proposition targets, and every theorem's transitive dependencies.

## Radial equivalences

`radialInwardEquivalence` proves full RS iff IR on the same compact sublevel
strictly above the attained minimum. It does not require differentiability at
an inward point, uniqueness, or any gradient-continuity hypothesis. Rademacher
applied to actual affine compositions proves joint differentiability on a full
measure set; approximation stays inside the original sublevel, including at its
boundary. Only outer gradient convergence is needed. See
`RADIAL_REVERSE_STATEMENT_REVIEW.md` for the quantified constant and domain audit.

`localRadialCentralEquivalence` is explicitly local: the function-value predicate
requires the outer dilation in the structural upper sublevel and the inner one
in a positive band. RS yields the exact 5C bound; the converse shrinks the upper
level. This matches the source's nested-band qualification and does not silently
assert outward coverage at an original top boundary. All sampled points may be
nonsmooth. See `RADIAL_CENTRAL_STATEMENT_REVIEW.md`.

These targets complete the equivalences, not the later structural-family,
radial normalization, infinitesimal Hessian interpretation or boundary examples.

## Actual projection and lifting

`linearImageLifting` quantifies over a rectangular full-row-rank A and an actual
run for F composed with A. The projected run is constructed with true derivatives,
SPD compressed matrices, the full update and identical alpha, q, d, t and line
search comparisons. The invariant H_k A^T=L0(A H_k A^T) is proved before limits.
The exact fixed affine lift then transfers a limit of this projected run to the
original run. An initial-inverse-metric Pythagorean identity proves actual fiber
membership, optimal squared distance, and uniqueness of that fiber projection.

The projected-limit premise is the explicit premise of source F:lifting; it is
not a claim that every projected run converges. Specific objective applications
must discharge it through retained sufficient theorems. No original full-run or
matrix limit is assumed. Generic tail-gradient-image identities are separate
from the globally factored-objective projected run, so tail membership is never
misrepresented as global objective factorization. Root reviewed the compression,
annihilator induction, limit map and Pythagorean proof. Detailed evidence is in
`AFFINE_LIFTING_VERIFICATION.md`. H.C's endpoint/planar convergence remains open.

## Local solution set and rates

`nonuniqueSolutionBasin` requires a neighborhood of every optimizer in the compact
low sublevel. Compactness of its closed complement gives a strictly positive
value gap; the resulting delta is chosen before every run and initial SPD matrix.
It proves trapping, objective convergence, actual Euclidean distance to the full
argmin, and the uniqueness upgrade. No uniqueness was used for delta.

`linearCorrectionRate` retains the source actual linear cumulative correction
premise and derives sqrt(N)*(F_N-Fstar)→0. Finite square-root bounds and the
pointwise-uniform-correction specialization are separately proved. Compactness
supplies gradients and Armijo supplies summability; reciprocal growth is derived
from the actual matrix theorem. This is not a rate for arbitrary band-dependent
certificates.

`homogeneousRates` bundles the source finite bound with exact initial homogeneous
potential, N*F_N→0 for lower-bounded runs, and the Euclidean iterate norm rate under
coercivity. The actual potential is telescoped; nonnegative values are derived
from H's already-proved dichotomy. A compact unit sublevel and homogeneity derive
a positive Euclidean radial lower bound, rather than assuming it.

`HarmonicRates` proves the exact zero-safe square-root increment estimate, the
finite-prefix harmonic summation of little-o increments, and both o(log N/N) and
O(log N/N). `ObjectiveLogRates` derives the scalar budget from the actual energy
identity, retaining an explicit correction≤C*(next gap) premise. This is currently
a verified conditional criterion: the specific quadratic-plus-gauge correction
estimate is still a separate obligation. No conditional scalar result is labeled
as verifying that family. Local and first-rate statements also received the
independent review recorded in `LOCAL_RATES_PEER_REVIEW.md`.

## Explicit scalar examples and finite-pair geometry

`scalarGlobalCertificateNonnecessity` uses the literal shifted quadratic plus
absolute value, with strong convexity, the unique optimizer -1, actual derivatives
and eligible crossings. Certificate failure occurs on the concrete sublevel F≤3,
which contains a neighborhood of the nonoptimal kink. Both arbitrary-positive-
metric scalar convergence and actual dimension-one BFGS convergence are proved.

`scalarLocalCertificateNonnecessity` uses the actual infinite accumulating-hinge
series, not a truncation. Summability, compact-uniform convergence, strong
convexity, standard coercivity, exact knot formulas and one-sided derivatives are
proved. Each neighborhood first supplies one fixed knot and positive band, and
only then is the crossing size sent to zero. Thus no interchange of band and
knot limits hides a uniformity assumption. Actual scalar runs nevertheless
converge. Root reviewed the fixed-knot quantifiers and source indexing; the full
claim map is `SCALAR_NONNECESSITY_REVIEW.md`.

`eligiblePairRealizability` constructs the source actual SPD metric and unit step
for each individual eligible pair, preserving the predicted decrease. It asserts
neither one common history for multiple predecessors nor infinite continuation.
`finiteSampleFeasibility` constructs the constant identity field, includes its
PSD property, and derives positive visibility and finite suppression constants
from the finite data. Projected transport is exact equality. Empty sets are
covered; a finite sum of nonnegative quotients replaces the source maximum with
another valid existential constant. See `G_PAIR_FINITE_SAMPLE_PEER_REVIEW.md`.
The continuum feasibility/ellipsoid/tangent geometry claims remain open.

## Audit boundary

Only the standard propext/Classical.choice/Quot.sound dependency set is allowed.
The comprehensive build/axiom outcome and declaration counts are recorded in
STATUS.json and report_continuation_check.log. The source coverage register still
sets entire_report_verified=false. The proof designs parked in audit/scratch are
not imported, audited project declarations or completed report obligations.
