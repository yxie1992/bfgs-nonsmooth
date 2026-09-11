# Second entire-report tranche: statement and dependency review

The exact seven new targets are in `ReportGeometryTargets.lean`; their inhabitants
are in `ReportGeometryEndToEnd.lean`. Original research sources are preserved.
The primary theorem targets, definitions and transitive axiom sets are printed
by the full project audit. No entire-module completion is inferred from a helper
or one target passing.

## Retained source claims now supplied

1. **G normalization.** A value upper bound, c1>0 and c2<1 give equivalence of
   certificate existence and certificate existence with L=0. The new field is
   exactly exp((L/c1)(F-Fstar)) W, the small-pair threshold is unchanged, and no
   uniform bound/continuity/rank condition on the original W is assumed.
2. **H.B.** Finite max-linear objectives are actual finite suprema, with convexity
   and degree-one homogeneity proved. The true derivative at each differentiable
   point equals an active slope, so the finite accepted alphabet is derived.
   Finiteness gives an eventual tail of recurrent slopes. Excluding affine zero
   supplies a fixed vector with gradient pairing one; its actual inverse-Hessian
   energy loses exactly 1/q. The verified matrix reciprocal theorem excludes that
   tail. Finite values therefore force affine zero in the recurrent slopes;
   excluding zero from the full slope affine hull forces value escape. The
   t+max(b·u) family and the recurrent rank-plus-one cardinality corollary are
   separately checked. No finite-termination or low-rank iterate theorem is
   inferred from this argument.
3. **R supporting-plane interpretation.** RS and the optimizer-intercept bound
   use identical ordered, differentiable, positive-curvature endpoint pairs and
   identical positive bands. Finite convexity and compactness derive G and R,
   then the exact source Tmax=4GR bound and both constant conversions 2C+2Tmax.
4. **R inward sufficiency.** The exact inward Taylor condition differentiates
   only the outer point. Signed inward probes, swapped numerator T-N, and scalar
   optimization derive RS and therefore actual objective/Euclidean solution-set
   convergence. Zero M, zero t and zero curvature cases are handled. This does
   not assert the converse: only the both-differentiable reverse pair estimate
   is currently checked. Convex supporting-vector convergence at a differentiable
   limit is proved as infrastructure for the missing approximation argument.
5. **G incoming jumps.** Actual common-target eligible endpoint families on a
   fixed band, small predicted decreases, and the stated representation with
   vanishing weighted curvature cost exclude visibility and secant suppression
   alone. No transport, field continuity, boundedness, or common BFGS history is
   used. Singular PSD fields and arbitrary nontrivial limiting filters are
   covered. A full limiting Basis, vanishing curvatures and bounded target
   gradients derive representation coefficients through matrix inverse
   continuity; coefficient boundedness is not added as an assumption.
6. **G scalar characterization.** The exact derivative-jump quotient is
   equivalent to scalar certificate existence. Compactness and finite convexity
   derive upper and positive-band lower gradient bounds, making this equivalent
   to Lipschitz control on eligible small pairs only. The explicit canonical
   field is inverse actual gradient squared. Neither all-pair Lipschitzness nor
   continuity of the gradient near a kink is inferred. Empty pair families are
   included.

## T secondary source consequences

The same integration includes bounded-potential absorption, with displayed new
constants and threshold; rank-one transport allowing a zero multiplier; RS as a
rank-one certificate; and equivalence of projected Loewner comparison with its
perpendicular quadratic formulation. A structural neighborhood yields a basin
chosen before every admissible run and arbitrary initial SPD matrix. The
one-sided-shell variant derives eventual shell membership and small predicted
decreases from the actual monotone value limit and Armijo budget. Its compact
sublevel conclusion includes solution-set distance and uniqueness upgrade.
Affine covariance, the Q strict-separation example, and the nonunique entire-solution-set neighborhood-to-basin deduction remain open; direct restriction to an already-contained initial sublevel is checked.

## Representation and scope checks

All matrix quantities are actual BFGS or explicitly defined objective-certificate
matrices. No normalized scalar hierarchy, matrix limit or iterate limit is
assumed in an end-to-end export. The public inward convergence target explicitly
uses Euclidean distance to the image of the actual argmin, as in the prior
tranche. Intermediate scalar recurrences and basis/gradient-bound lemmas retain
visible conditional premises, discharged by their actual objective applications.

The G and R equivalence statements actually need fewer hypotheses than the
report's surrounding setup (for example, star need not minimize F for the
positive-band scalar lower bound). These are proved generalizations. Their
specialization to the original source hypotheses is immediate; no source
conclusion or pair quantifier is weakened.

Independent review of incoming jumps is in `INCOMING_JUMP_PEER_REVIEW.md`;
R's exact constants, sampled-point differentiability and gradient limits are
reviewed in `RADIAL_SECOND_PEER_REVIEW.md`. Root reviewed the full scalar
certificate construction, derived gradient bounds, and both equivalence
implications. Per-module compiler/axiom logs supplement the full audit.

The entire report remains incomplete: H.C and affine lifting, full RS-to-IR,
structural families, remaining G examples/geometry, C/U, and both negative
constructions retain explicit obligations. Missing historical scripts and the
stable-manifold infrastructure requirement are documented in
`NEGATIVE_MODULES_PROOF_DESIGN.md`; historical PASS tables are not proof inputs.
