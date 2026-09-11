# Mathematical and statement review

The original M.1–M.3 matrix-run targets and objective-level bridge are compiled with the pinned toolchain
and transitively axiom-audited. This replaces the uncompiled-draft status. Original
target definitions are unchanged apart from documentation comments. Independent
agent reviews appear in `audit/STATEMENT_REVIEW.md`,
`audit/OBJECTIVE_STATEMENT_REVIEW.md`, and `audit/FOUNDATION_STATEMENT_REVIEW.md`;
these are not external peer reviews.

## Actual matrices and original assumptions

`principalSum` remains the sum of actual principal determinants. `inverseBFGS`
is the full undamped inverse-BFGS formula. Positive alpha, energy, and beta are
used exactly where required. Local compression assumes independent columns; the
final theorem constructs and proves that property for eigenbasis coordinate
columns, adding no assumption on the run.

The rank-two formula follows from the determinant lemma for the original SPD
compression and an actual 2-by-2 determinant. One- and two-column Schur identities
are checked for actual appended Gram matrices. Nonnegativity includes singular
Gram matrices. The rank-one increment never inverts the projected compression
or the larger Gram matrix.

Principal-sum invariance follows from the checked generating identity for
`det(I+XH)`: its degree-j coefficient is the actual principal sum. A block
determinant and multilinearity prove that identity; the verified spectral theorem
supplies the eigenbasis. The final hierarchy uses these proved facts, not scalar
identities passed as unproved matrix hypotheses.

## Normalization and line search

Normalized entries are exactly `principalSum (R.H k) j`. The energy bound
q<=||g||² trace(H) uses a PSD square root and Cauchy–Schwarz. Bounded gradients give
||y||²<=4G²; beta>=c gives K=4G²/c² and delta=d/c. Positive trace, terminal zero,
and nonnegative entries are derived.

The weak-Wolfe bridge checks

    g_nextᵀs >= c2 gᵀs  =>  beta >= 1-c2,

using d=−gᵀs=alpha*q and yᵀs=beta*d. Strong Wolfe is not substituted. No matrix
bound, iterate convergence, eigenvector convergence, or finite gradient alphabet
is introduced.

`FullBFGSRun` is the original pure matrix-run specification, including SPD matrices
and positive accepted lengths/curvature. The original targets retain their exact
statements. The new `AdmissibleBFGSRun` supplies the objective-level bridge below.

## Finite convex objective and accepted-run bridge

`AdmissibleBFGSRun` assumes `F : (Fin n → ℝ) → ℝ` is convex on the whole space,
which expresses finiteness everywhere. Its actual derivative at each accepted
point is the continuous linear functional `v ↦ dot g v`. The coordinate space
uses mathlib's Pi norm; in finite dimension this represents the same derivative
and topology as Euclidean coordinates. Matrix energy and `sqNorm` use the
Euclidean dot product explicitly. No transport to the `EuclideanSpace` type is
exported, and no smoothness at other points is assumed.

Only `H 0` is assumed positive definite. Positive alpha and nonzero current
gradient give positive energy; weak Wolfe gives positive curvature. The exact
inverse-BFGS quadratic form then proves positive definiteness of the next matrix.
Induction derives all invariants without assuming future SPD or curvature.
`toFullBFGSRun` keeps the same matrices, gradients, and lengths, with energies,
predicted decreases, and beta definitionally identical.

Convexity and the derivative at the current point give the supporting inequality
and `c₁ d_k ≤ F(x_k)−F(x_(k+1)) ≤ d_k`. Armijo keeps iterates in the initial
sublevel. A lower bound on values along the run yields summability and the tail
budget `sum_i d_(J+i) ≤ (F(x_J)−L)/c₁`; a finite limiting value also supplies such
a lower bound, without claiming it is optimal.

Finite convexity supplies continuity. On a compact set, values are bounded below,
and all supporting vectors are bounded by evaluating at coordinate translates
of that set. This proves the accepted-gradient bound without continuity of the
gradient, including when the function is nonsmooth elsewhere. The compact-sublevel
exports derive both bounds. The separate bounded-gradient/lower-value-bound
exports avoid imposing compactness where the more general hypotheses suffice.
They apply the existing matrix hierarchy, never an assumed scalar hierarchy.

## Qualitative means

The weighted shift identity includes its terminal term. For any fixed contraction
factor, one fixed potential and one tail are selected. The log telescope retains
the entire finite prefix. Exponentiation yields the actual product-root geometric
mean, and log(u)<=u transfers divergence to the arithmetic mean.

This replaces the source's qualitative root/AM–GM presentation. It does not infer
pointwise q_k→0 or the stronger summable-budget result without its separate proof.

## Finite horizon and ordered tail limit

The exact finite bound is exported in real-power notation with the source's
constants, actual matrix potential, and tail sum. Formal m+1 is source m; formal
m>0 is exactly source m>=2.

Optimized eta depends on the horizon, while J and its matrix are fixed. The proof
bounds the potential by a polynomial of degree n, a convenient weaker estimate
than the source's n−1; either gives the same root limit. The explicit normalized
lower function tends to 1/(2D), with D the normalized tail budget. The nonnegative
prefix and factor ((m+1)/(J+m+1))²→1 are handled explicitly. Only then does
summability make the tail budget arbitrarily small. No bound on H_J uniform in J
is required.

## Hessian, fixed-reference energy, and correction criteria

`hessianUpdate` proves the displayed candidate is an actual left inverse of the
full inverse-BFGS update. It does not assume the Hessian recurrence. The
annihilated part is an actual congruence of `H⁻¹`, hence PSD, and kills the actual
step. The determinant equality `det H_next=(alpha/beta) det H` is also proved,
closing the separate exact top-degree identity beyond the original inequality.

Fixed-reference energy uses exactly `B_k=(H_k)⁻¹` and the original correction
`(y_kᵀ(x_(k+1)−xstar))²/t_k`. Annihilation proves the cancellation, and telescoping
retains the terminal nonnegative energy. The gap comparison uses nonnegative
monotone objective gaps before squaring. Both the negligible-correction and
quadratic-correction convergence criteria are proved, with those correction
conditions explicit. Unique-minimizer value convergence is then lifted to point
convergence by the proved local basin; no iterate limit is assumed.

## Localization and strict contours

The positive sphere minimum is attained on a compact nonempty sphere. Its exact
minimum statement explicitly requires a nontrivial space. Separate proofs cover
zero-dimensional compactness and neighborhood basins, and actual infinite runs
already imply positive dimension. Radial convexity proves the outside-sphere
lower bound, low-sublevel trapping, and compactness of every sublevel.

The generic localization theorems hold in every finite-dimensional real normed
space. `Vec n` has the default Pi norm, so its displayed ball radius refers to
that norm. Euclidean localization is an instance of the generic theorem; no
equality between Pi and Euclidean balls of the same radius is asserted.

For strict contours, the formal proof uses compact endpoint pairs rather than
extracting a convergent gradient subsequence. Supporting inequalities and d→0
force every point on a limiting segment to have value ℓ. The proof explicitly
shows that such a level point lies on the frontier when some point has value
strictly below ℓ. This supplies the step omitted from the short source proof,
without a new assumption. The positive-level hypothesis is stated as
`∃ y, F y < ℓ`, avoiding an unnecessary attained-minimum assumption.

## Exact and imperfect frame transports

For exact transport, normalizing the frame by `P_k⁻¹` removes `T_k` in the correct
order `P_(k+1)=P_k*T_k`. The actual trace recurrence yields an O(N) reciprocal-sum
bound, contradicting qualitative reciprocal-mean growth. The proof does not
replace d→0 with the stronger summability assumption. Rectangular frames need
not have full rank. Invertibility concerns the cumulative transport matrices,
as in the source, and never a new constraint on BFGS matrices.

For imperfect transport, `UᵀU=I` defines the actual fixed projection `UUᵀ`.
Projection identities, projected squared norms, and the equivalence of fixed
residual columns with subspace membership are proved. The Hessian update derives
`tr(P_S B_k) ≤ tr(P_S B_0)+L*k`. The residual-energy estimate and PSD Young bound
then derive the scalar recurrence, before any scalar contradiction is invoked.
No whole-Hessian bound, frame rank, or invertible T is assumed.

The source uses a tail with d≤1. The formal proof instead uses the finite global
bound `D=sum d`, obtaining drift coefficient `1+C_T+C_T*D` and additive constant
`C_R*(1+D)*(tr(P_S B_0)+L)+C_0`. This changes no conclusion or hypothesis.
The source-form wrapper derives the nonnegativity of L, C_0, and C_R from their
actual norm bounds and enlarges C_T to `max C_T 0`; its final statement adds no
sign premises. All tail versions use the actual shifted run and derive its SPD.

`FrameNorms` proves that the quadratic transpose-action bound is exactly the
squared Euclidean operator-norm bound and that every Euclidean subspace has an
orthonormal matrix representation, including zero-dimensional subspaces.

## Corrections and unformalized conclusions

No substantive correction to Module M was needed. Sphere nonemptiness and the
level-to-frontier step are now explicit. The principal-product
inequality is proved directly using an insertion injection instead of exporting
the exact regrouping equality; the potential bound uses degree n instead of n−1.
These disclosed proof choices change no requested conclusion or constant.
Original research sources and `reference/foundation.tex` are unchanged.
`PROOF_OBLIGATIONS.md` records the verified/unformalized boundary.


## Entire-report execution: first tranche

The original Module M proof chain remains intact. The five exact report-level
exports in `ReportCoreTargets.lean` are now compiled and transitively audited:
T's primary transported-certificate theorem, H.A's unrestricted homogeneous
value dichotomy, G's scalar theorem with arbitrary positive metrics and its
actual full-BFGS specialization, and convergence under R's radial condition.
Shared compact analysis supplies nonunique solution-set distance, with an exact
Euclidean realization in the public targets. The 19-target audit passes for all
417 explicit / 594 total theorem declarations.

See `audit/REPORT_CORE_STATEMENT_REVIEW.md` and the separate T, H and compact/radial
peer reviews for the exact quantifier and proof-dependency checks. No substantive
correction to these primary source statements was needed. T/H use the stronger
proved reciprocal-sum theorem after deriving its summability requirements; T's
unused strict top-sublevel inequality is removed in a proved generalization.

The full report is not verified. `ENTIRE_REPORT_PLAN.md` and
`audit/REPORT_STATUS.json` cover the remaining modules. Initial investigation of
Q records that its printed eligible separation pair covers only c1≤2/3; a
parameterized generalization is proposed for all c1<1 and still requires Lean
verification. This observation is not used to overclaim the example's scope.


## Entire-report execution: second tranche

The full pinned build and transitive axiom audit pass for 528 explicit / 768
total theorem declarations and 26 exact targets. The seven new targets cover
exact normalization, actual recurrent affine-hull geometry and max-linear escape,
radial/supporting-intercept equivalence, inward-certificate convergence, incoming
jump obstruction, and scalar certificate characterization. Additional checked
consequences include rank-one/projected transport, bounded-potential absorption,
unique-minimizer local basins, one-sided shells, and recurrent cardinality.

The statement/dependency review is `audit/REPORT_GEOMETRY_STATEMENT_REVIEW.md`,
with separate incoming-jump and radial peer reviews. No mathematical axiom was
added. A failed audit caused by an outdated namespace in one #check command is
preserved in audit/history; it was corrected before the passing full rerun.

Full RS-to-IR still needs approximation through jointly differentiable points;
the paired reverse estimate does not discharge this. Nonunique solution-set
neighborhood localization, H.C/affine lifting, remaining G examples and geometry,
and the other modules remain explicit obligations. Source reading also identified
precision issues in C's oriented determinant, U's non-additive example at c=0,
and C's use of smooth for C1 fields; these are recorded in
`audit/PLANAR_FIXED_NORMAL_INVENTORY.md` for exact formal correction. Original
research sources remain unchanged.


## Entire-report execution: third tranche

The complete audit passes for 760 explicit / 1,069 total theorem declarations
and all 36 exact targets, with only standard axioms and matching Lean source
hashes. The ten new targets are reviewed in
`audit/REPORT_CONTINUATION_STATEMENT_REVIEW.md`; independent radial, local-rate,
affine, scalar-example and finite-pair reviews accompany actual compiler logs.

Full RS-to-IR and its local derivative-free central counterpart are now proved.
Affine projection constructs an actual reduced full-BFGS run; lifting transfers
the source's explicit projected limit and uniquely characterizes the initial-
metric fiber projection. Nonunique minimizers now have the full neighborhood
basin result. Finite and little-o rates retain their actual correction premises;
the homogeneous rates derive their budgets. The logarithmic criterion is proved
but its quadratic-gauge correction application remains open. Both literal scalar
nonnecessity examples and finite-sample/individual-pair claims are checked.

No original research source was changed. The broader family/geometric/negative
construction and synthesis obligations remain recorded; entire_report_verified
is still false. Proof designs in audit/scratch are outside this verified tranche.

## Fourth milestone: structural applications and geometric scope

The pinned full build and transitive audit pass for 996 explicit / 1,384 total
theorem declarations and all 44 exact targets. The fourth tranche adds the
actual centered and quadratic-gauge families, affine covariance, main planar
H.C, G ellipsoid/pointwise/accessibility geometry, and Q foundations through
Q.13. Statement and peer reviews are collected in
`audit/REPORT_APPLICATIONS_STATEMENT_REVIEW.md`; actual logs are
`audit/report_applications_check.log`, `audit/build.log` and `audit/axioms.log`.

The G.4 correction distinguishes accessible and all-active jump spans. Its
precise accessible-span consequence is proved, the full-active version keeps
its necessary qualification explicit, and the algebraic countermodel is not
misrepresented as an objective example. Original research sources remain
unchanged. `audit/REPORT_STATUS.json` records this separately.

Next independent work is Q's derived finite-envelope calibration and uniform
compensated transport, H's remaining block/low-rank/relative-interior clauses,
and F's transformed-gauge family. Remaining R/F applications, C/U/A and D/L
constructions, and synthesis/evidence closure are still obligations. Entire-report
verification remains false; no generic conditional criterion is counted as its
undischarged objective-specific application.

## Fifth milestone: parabolic and transformed families, H.8, and G.4 correction

The pinned full build and compiled-environment axiom audit pass for 1,202
explicit / 1,675 total theorem declarations and all 52 exact targets. Logs are
`audit/report_families_check.log`, `audit/build.log` and `audit/axioms.log`.
Only propext, Classical.choice and Quot.sound occur; every audited source hash
matches. See `audit/REPORT_FAMILIES_STATEMENT_REVIEW.md` and its linked reviews.

Q's arbitrary original finite family now has a derived actual θ²rrᵀ certificate
and full-BFGS value/iterate convergence. Uniform calibration, denominator,
logarithm and transport data are proved before all eligible pairs. The explicit
three-branch objective has actual SPD first-step witnesses, arbitrarily small
eligible decreases and unbounded radial quotients on a fixed positive band in
every neighborhood. The printed c1≤2/3 pair scope and the all-c1 rho extension
are distinguished. Literal ordered pruning and printed-field identification
remain separately tracked source-description obligations.

F:transform is proved including literal inverse/Theta' formulas and endpoint
gauge differentiability. H.8 has both the full-slope and actual recurrent-tail
convergence conclusions, derived coordinates and exact initial/current metric
fiber limits. H.7.4 and remaining H class bookkeeping are next-tranche work.

G.4's missing accessibility qualification now has an actual convex-objective
counterexample: shiftedAbs with (c1,c2)=(1/8,1/4), a continuous constant-I band
certificate and genuine limiting gradients whose full-active tangent is zero.
Accessible jumps are zero for these constants. The qualified accessible-span
statement remains valid. Original sources are unchanged; the correction and
example scope are recorded in `audit/G4_ACTUAL_OBJECTIVE_CORRECTION_REVIEW.md`.

Entire-report verification remains false. Remaining F/R applications, G
interpretations, C/U/A, D/L constructions and final synthesis/evidence coverage
remain explicit obligations. Next-tranche drafts live only under audit/scratch
and are excluded from this release manifest until fully integrated and audited.

## Sixth milestone: finite structural families and source closure

The pinned full build and compiled-environment audit passed for **1,445 explicit
and 2,014 total theorem declarations**, with all **61 exact targets** inhabited
and only propext, Classical.choice and Quot.sound in transitive dependencies.
The exact 177 source hashes match the audited bytes. Actual logs are
`audit/report_structures_check.log`, `audit/build.log`, `audit/axioms.log`;
statement scope is reviewed in `audit/REPORT_STRUCTURES_STATEMENT_REVIEW.md`.

Q's original-family theorem and every internally retained source construction
are now mapped, including literal ordered pruning, printed scale and strict
acceptance identities. H's internal H.7.4/class/energy statements are now proved;
its cited earlier three-gradient construction and external two-piece termination
result remain cross-references to reconcile. The rank-at-least-three open
question remains classified as a conjectural gap, not as a theorem.

F's actual max-affine active reduction, literal extended-real threshold and
tail basin are proved, as is the actual coercive five-piece finite line-search
obstruction in every neighborhood of its unique minimizer. R's arbitrary mixed
gauge powers, actual finite polyhedral C1,1 extensions and smooth-plus-PLQ basins
are proved. Extensions need not be convex off their cells. The proof derives
one-sided radial matching; the source's stronger full-gradient boundary assertion
is separately pending. No matrix/iterate convergence or algorithm modification
was added to any family theorem.

The A barycentric Gram-inverse and local affine-independence/positive-coefficient
geometry is checked, but its application to actual finite smooth-max subdifferentials
is still a separate obligation in this frozen release. New scratch proofs do not
change the verified status until integrated and audited.

Entire-report verification remains false. Continue with the explicit matrix-limit
run, finite-ray-singularity step existence, residual decompositions, R branch and
spectral boundary cases, A/C/U, D/L and source synthesis. Review and push the
milestone, then continue these independent proof chains autonomously.

## Seventh report statement review

The full frozen audit passes 1,848 explicit theorems, 2,636 total declarations and
78 exact targets, standard axioms only. See audit/REPORT_ANALYTIC_STATEMENT_REVIEW.md
and its linked scoped/independent reviews. Actual convex subdifferentials, real
Frechet derivatives, full BFGS matrices, actual closed-box polynomial roots and
actual Hermitian eigenvalues are modeled, rather than supplied as certificate
premises. The generated rational seed candidates are checked by Lean ring and
norm_num proof terms; the generator is not a mathematical oracle.

U.1/U.2's smooth-strip bound uses local derivative Lipschitzness together with
full strong curvature. This replaces a source cocoercivity argument without
adding assumptions or changing the unspecified constant. It does not establish
the weaker tangential-only U.6 extension. The C orientation algebra and U's
variable-jump non-additive assertion have separately recorded source corrections:
the signed determinant changes sign when det(T,n)=-1 (absolute estimates are
unchanged), and non-additivity requires c≠0 because the printed norm(c)<1 permits
zero. Original research sources remain unchanged; see the report correction
register and the C/U scoped reviews.

D/L's exact source root box, inverse-Jacobian identification, residual bound and
strict actual Jacobian supremum bound are proved, including box boundaries.
Every later update-specific denominator and every deterministic accepted/rejected
trial remains an independent obligation until the actual cycle is formalized.

## Eighth report statement review

The frozen pinned build and complete transitive axiom audit pass 2,193 explicit
and 3,134 total theorem declarations, with 85 exact targets and only
propext, Classical.choice and Quot.sound. See
audit/REPORT_DYNAMICS_STATEMENT_REVIEW.md and its independent peer reviews.

The deterministic seed is now a genuine full-BFGS trajectory: its exact update
closure, point cycle, actual derivatives, all strict oracle decisions and exact
bracket-search execution are proved. Limits follow from the rho-powered orbit;
nonstationarity follows from the actual supporting-subgradient inequality. No
iterate/matrix convergence or accepted-length oracle was inserted as a premise.
The seed objective is not the final coercive/local D or L construction.

U.6 now uses only source tangential curvature and relevant strict contours; its
frame, secants, support split and vanishing steps are derived. C's actual field
is constructed with common all-support pairing and neighborhood visibility,
while endpoint transport/secant and final consequences remain open.

R's general-degree optimizer intercept has the exact term +F(0). Positive degree
forces F(0)=0, but degree-zero positive constants show the unqualified simplified
formula needs normalization. The correction is recorded without editing sources.
The inherited C orientation and U c!=0 qualifications remain explicit. Actual
Hessian/ray identities do not justify an a.e.-only radial-curvature criterion;
that separate caveat remains pending in this frozen snapshot.


## Ninth report statement review

The frozen project audit passed 2,718 explicit and 3,841 total theorem
declarations and 95 exact targets. `REPORT_CONSTRUCTION_STATEMENT_REVIEW.md`
records the exact scope, and independent reviews cover the scalar construction,
actual infinite-spike objective/oracle, and corrected supporting-plane example.
All derivative interchanges, infinite tails, deterministic search histories,
and objective-level limits are proved in Lean. Actual derivative existence at
accumulation points is asserted explicitly where required.

D's positive scalar is implemented as a ramp series proved equal to every
printed piece. Its second derivative is an attained nonnegative ramp component;
the Lipschitz proof compares that component with the full sum. Combining the
positive and negative halves takes the maximum of their second derivatives
and constants. These proof-route changes preserve the literal construction and
sharp constants. C's right-derivative comparison avoids assuming a finite
crossing partition. U's executable rational oracle is universally identified
with the actual infinite integral, including both derivative outputs.

R's historical(-1,5),25/4 attribution could not be recovered. The currentD
objective has optimizer(-1,16), heights0,0,-1+c-16d, and actual RS/SP failure;
the discrepancy and its checked correction are explicit in
`audit/COERCIVE_SEED_INTERCEPT_CORRECTION.md`. No original source was overwritten.
The remaining entire-report obligations are retained in `audit/REPORT_STATUS.json`.


## Tenth report statement review

The frozen compiled-environment audit passes 3,004 explicit / 4,254 total
theorem declarations and 106 exact targets. D's geometry target uses actual
Frechet Hessians and the literal four scalar-composed branches; its dynamics
target has no assumed local model or search history. The proved slab identity
supplies all accepted and rejected trial values and gradients. All matrices are
those of the actual full update, and all limits are derived. Literal right-zero
Big-O estimates and source plateau bounds are separately checked.

C's source chart convexity remains explicit. Actual branch gradients, a genuine
tie point and exact support-jump cancellation yield the uniform all-eligible-pair
secant estimate. One actual field supplies that estimate and late log transport,
so the original-objective principal theorem has no certificate assumption.
Its stronger all-pair transport statement remains a distinct obligation.

U's nonsplitting proof allows an arbitrary scalar function; only the proposed
smooth term is differentiable. The necessary c!=0 qualification is explicit.
L's least-norm hull point and optimizer are actual objective calculations and
make no persistence assertion. All scope and independent reviews are linked in
`audit/REPORT_EMBEDDING_STATEMENT_REVIEW.md`. Historical R attribution remains
unresolved as documented; no original research source was overwritten.


## Eleventh report statement review

The full audit passes 3,346 explicit / 4,762 total theorem declarations and
120 exact targets. A's distance is the actual Euclidean distance to the affine
hull of the actual subdifferential, not a surrogate gap. C's finite-max application
only requires original-active independence and positive weights, and its common
Hessian premise is on actual second Frechet derivatives. The literal quadratic
example has actual eligible/SPD-realized pairs and eta chosen before every
smallness parameter and proposed radial constant; its convergence theorem does
not infer divergence from those pairs.

The rectangular nuclear construction uses actual Gram eigenvalues, square-root
trace and an attaining spectral-contraction witness in arbitrary dimensions,
including rank zero. All named objective applications derive norm properties
before applying convergence criteria. L's actual normalized return holds input
tau fixed through all three substeps, and its positive-scale neighborhood derives
all actual search decisions and point/matrix updates.

The nonlinear orbit is constructed by a contraction on the complete space of
sequences tending to zero, after proving the operator maps that space to itself;
no convergent orbit is assumed. Explicit inverse coordinates and conjugacy give
the required stable/inverse-unstable norm bounds from the stated actual block
roots. Actual spectral inputs and global BFGS application remain open in this
release; smooth-manifold regularity is not implied by orbit existence. All exact
scopes and independent reviews are linked in
`audit/REPORT_STRUCTURAL_CLOSURE_STATEMENT_REVIEW.md`.


## Twelfth milestone: actual L dynamics and fixed-metric local failures

The complete pinned build and transitive axiom audit passed 4,039 explicit
theorems, 5,852 total theorem declarations including generated auxiliaries, and
all 145 registered exact targets across 488 frozen Lean sources. Only propext,
Classical.choice and Quot.sound occur. Evidence: audit/report_l_failure_check.log,
audit/build.log, audit/axioms.log, audit/STATUS.json and the frozen source manifest.

L's actual shape Jacobian, kernel rational spectral certificate, full characteristic
polynomial, parameter dependence and local inverse now supply the constructive
positive return orbit. The final actual global Q_mu BFGS run has no assumed
spectrum, trajectory or limit; every deterministic query and its actual derivative
is proved. Both literal smooth and countably affine local embeddings now have
actual infinite BFGS run families with one fixed SPD initial matrix, nonstationary
positive-value limits, strict Armijo/weak Wolfe, exact complete search histories,
and uniform all-query smallness as starts tend to 0. Scalar regularity, the
source 439/446/27 and 512 constants, actual Hessian bounds and local-copy identities
are checked. See audit/REPORT_L_FAILURE_STATEMENT_REVIEW.md and linked independent
reviews for each exact source boundary and reproducible scoped audit.

A's actual path calculus, bounded signed support representations, genuine
polynomial projection reduction and exact affine-coordinate Boolean elimination
are verified infrastructure; general nonlinear QE and finite semialgebraic path
decomposition are still required. C's literal three-dimensional transport warning
and the same quadratic's actual radial convergence are checked.

The entire report remains incomplete. L's fixed identity initialization and its
transformed constants/search/family conclusions are outside this frozen milestone,
as is smooth stable-manifold regularity/tangency. A's general semialgebraic
application/rank-loss spectrum, C's remaining uniform and higher-dimensional
partial statements, and final family/source/synthesis/evidence reconciliation
remain active obligations. Original research sources are unchanged.


## Thirteenth milestone: identity initialization and invariant stable manifold

The frozen pinned build and full transitive axiom audit passed 4,291 explicit
theorems, 6,264 total theorem declarations including generated auxiliaries, and
162 registered exact targets in 543 Lean files. Only propext, Classical.choice
and Quot.sound occur. Evidence: audit/report_source_closure_check.log,
audit/build.log, audit/axioms.log, audit/STATUS.json and the frozen source hashes.

Both actual L local failure families now use identity initialization for one
fixed objective each, with all exact search histories, actual query derivatives,
strict Armijo/weak Wolfe, positive nonstationary limits and uniform query
locality. Actual transformed strong-convexity/Lipschitz/Hessian constants are
derived from the fixed SPD square root. The actual L return map now has a
smooth embedded two-dimensional locally invariant stable manifold, with actual
stable tangent space and positive physical scales. These are conclusions, not
assumed orbit or spectral data.

C's same constructed field satisfies all three uniform estimates for every
sufficiently close eligible endpoint pair. A's literal rank-loss Hessian spectrum,
genuine univariate cells and actual arbitrary-degree simple-root local charts
are checked. T/F source details are closed; G is covered with its explicitly
documented accessible/active-span correction and actual objective counterexample.
See audit/REPORT_SOURCE_CLOSURE_STATEMENT_REVIEW.md and its linked independent
reviews and delivered-only reproduction scripts.

The entire report remains incomplete. A still needs general nonlinear
semialgebraic projection and finite smooth-path decomposition/application; C
still needs its arbitrary-dimensional constant-rank field/secant partial
construction and A-dependent alternative. Final numerical-display, historical
source, synthesis and evidence reconciliation remain active. Original sources
are preserved, including every disputed claim and documented correction.


## Fourteenth milestone: constant-rank geometry, precision and two-piece termination

The frozen pinned build and full transitive audit passed 4,469 explicit theorems,
6,568 total theorem declarations,178 exact targets and582 frozen Lean files.
Only propext,Classical.choice and Quot.sound occur. Evidence is in
audit/report_geometry_completion_check.log and the accompanying frozen manifest,
compiler logs, declaration inventory and source statement review.

C's actual arbitrary-dimensional constant-rank construction now derives one C1
comparison field and uniform all-endpoint secant correction from the original
active gradients. C2 input does not justify C-infinity field regularity; the
qualification is explicit. L's complete source map and actual Jacobian precision
certificate close its remaining display claim, with a documented last-digit
nearest-rounding correction. The literal two-piece actual BFGS transition relation
is well-founded, and its terminal search ray exposes unboundedness. Arbitrary
full-row-rank linear images have no infinite actual admissible continuation.
The pre-existing two-piece theorem retains Xie–Wächter attribution.

A now has actual finite degree/multiplicity strata, derivative charts, exact
global quadratic root/sign projection with degeneracies, and arbitrary-degree
positive pseudo-division with one finite remainder family chosen before every
specialization. These fragments do not establish general Boolean projection.
General semialgebraic elimination and finite smooth paths, the dependent C
alternative, D numerical-display precision and final synthesis/evidence
reconciliation remain active. The entire report is not yet verified.


## Fifteenth milestone: general projection, critical definability and source conclusions

The frozen pinned build and full transitive audit passed 4,768 explicit theorems,
7,134 total theorem declarations, 205 exact targets and 633 frozen Lean files.
Only propext, Classical.choice and Quot.sound occur. Evidence is in
audit/report_algebra_completion_check.log, STATUS.json and the accompanying
source hashes, actual compiler/axiom logs and statement/independent reviews.

Actual arbitrary-degree Boolean and finite-coordinate semialgebraic projection
is now proved through actual root-index recursion, sign determination and finite
sampling. Actual supporting/affine-critical set/graph definability follows.
The finite semialgebraic smooth-path argument, finite critical values and low gap,
and C's dependent alternative remain open; conditional path-cover statements
are not a proof of those premises.

H's actual three-gradient rank-two sharpness and I's literal ridge supersession
are proved. D's actual numerical precision, original-box update denominators and
literal Euclidean nine-query locality bound are proved, with five documented
nearest-rounding corrections; four immediate literal exports await the next
central gate. I's complete source reconciliation and E's historical-evidence
classification distinguish checked mathematics from absent original run records.
The entire report remains incomplete. Original research sources are unchanged.


## Sixteenth milestone: actual finite geometry, critical values and planar tame basins

The frozen pinned build and transitive audit passed 5,002 explicit theorems,
7,486 total theorem declarations, 233 exact targets and 693 frozen Lean files.
Only propext, Classical.choice and Quot.sound occur. Actual logs and frozen
hashes are report_tame_geometry_check.log, STATUS.json and their companions.

The actual arbitrary-dimensional semialgebraic finite smooth cover is proved
from polynomial root analysis and finite sign refinements. It yields actual
finite ordinary/smooth-path components, finite affine-critical values, the
original low gap and the planar tame convergence basins, without any assumed
geometric decomposition or convergence. D's literal non-strict search and
remaining finite-algebra identities also pass; all453 D lines are reconciled.

The stronger literal A assertions about semialgebraic path graphs and general
piecewise-C1 composition remain in a separate active proof scope. Historical E
jobs/counts/timings/archive identities and R's unidentified older four-piece
numerical claim remain unresolved. The latter is a mathematical attribution
exception, not merely execution history. No original claim is silently retired.
All original research sources are unchanged; the entire report flag is false.


## Seventeenth milestone: literal semialgebraic paths and composition

The pinned full build and transitive audit passed 5,111 explicit theorems,
7,684 total theorem declarations, 249 exact targets and 726 frozen Lean files.
Only propext, Classical.choice and Quot.sound occur. Actual closed evidence is
in report_semialgebraic_path_check.log, STATUS.json and the source/hash records.

Actual semialgebraic path graphs, a finite cover in arbitrary dimension,
finite actual continuous-semialgebraic path classes, same-curve regularity and
actual objective composition now close A's literal geometric proof ingredients.
Continuity includes the closed interval; smoothness is asserted off a finite
set of interior parameters, without endpoint derivative claims. C's literal
smooth-path constancy and I's synthesis are covered. All earlier mathematical
corrections remain explicit and the original research sources are unchanged.

M's principal theorems remain verified. The source's additional exact Gram-sum
identity and sharp degree-n−1 potential bound were found to need explicit
exports beyond the sufficient inequalities used in those proofs. They remain
a separate active scope until their delivered compiler/audit gate passes.

R182–187's older four-piece objective is unidentified, so its printed numerical
attribution remains a mathematical obligation. E's original 19-job archive,
counts, timings and execution identities remain unverified. Current D's proved
correction and current universal Lean proofs do not establish those missing
source facts. The entire original report flag remains false pending resolution;
no claim has been silently dropped or replaced by an added assumption.


## Eighteenth milestone: literal M identities and complete shared-graph audit

The pinned complete build and transitive audit passed 5,126 explicit theorems,
7,704 total theorem declarations, 251 exact targets and 729 frozen Lean files.
Only propext, Classical.choice and Quot.sound occur. Actual complete evidence
is in report_literal_foundation_check.log, STATUS.json and their companions.

The exact actual-SPD eigenbasis Gram-sum equality closes foundation94–99.
The constructed optimized principal-potential polynomial, sharp degree n−1
bound and actual horizon root limit close foundation151–155. The earlier
principal-matrix and reciprocal-growth proofs remain unchanged.

The shared dependency-graph collector preserves Lean4.19's exact checked
constant cases and handles cycles by reverse reachability. Every milestone17
theorem's type/axiom set was compared with its complete ordinary audit; all
new scoped declarations also passed ordinary collector checks. All original
trailing axiom/target commands remain. This tooling change supplies no proof
premise and changes no mathematical theorem or pinned dependency.

R's unidentified older four-piece numerical objective and E's absent original
19-job archive remain source-resolution obligations. Neither current D nor
current Lean executions establishes those missing original inputs. The entire
original report remains unverified pending their explicit resolution. All
research originals, documented corrections and explicit questions are preserved.
