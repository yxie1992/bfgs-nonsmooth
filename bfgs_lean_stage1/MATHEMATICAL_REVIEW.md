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
