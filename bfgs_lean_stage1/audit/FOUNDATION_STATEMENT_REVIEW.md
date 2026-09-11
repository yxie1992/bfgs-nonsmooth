# Remaining Module M: statement and dependency review

Review date: 10 September 2026 (local date). Independent agents reviewed the
Hessian, localization, energy, moving-frame, and residual arguments, followed by
the final target propositions and certificate structures. These are internal
independent reviews, not external peer review.

The integrated audit covers 320 explicit theorem declarations and 440 total
theorem declarations including generated auxiliaries. All 14 target signatures
are exact matches and are inhabited again in `Audit.lean`. Current compiler,
axiom, and source-hash evidence is in `STATUS.json`, `build.log`, `axioms.log`,
and `declarations.json`; historical logs do not certify later edits.

## Actual matrix and energy statements

The Hessian update is derived by exhibiting an actual inverse of the full
inverse-BFGS formula. The annihilated part is a proved PSD congruence, kills the
actual step, and has PSD complement in the Hessian. The separate exact
determinant identity is proved. No Hessian recurrence is an input assumption.

Fixed-reference energies, pairings, and corrections are exactly the source's
functions of the actual inverse matrices, iterates, gradients, q and t. The
finite telescope retains terminal energy, and the gap comparison uses
nonnegative monotone gaps before squaring. The negligible-correction and
quadratic-correction value criteria remain conditional on their displayed
correction budgets. The general value criterion does not assume uniqueness.
The registered `QuadraticCorrectionTarget` additionally uses uniqueness to
derive both compactness and iterate convergence; it is a separate upgrade.

## Geometry and norm conventions

The exact sphere minimum requires nonempty spheres, stated through nontriviality
of the normed space. Zero-dimensional compactness and basin statements are
proved separately. Actual infinite admissible runs already imply n>0.

Localization is generic over finite-dimensional real normed spaces and thus
includes Euclidean space. Explicit `Metric.ball` statements on the project's
coordinate type use its Pi norm at the stated radius. No equality of Pi and
Euclidean balls of equal radius is claimed. Convergence and neighborhood-basin
statements do not depend on that radius convention.

Strict contours use the exact frontier condition: no segment contained in the
frontier has distinct endpoints. The positive-level condition is the existence
of a point with value below ℓ. The proof checks that level points lie on the
frontier, and uses compact endpoint pairs and convex segment limits. It does
not assume a convergent gradient subsequence or convergence of the iterates.

## Exact and residual frames

The exact-frame product order is `P_next=P*T`; normalization is by right
multiplication with `P⁻¹`. The actual inverse-congruence trace recurrence yields
an O(N) reciprocal bound and contradicts qualitative growth under d→0. Arbitrary
rectangular frames are allowed. The source's starting P=I is covered by the
stronger statement permitting any invertible starting normalization.

The residual proof derives the smooth-subspace Hessian trace budget and the
actual residual metric energy. Its one-step inequality is proved from PSD
Young and transport bounds before the scalar drift argument is invoked. With
`D=sum d`, the finite constants

    A = 1 + C_T + C_T*D
    C = C_R*(1+D)*(tr(P_S B_0)+L) + C_0

replace the source's d≤1 tail simplification. The PSD-derived nonnegative base
energy justifies enlarging the drift coefficient. Actual shifted runs discharge
all arbitrary-tail conventions. No whole-Hessian growth bound, frame rank, or
invertibility of residual transport T is assumed.

The final source-form residual wrapper removes sign premises on all upper-bound
constants: L, C_0, and C_R have nonnegative signs forced by their norm bounds;
C_T may be enlarged to `max C_T 0`. Only the positive visibility lower bound m
is retained, as in the source.

`FrameNorms.operatorSqBound_iff_opNorm_sq` proves exact equivalence to the actual
Euclidean operator norm and checks transpose norm equality.
`orthonormal_matrix_for_subspace` supplies an actual orthonormal matrix for
every Euclidean subspace, including zero dimension. The associated projection,
column-range, and projected squared-norm identities are also proved.

## Audit and remaining scope

The final `ExactFrameCertificate` and `ResidualFrameCertificate` structures
contain actual frame geometry and norm constraints. They assume no scalar energy
recurrence, matrix hierarchy, or convergence. All such analytic conditions are
discharged by the final target proofs. The complete transitive axiom inventory
contains only `propext`, `Classical.choice`, and `Quot.sound`.

Review caught two audit-tool issues and they were addressed: private helper
names were made public for complete source/environment name matching, and
dependency checks now verify every locked Git revision and reject tracked
dependency worktree changes. The delivery manifest hashes staged repository
artifacts, excluding unrelated untracked notes.

No substantive correction to Module M was necessary. Its omitted sphere and
frontier details are now explicit; disclosed proof-route changes preserve the
conclusions. Original research sources remain unchanged. Other research modules
must still derive the certificates and correction budgets for their objective
classes. These conditional criteria are not an unconditional BFGS convergence
theorem and do not assert universal line-search existence.
