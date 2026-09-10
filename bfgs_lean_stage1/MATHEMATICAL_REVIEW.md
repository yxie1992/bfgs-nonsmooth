# Mathematical and statement review

The original M.1–M.3 matrix-run targets and objective-level bridge are compiled with the pinned toolchain
and transitively axiom-audited. This replaces the uncompiled-draft status. Original
target definitions are unchanged apart from documentation comments. Independent
agent reviews appear in `audit/STATEMENT_REVIEW.md` and
`audit/OBJECTIVE_STATEMENT_REVIEW.md`; these are not external peer reviews.

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

## Corrections and unformalized conclusions

No correction to the requested M.1–M.3 statements or objective bridge was needed. The principal-product
inequality is proved directly using an insertion injection instead of exporting
the exact regrouping equality; the potential bound uses degree n instead of n−1.
These disclosed proof choices change no requested conclusion or constant.
Original research sources and `reference/foundation.tex` are unchanged.
`PROOF_OBLIGATIONS.md` records the verified/unformalized boundary.
