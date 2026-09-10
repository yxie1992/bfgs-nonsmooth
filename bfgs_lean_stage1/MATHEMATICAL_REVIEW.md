# Mathematical and statement review

The original M.1–M.3 matrix-run targets are now compiled with the pinned toolchain
and transitively axiom-audited. This replaces the uncompiled-draft status. Original
target definitions are unchanged apart from documentation comments. Independent
agent review appears in `audit/STATEMENT_REVIEW.md`; this is not external peer review.

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
and positive accepted lengths/curvature. Exported targets do not encode an
objective or claim objective convergence. Objective-level derivations of bounded
gradients and summability from compactness/Armijo remain outside this project;
M.2 and M.3 state those hypotheses explicitly.

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

No correction to the requested M.1–M.3 statements was needed. The principal-product
inequality is proved directly using an insertion injection instead of exporting
the exact regrouping equality; the potential bound uses degree n instead of n−1.
These disclosed proof choices change no requested conclusion or constant.
Original research sources and `reference/foundation.tex` are unchanged.
`PROOF_OBLIGATIONS.md` records the verified/unformalized boundary.
