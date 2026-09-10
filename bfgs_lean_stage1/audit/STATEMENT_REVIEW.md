# Mathematical statement and dependency review

Reviewed on 2026-09-10 against the unchanged source Module M in
`BFGS_MASTER_REPORT_LaTeX/report/chapters/foundation.tex`. This review complements,
and does not replace, the pinned compiler and transitive axiom logs.

## Actual matrix statements

`BfgsVerification.principalMinorHierarchy` inhabits the original
`PrincipalMinorHierarchyTarget`. The target uses the actual full inverse-BFGS
matrix, its actual principal-submatrix determinants, arbitrary finite dimension,
SPD input, and positive alpha, q, and beta. No determinant inequality, spectral
limit, matrix bound, or normalized hierarchy is supplied as an extra premise.

The single-compression proof in `BFGSCompression.lean` derives its input matrix
from the actual inverse-BFGS definition. Injectivity of the compression columns
is proved for orthogonally transformed coordinate inclusions. In
`CompressionDeterminant.lean` and `GramSchur.lean`, only the original SPD
compression is inverted. Neither the projected compression nor the larger Gram
matrices is assumed invertible. The rank-one determinant increment is exact,
and nonnegative larger Gram determinants and the compressed-energy bound are
proved from the actual Gram matrices.

`PrincipalInvariance.principalSum_conjugate` proves invariance of the actual
principal-determinant sum. Its proof identifies that sum with a coefficient of
`det(I + X H)` by determinant multilinearity and block reindexing. In particular,
the row-selection lemma explicitly uses the matrix identity, not the constant
one function. The public invariance result is stronger than orthogonal
invariance and is used with the proved orthogonal diagonalization.

The eigenbasis Gram bound uses a direct injective finite-set summation argument.
This proves the required inequality without assuming the source's combinatorial
identity or replacing principal determinants with an uninterpreted sequence.
The hierarchy theorem retains the source's degree range. Its proof also works
outside that range, but the public target has not been changed.

## Normalization and growth statements

`Normalization.lean` constructs `NormalizedHierarchy` from the actual principal
sums, with K = 4 G^2/c^2, C = G^2 and delta = d/c. It proves trace domination,
trace positivity, the terminal slot, and nonnegative coefficients. Its temporary
`hminor` parameter is explicit; end-to-end exports must instantiate that parameter
with `BfgsVerification.principalMinorHierarchy`. Such an implication alone is not
an end-to-end theorem.

The scalar qualitative and quantitative declarations are correctly labeled
conditional. They do not assume their growth conclusions. In the quantitative
proof, nonnegative summable delta is supplied by positive predicted decreases
and the stated summability hypothesis. No convergence of q, H, eigenvectors, or
iterates occurs in these hypotheses.

`QuantitativeGrowth.hierarchy_finite_horizon_rpow` matches Module M.3 after writing
the block length as m+1 and its normalized budget as D/c. The actual-matrix
normalization wrapper uses the true infinite tail sum of d. The bound retains
its explicit potential and constants; it is not only a qualitative consequence.

The superquadratic proof fixes a tail first, proves its horizon limit, restores
the nonnegative fixed prefix explicitly, and only then chooses arbitrarily small
tail budgets using summability. The potential is bounded by a polynomial of
degree n, a disclosed harmless overestimate of the source's degree n-1. Its
logarithm divided by the horizon tends to zero. The resulting eventual lower
bounds are every a < 1/(2D) for a fixed normalized tail budget D, and the final
conclusion is divergence of the full reciprocal sum divided by N^2.

No mathematical correction to Module M.1-M.3 was required in this review. The
logarithmic AM-GM presentation, polynomial-degree overestimate, and finite-set
summation proof are alternative proofs of the same stated conclusions.

## Scope and final integration checks

The frozen targets describe an algebraic full-BFGS run and the bounded-gradient,
weak-Wolfe curvature, and predicted-decrease hypotheses relevant to M.1-M.3.
They do not themselves formalize a finite convex objective, differentiation,
Armijo acceptance, compact-level-set gradient bounds, or objective descent to a
finite limit. The separate accepted-step weak-Wolfe bridge correctly yields
beta >= 1-c2 without a strong-Wolfe assumption. Claims about an objective-level
algorithm must distinguish these proved algebraic targets from any additional
objective-analysis wrapper.

Standalone builds and axiom reports for the quantitative and invariance modules
are stored in `quantitative_build.log`, `quantitative_axioms.log`,
`principal_invariance_build.log`, and `principal_invariance_axioms.log`. The
reported dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
The final project audit must additionally check the integrated end-to-end
exports and the remaining source declarations.

## Integration follow-through (primary agent)

The integrated `EndToEnd.lean` now supplies `principalMinorHierarchy` to every
normalization/growth wrapper. `Audit.lean` requires terms of all three original
target types with no additional premises and prints the full finite-horizon and
normalization signatures. The final clean bootstrap and complete audit passed:
115 explicit theorem declarations, 167 including generated theorem declarations,
no missing axiom reports, and no dependencies beyond the three listed above.
The entire code of `Definitions.lean` was compared to pushed checkpoint `2c8bb60`;
only documentation comments changed (`target_preservation.log`).
