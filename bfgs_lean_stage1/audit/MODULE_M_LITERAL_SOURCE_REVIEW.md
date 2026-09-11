# Module M final literal-source reconciliation

The unchanged `foundation.tex` has 248 lines in five disjoint source spans.
This reconciliation identifies the existing checked statements and the two
supplemental literal exports. It does not replace their compiler/axiom evidence
or the forthcoming integrated milestone18 gate. No original source is changed.
The companion `module_m_literal_source_map.json` records exact declaration
references and the original source hash.

| Source span | Actual proof coverage |
|---|---|
| 1–49 | The actual run derives positive energy, curvature and later SPD from initial SPD, positive step lengths and weak Wolfe. Convex supporting inequalities give both decrease bounds, Armijo summability and compact gradient bounds. Actual Hessian update, PSD annihilated part and step kernel are proved. Generic localization proves the attained sphere gap, radial bound, sublevel compactness and trapping; strict contours give vanishing actual steps without assumed iterate or gradient convergence. |
| 50–102 | Actual principal determinants, trace/top determinant slots, diagonal elementary products and orthogonal invariance are identified. Rank-two compression and Schur identities include singular larger Gram matrices. Exact rank-one increment and captured-energy bounds give the actual full-BFGS hierarchy. The new `principalGramSumIdentity` additionally proves the printed equality at94–99 with the actual SPD eigenbasis chosen before every vector and degree. |
| 103–158 | The actual hierarchy yields the normalized scalar recurrence with the original constants. Weighted potential and fixed-prefix arguments prove geometric/arithmetic mean divergence, the exact finite-horizon bound, and superquadratic reciprocal sums. The new `sharpPrincipalPotential` supplies the source151 polynomial of degree≤n−1, exact optimized parameter D/[c(m−1)], sharp power bound and actual mth-root limit. The fixed-tail liminf statement is already represented by the theorem that every number below1/(2D) is eventually a lower bound after normalizing the actual budget by c. |
| 159–191 | Exact fixed-reference cancellation, finite objective-gap bound, negligible/quadratic correction criteria, moving-frame matrix identity and inverse-congruence trace recurrence are proved. The cumulative-transport hypotheses are explicit and remain trajectory criteria. The contradiction uses the actual reciprocal theorem, not an assumed reciprocal bound. |
| 192–248 | The fixed-subspace projection trace recurrence and linear budget are derived from the actual Hessian update. Actual residual metric energy is bounded by Frobenius square times the derived subspace trace. The PSD trace-square identity and factorization justify the source's square-root/Frobenius notation; Young's inequality is proved in that same metric. The actual source-form tail theorem discharges the scalar drift recurrence and gives the contradiction. It imposes no frame rank, invertible transport or full-Hessian bound. |

The two supplemental claims were not needed to validate the earlier principal
or growth targets: the old proofs used a sufficient Gram-sum inequality and a
sufficient degree-n growth bound. Those valid conclusions did not themselves
verify the stronger displayed intermediate assertions. The supplement now
provides exact statements for both, with no extra mathematical premises.

The combinatorial equality is sign-free before specializing to actual positive
eigenvalues. It treats empty dimension, degree zero and degrees beyond the
dimension correctly. The final target constructs the orthogonal diagonalization
from the SPD matrix; its Gram determinants and vector coordinates are actual
matrix expressions, not supplied scalar data.

The potential polynomial is explicitly constructed from the existing finite
weighted potential. The source horizon m and exponent1/m are retained without
an indexing substitution in the target. Strict positivity of the actual tail
comes from summability and positive predicted decreases. The horizon tends to
infinity with the tail fixed; no uniform bound on the tail matrices is used.
The generic zero-dimensional polynomial case and G=0 are handled, while actual
infinite runs imply positive dimension through their positive energy.

This source reread found no additional discarded mathematical assertion beyond
those two supplements. Some exact equalities are compiler-checked local facts
inside `BFGSCompression` or `ResidualFrames`; a duplicate standalone theorem
spelling is not required to treat those already proved equalities as checked.
In particular, compression numerator/rank-one identities are established from
actual matrices before use, and the factorized Gram trace is exactly the
Frobenius square used in the residual estimate.

All five spans retain the original algorithm and objective convention. The
sequence-only hierarchy results remain reusable conditional lemmas, whose
matrix and objective premises are discharged in the final targets. This map
makes no pointwise q-to-zero, matrix/eigenvector convergence, universal
admissible-step existence or blanket nonsmooth BFGS convergence claim. The
report's separate R source-attribution and E historical-evidence exceptions are
unaffected by completing these Module M assertions.
