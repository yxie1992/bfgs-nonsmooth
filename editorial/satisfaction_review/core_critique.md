# Skeptical core-proof review

No material proof gap was found in the actual matrix-to-reciprocal-to-objective chain. This review reread the printed proof and expanded the formal target definitions, rather than relying on prior PASS records.

## Admissibility is an actual algorithmic contract

ObjectiveDefinitions.lean30–51 gives actual F derivative, positive initial matrix, full update, positive step and weak Wolfe; no boundedness/summability/convergence field is assumed.

## Actual principal determinants

Definitions.lean41–55 uses det of actual submatrices in a finite powerset-card sum. PrincipalHierarchy.lean sums actual compressed Gram determinants after an orthogonal diagonalization; it does not assume the scalar hierarchy.

## Compression calculation

Reexpanded the rank-two determinant: detA[(κ−w)²+u(r−z)]/κ². The nonnegative(g,y,Z)Gram determinant removes the square term. Addingρaaᵀ contributesρdetA·u with0≤u≤q, even when the projected compression is singular. The full-size endpoint gives the exact determinant.

## Normalization and product endpoint

The run givesβ=t/d≥1−c2, ||y||≤2G andα=d/q. Weighted adjacent degrees boundqVnext≤2ηV. The product bound usesm−1updates and the q≤G²V inequality at the last endpoint; it does not require any positive lower spectral bound.

## Weaker assumption preserved

Only d_k→0 is used in the reciprocal theorem. Summability is derived later on compact sublevels, not substituted into the weaker statement. GM divergence implies arithmetic mean of reciprocals divergence, not pointwise q_k→0.

## Reference energy

Mksk=0 removes both reference-point step cross terms. Convexity suppliesg·r≥gap; summation uses finalgapmonotonicity and nonnegativeenergy, not an energyupperbound assumed in advance.

## Transported energy

Projected PSD order can be paired withMk by trace monotonicity. Dividing byP_{k+1} subtractsm/(qP_k); 1≤P_k≤exp(LΣd) gives the stated reciprocal-sum bound. A compact cluster argument separately derives solution-set distance and unique-minimizer whole-iterate convergence.

## Definitions expanded rather than only theorem names

Read FullBFGSRun, ReciprocalGrowthTarget, TransportedCertificateTarget and AdmissibleBFGSRun. Pure matrix SPD/curvature invariants in FullBFGSRun are derived when passing from objective-level admissible runs; no recurrence or favorable limit is inserted.

The preceding article-geometry audit used a less explicit structural traversal. A fresh replay now uses the full type/value/constructor/mutual-inductive/recursor-rule traversal used by newer supplements, checks kernel type and value agreement, and compares ordinary axiom collectors per root. All14unchanged mathematical declarations compiled; their exact types and axioms agree with the prior audit. The closure is still26,496declarations with only propext, Classical.choice and Quot.sound. The former audit was not found to have omitted any dependency in this case; the new record makes the stronger check explicit.
