# Results selection and scope guardrails

Source basis: corrected `latex.zip`, dated 11 September 2026. This is an editorial map. It does not replace exact theorem statements or prove novelty. The current repository may supersede these source locations. Use the generated archive label index to locate statements, then complete the formal claim ledger from actual exports.

## Retain by logical role

| ID | Result / component | Default placement | Why it remains |
|---|---|---|---|
| CORE-M | Actual principal-minor hierarchy and normalized BFGS bridge | Article, complete proof or article appendix | Common positive foundation; not merely a scalar hypothesis |
| CORE-GROWTH | Reciprocal means, finite-horizon bound, superquadratic reciprocal sum | Needed asymptotic theorem in article; complete family in companion | Hypotheses and finite/asymptotic conclusions differ |
| CORE-ENERGY | Reference energy, transported certificate, normalization | Article | General sufficient mechanism |
| CORE-RADIAL | RS equivalence with inward modeling control | Article | Human-readable route to familiar objective classes |
| CORE-PARTITION | Local finite polyhedral partitions with smooth cell extensions | Article headline | Clean positive contrast with finite smooth branch formulas |
| CORE-COMPOSITE | Smooth-plus-centered-sublinear and selected residual/powered-gauge corollaries | Article examples; complete companion development | Nonpolyhedral coverage and recognizable applications |
| GEO-PLANAR | Planar affine-critical cluster and local nondegenerate smooth maxima | Preferred article extension, with complete proof | Curved switching geometry beyond RS; dimension restriction essential |
| GEO-FIXEDNORMAL | Arbitrary-dimensional fixed/parallel normal interfaces; weaker tangential-curvature variant | Article if proof budget permits; otherwise companion theorem | Not planar reduction; tolerates rough normal curvature |
| GEO-PARABOLIC | Finite max of a_i u^2+b_i v with arbitrary branch count and allowed b_i=0 | Companion, article summary as appropriate | Flat contours make it incomparable with strict-contour theorem |
| N-UPPER | Deterministic local failure with globally C^{2,1} convex branches | Article headline with complete argument | Fixed algorithm and one objective; bad starts accumulate at optimizer |
| N-LOWER | Positive-lower-curvature local failure with C^{1,1} branches, plus literal-Hessian variant | Article separate theorem if fully developed; always companion | Lower curvature is gained at a different differentiability level |
| N-GLOBAL | Coercive finite polyhedral failure; strongly convex quadratic-branch failure | Article corollaries; detailed companion | Simpler objective classes, different local/global conclusions |
| HOMOGENEOUS | Unconditional degree-one value dichotomy; low-rank/fiber refinements | Bounded-below/coercive application may be article; full companion | Noncompact/unbounded-below statements not subsumed by compact certificates |
| SCALAR | One-dimensional convergence independent of BFGS update | Companion or concise contrast | Covers local certificate failure despite actual convergence |
| CERT-GEOMETRY | Normalization, pointwise feasibility, accessible-jump obstruction, nonnecessity | One warning in article; complete companion | Separates failure of proof condition from failure of algorithm |
| AFFINE-GEOMETRY | Equal-rate descent, rank stability, semialgebraic affine-critical gap | Article when used; full companion with attribution | Geometric bridge, not a blanket semialgebraic BFGS theorem |
| LIFT-RATE | Initialization-dependent affine-fiber selector and conservative rates | Companion; concise article corollaries if useful | Special nonunique/noncompact conclusions and quantitative information |

“No article placement” never means “delete the result.” It means it is not an independently claimed contribution of the focused article. Preserve it in the complete companion, and label pointers from the article accurately.

## The counterexample table must not be collapsed

### N-UPPER

The corrected record states local failure for one fixed finite convex maximum of four globally C^{2,1} convex branches with upper Hessian bounds. A unique nonsmooth minimizer, compact sublevels, identity initialization, deterministic unit-first weak-Wolfe bracketing, strict accepted/rejected decisions, and all-trial containment are part of the claimed construction. A uniform positive lower curvature bound is not.

### N-LOWER

The local finite-branch version has uniform strong convexity and Lipschitz gradients, but branches are C^{1,1}, not twice differentiable at the accumulation point. A second variant has one constant positive-definite classical Hessian wherever it exists but a countable nonsmooth description. A common initial SPD matrix is converted to identity by one fixed affine change. Stable-manifold existence, not rounded forward shooting, supplies the perturbed seed.

### N-GLOBAL

A maximum of affine pieces can fail globally even though local finite-polyhedral convergence holds. Adding a common positive quadratic gives a global strongly convex example with constant branch Hessians. Its wrong vertex is not its minimizer. It does not refute the local theorem at that minimizer.

Do not infer local failure for finitely many uniformly strongly convex C^2 branches from these statements. Do not infer a positive-measure failure set, robustness to floating-point perturbations, or failure of every weak/strong-Wolfe implementation.

## Actual supersessions already recorded

- Older externally prescribed admissible-length seeds are not independent principal results once the canonical deterministic seed supplies the corresponding conclusion. Keep original versions only as provenance when available.
- The older two-branch scalar-ridge convergence result is recorded as a consequence of the planar theorem under the original profile assumptions. Preserve the existing implication proof; do not count it as another main contribution.
- RS is an interpretable specialization of the transported certificate, but its equivalence and verifiable classes remain useful exposition.
- The superquadratic reciprocal sum supersedes earlier asymptotic lower-bound headlines **under summability**, not the weaker-assumption theorem or explicit finite-horizon bound.
- Simple examples such as u^2+|v| and the two-quadratic curved ridge are illustrations, not multiple separate main contributions.

A new deletion needs an implication proof specifying assumptions, conclusion, dimension, locality, algorithm, and quantifier differences. Similar-looking statements are not enough.

## Non-implications to make visible

1. Pointwise Hessian bounds off nonsmooth sets are not a global Lipschitz-gradient assertion.
2. A finite maximum of quadratics is not automatically PLQ on finitely many polyhedral cells.
3. Compactness plus objective convergence gives distance-to-solution convergence; unique minimization or a separate result is needed for whole-sequence convergence.
4. An affine-critical cluster point need not be stationary; no-false-affine-criticality is a separate assumption/consequence under specified geometry.
5. Local no-false-affine-criticality for tame functions does not prove that BFGS must reach that geometry.
6. A planar theorem is not an arbitrary-dimensional theorem; fixed normals are not rotating normals.
7. A Lipschitz comparison field does not by itself control its energy in an unbounded B_k metric.
8. Certificate nonexistence is not an actual bad BFGS trajectory. Accessible jumps and all active jumps are different objects.
9. Existence of an acceptable differentiable length is not finite termination of every implementation.
10. Formal verification of a correct contract does not certify publication priority or human-language contract correspondence.

## Corrections that must survive rewriting

Use the latest corrected source and actual formal proofs for:

- Constant/linear intercept terms in radial supporting-plane identities and the assumptions allowing simplification.
- Signed planar determinant orientation and its right-derivative comparison proof.
- C^1 regularity of fields derived from C^2 branch gradients; a smooth partition does not improve input regularity.
- Domain exclusions at affine-critical points for common-rate pairings.
- Nonzero-coupling qualifications for claims of nonsplitting, distinct from the convergence theorem itself.
- Exact Armijo eligibility ranges and non-strict boundaries of printed examples.
- Rational enclosures versus rounded decimal displays.
- Withdrawal of historical verifier execution claims not supported by actual evidence.

## Suggested theorem contracts ledger

Use `templates/claim_ledger.csv` as a starting register. Each row needs:

- The actual corrected statement (or a stable source locator).
- Every essential hypothesis and quantifier, and whether it is derived or assumed.
- Article/companion location and logical role.
- All formal declarations needed, not just the sample export shown in a chapter table.
- Any proof substitution, specialization, or change of notation and its correspondence justification.
- Attribution class and cited primary source where applicable.
- Status and audit/build evidence tied to a Git commit.

Do not assign `verified` because a row exists in this template. Initial rows are deliberately marked `requires_repo_contract_review`.
