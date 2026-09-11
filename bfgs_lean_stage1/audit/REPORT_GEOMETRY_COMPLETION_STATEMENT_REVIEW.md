# Fourteenth milestone: constant-rank geometry, precision and polynomial infrastructure

This release comprises39 new library modules,234 explicit declarations plus17 structure constructors/projections in the scoped reports, and16 new exact proposition targets. The central frozen source inventory contains582 Lean files; the project has178 registered exact targets. The full release gate is `audit/report_geometry_completion_check.log`, with `STATUS.json`, actual compiled-environment inventory, compiler/axiom logs and `report_geometry_completion_source_hashes.json`. The gate, rather than this review text, determines completed verification status.

All original research files are preserved. Module M's actual full-BFGS matrix theorem and objective bridge remain unchanged. All new mathematical proofs are kernel checked with the pinned toolchain; actual transitive dependencies are audited, including generated theorem declarations. Scoped proof-body comparisons show only owned import names changed when reviewed scratch files were copied into the delivered library. Reproduction requires the delivered files and pinned dependencies; scratch artifacts are not release inputs.

## Actual arbitrary-dimensional constant-rank field in C

Twelve modules derive the actual canonical minimum-norm affine point from the actual active gradient family. The gradient-difference matrix has its literal rank, identified with affine direction dimension. A genuine finite affine basis is selected; actual nonzero Gram determinant plus local constant rank derive persistence of its span. Differentiation of the actual inverse-Gram formula proves regularity. No desired field or smooth selection is a premise.

A buffered finite partition constructs one globally C1 field, a compact buffer surrounding an open neighborhood of the given compact non-affine-critical set, and a uniform field norm bound. That same field pairs to one with every actual subgradient. Original inactive branches are excluded by continuity; every chart contributing at the later endpoint also contains every sufficiently close earlier endpoint. Actual one-sided convex smooth estimates, a proved feasible local descent test and actual finite-max supporting gaps yield the uniform secant correction. Constants precede all endpoint pairs. The eligible-pair version derives positive curvature from weak Wolfe. Affine independence is proved sufficient for the literal rank condition.

C2 branch hypotheses guarantee C1 field regularity. The source's word smooth must be qualified; C-infinity is not asserted. This is recorded in the correction ledger. No arbitrary-dimensional projected transport or BFGS convergence theorem follows from this partial construction, as the source itself warns. The previously proved actual spatial counterexample remains in force.

Evidence: [statement review](C_CONSTANT_RANK_STATEMENT_REVIEW.md), [independent review](C_CONSTANT_RANK_INDEPENDENT_PEER_REVIEW.md), `verify_c_constant_rank.sh`, `c_constant_rank_declarations.json`. The scoped report has52 explicit declarations and17 generated structure declarations,69 actual types/transitive-axiom reports, and four strict source/wrapper checks for two targets.

## L numerical precision and full source reconciliation

Two modules certify the actual shape-map Frechet derivative at the actual unique algebraic seed. Kernel interval arithmetic encloses its four entries within5e-21 of specified twenty-decimal rational centers. All original displayed15-decimal approximations have error<1e-15. The original lower-left value is more than0.5e-15 above the actual entry, so its nearest15-decimal rounding should end427498, not427499. The source is preserved and the correction is explicit.

The generated interval proof is ordinary Lean arithmetic. The Python generator proposes terms; it is not an unchecked computation used as a theorem premise. Byte-identical regeneration and a fresh main compiler/axiom/contract gate passed. The complete368-line source map, in50 disjoint groups, connects the existing actual global/local identity-initialized failures, complete deterministic queries, scalar/objective geometry and actual invariant stable manifold with the newly certified precision display. The expressly unclaimed combination of globallyC2 branches and uniform lower curvature remains unclaimed.

Evidence: [complete L source map](L_SOURCE_MAP.md), [precision review](L_SHAPE_PRECISION_STATEMENT_REVIEW.md), [independent review](L_SHAPE_PRECISION_PEER_REVIEW.md), `verify_l_shape_precision.sh`. Two sources,16 actual declaration reports and one exact target.

## Literal two-piece finite termination and linear-image scope

Nine modules prove the attributed two-piece conclusion through actual unmodified inverse BFGS. The objective is|x0|+x1; actual derivatives force gradients(±1,1), actual positive curvature forces alternation, and the actual matrix update derives the scalar relations. The positive scalar potential B*X/D loses more than c1 whenever two further accepted transitions exist. A finite telescoping argument excludes an infinite actual run. The lookahead is used explicitly; no future-step inequality is silently assumed at the present state.

The actual reverse transition relation is well-founded. Every differentiable SPD initial state has a finite path to a terminal state. If its actual search ray had nonnegative asymptotic slope, the proved finite-bad-ray Armijo–weak-Wolfe existence theorem would give a successor. Thus the terminal ray tends to minus infinity. This proves a finite mathematical transition-path result, not finite oracle complexity for an unspecified implementation.

A separate actual full-row-rank projection theorem excludes infinite admissible runs for arbitrary finite-dimensional linear images and for|u·x|+v·x with linearly independent rowsu,v. It projects actual full matrices and derivatives; no off-plane metric data are discarded. The detailed terminal-ray target is the literal two-dimensional model; the arbitrary-dimensional target is no infinite continuation. No finite-termination claim is made for the general many-piece family.

This is a formal verification of the pre-existing background result attributed to Xie–Wächter, not a new research claim. The proof was checked against the primary paper, [arXiv1712.08571](https://arxiv.org/abs/1712.08571), and the report's H403–408 wording.

Evidence: [statement review](TWO_PIECE_TERMINATION_STATEMENT_REVIEW.md), [independent review](TWO_PIECE_TERMINATION_INDEPENDENT_REVIEW.md), `verify_two_piece.sh`, `two_piece_declarations.json`. Nine sources,68 actual declaration reports and two exact targets.

## A: stronger polynomial infrastructure, with general elimination still open

The five multiplicity modules prove actual specialized fiber degree bounds, semialgebraic zero-fiber/exact-degree strata, actual derivative specialization and a finite root-multiplicity partition, including identically zero fibers. Each nonzero-fiber root of multiplicitym lies on the actual local simple-root chart for the(m-1)st derivative. That chart contains the multiplicity stratum; it is not claimed to parameterize original polynomial roots throughout a whole parameter neighborhood.

The five quadratic modules eliminate actual degree-at-most-two single polynomial root/strict-sign/weak-sign conditions with all degree drops and discriminant cases. Both existential and complementary universal formulations are actual semialgebraic sets. Arbitrary Boolean combinations of multiple quadratic atoms and general polynomial projection are not inferred.

The six positive pseudo-division modules prove the literal arbitrary-degree polynomial identity with an even power of the leading coefficient, actual specialization and preservation of signs at divisor roots. Zero-leading-coefficient branches preserve specialization and decrease symbolic degree. One finite family of lower-degree remainders is chosen before all parameter specializations, covering every nonzero specialized divisor including degree drops. No sign-determination, global projection or path-decomposition oracle is assumed or exported as proved.

Evidence: `verify_a_polynomial_multiplicity.sh`(5 sources/39 declarations/4 targets), `verify_a_quadratic_projection.sh`(5/33/4), `verify_a_polynomial_pseudodivision.sh`(6/26/3), their declaration manifests and `A_*_VERIFICATION.md`/`A_*_PEER_REVIEW.md` reports. Every scoped actual type/dependency and strict target gate passed independently before the central freeze.

## Remaining report scope

The entire report is not yet verified. General nonlinear Boolean semialgebraic elimination, finite smooth-path decomposition and the actual affine-critical finite-value application remain required; C's semialgebraic alternative depends on them. The final numerical-display and source/synthesis/evidence reconciliation remains active. The historical old four-piece numerical attribution in R is unsupported by a recoverable objective; its current-model correction is proved and distinctly recorded. Historical claims about absent original verification scripts are not treated as Lean-verified facts. Later scratch work is excluded from this frozen release.
