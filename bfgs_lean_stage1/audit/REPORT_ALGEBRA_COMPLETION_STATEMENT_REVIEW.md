# Fifteenth milestone: general projection and source conclusions

This tranche adds 51 library modules and 27 exact targets. Its four scoped gates
report 385 declarations (including three structure declarations), actual types,
transitive axioms and strict target equalities. The central gate covers 633 frozen
Lean files and 205 exact targets. Completion is determined by
`report_algebra_completion_check.log` and `STATUS.json`, not this review text.
Every adopted proof body was compared with its independently reviewed source;
only import qualification changed. All original research sources are preserved.

## General semialgebraic projection is proved

The actual distinct-root Tarski sum equals the actual rational Cauchy index of
the weighted logarithmic derivative. The proof handles arbitrary multiplicities,
common roots, removable singularities, odd/even poles and zero polynomials. Local
reciprocity is summed over the actual union of roots; a proved finite-jump
telescoping identity supplies the signs at infinity. Actual Euclidean remainder
recursion computes the index with a proved degree-based fuel bound. Positive
pseudo-division preserves this index through an even power of the actual leading
coefficient; the zero-leading-coefficient branch lowers symbolic degree.

Finite sign determination reconstructs simultaneous sign-pattern counts as a
rational combination of actual Tarski sums. Every atom shares the same root
witness. Actual roots of the product of the nonzero factors, roots of its
derivative, and two explicit tail samples realize every real sign pattern.
Empty families, identically zero factors, constants, repeated roots and vanishing
derivatives have explicit branches.

These results prove semialgebraicity of actual parameterized index/query fibers.
One finite family of polynomial tests is chosen before specialization. Boolean
projection preserves a single common scalar witness under conjunction and
negation. Induction over finite coordinate types then proves
`RealAlgebraicGeometry.coordinate_projection_semialgebraic` in arbitrary finite
dimension. `IsSemialgebraic` still means representability by a quantifier-free
polynomial formula; projection or decomposition is not a field of its definition.
No sign oracle, assumed elimination theorem or unchecked computation is used.

Independent evidence is in the ROOT_SIGNS, RATIONAL_INDEX, POSITIVE_INDEX,
SIGN_DETERMINATION, POLYNOMIAL_SAMPLING and GENERAL_PROJECTION statement/peer
reviews and their actual compiler/axiom/contract logs. The delivered-only scoped
validator is `scripts/verify_report_sign_query_scoped.py`.

## Actual supporting and affine-critical graphs

General projection discharges the previously explicit projection premise in the
supporting-plane graph theorem. The new witness construction uses actual global
supports and signed affine weights summing to one, with weighted vector sum zero.
The actual bounded affine representation theorem reduces this to at most n+1
supports. The finite union of actual projections is exactly the affine-critical
set; the objective graph restriction is exactly its lifted critical graph.
Zero-dimensional and empty-witness cases are included. Definability itself needs
only semialgebraicity of the objective; convexity is used later in the path
constancy argument. The AFFINE_CRITICAL_DEFINABILITY peer independently checked
the source statements, definitions and all transitive dependencies.

Finite smooth path covers, finite critical values, the low-level affine-critical
gap and C's dependent semialgebraic alternative are still open at this milestone.
The existing finite-path-cover and finite-value implications remain conditional.
Compilation of those implications does not discharge the missing premises.

## H cardinality sharpness and I ridge supersession

`SeedOrbit.sharpRecurrentCardinality` uses the actual identity-initialized
three-phase full-BFGS seed run for every original admissible pair of line-search
constants. Each of the three distinct actual gradients recurs arbitrarily late.
Their actual span is the whole plane, so the actual recurrent cardinality is
3 = rank + 1. The run has positive objective values tending to zero and iterates
tending to a nonstationary zero. This closes H89–116 and H410–415's concrete
sharpness cross-reference. Together with the separately audited attributed
two-piece termination theorem, H has no remaining asserted mathematical claim.
The explicitly open higher-rank zero-value behavior is not a theorem target.

`RidgeSupersession.ridgeSupersession` proves I165–176 for the literal two-branch
objective max(a(u)+pv,b(u)-qv), p,q>0. It derives strict profile convexity across
the exceptional minimizer, strict positive contours, the actual gradient
determinant and affine-critical correctness, then applies the actual planar
convergence theorem. The basin is chosen before every actual run, initial SPD
matrix and allowed constants. The source coercivity assumption is unnecessary:
finite convexity plus the unique attained minimizer already gives compact
sublevels. This is a strengthening proved from the remaining source hypotheses,
not an additional premise. See the H_SHARP_CARDINALITY and RIDGE_SUPERSESSION
independent reviews and the complete I source reconciliation.

## D displays, original-box positivity and literal Euclidean locality

The D supplement encloses 33 actual quantities: the contraction factor, accepted
points, all nine trial objective values, start values, accepted ratios and scalar
construction constants. Actual cycle identities connect the formulas with the
unmodified full-BFGS run. All original displayed approximations have error less
than one displayed decimal unit. Five are not nearest roundings; their corrected
values, with error less than half a unit, are:

| Source | Quantity | Original | Correct nearest rounding |
|---|---|---|---|
| D141 | Final accepted point, second coordinate | -0.004954238006 | -0.004954238005 |
| D206 | Final Armijo ratio | 0.375205963572 | 0.375205963573 |
| D206 | Final Wolfe ratio | -0.817119670486 | -0.817119670485 |
| D333 | Second scalar center | 0.468627450981 | 0.468627450980 |
| D334 | Lower plateau length | 0.635765118558 | 0.635765118557 |

The actual whole original root box, without root equations, has positive definite
three phase metrics, positive actual update energies and curvatures, and a
positive definite final updated metric. The final curvature exceeds 1/100.
The exact Euclidean bound in D448 uses the maximum norm of the nine actual trial
points, including a proof that it bounds the initial point. It controls every
accepted and queried point of every embedded copy and tends to zero.

The generators only produce ordinary Lean proof terms; their output is compiled
and byte-identically regenerated. D_SOURCE_SUPPLEMENT records the independent
97-declaration/three-target review. D_SOURCE_MAP covers all 453 original source
lines in 57 groups. Four groups still await separately audited literal exports
for the non-strict interpreter, polynomial equivalence and finite convex/affine
identities; they are not silently closed by prose consequence reasoning.

## Reproduction and remaining scope

The pinned whole-project build and whole-environment audit include generated
theorems as well as explicit source declarations. Only propext, Classical.choice
and Quot.sound are allowed. The startup Python metadata error occurred before
any Lean process; its repair and unchanged frozen Lean hashes are recorded in
`report_algebra_completion_startup_error.log`. The successful central command is
not a substitute for the actual type and definition review above.

The entire report remains incomplete: A's finite path/component/value closure
and its C consequence, D's final literal wrappers and final source reconciliation
remain active. The historical 19-job run and the older R four-piece attribution
lack recoverable original inputs. Current theorem proofs do not certify those
historical execution facts. See HISTORICAL_EVIDENCE_RECONCILIATION.md.
