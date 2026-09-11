# Full BFGS research report: Lean verification

**Module M and the primary transported-certificate, homogeneous-value,
scalar-convergence, and radial-certificate theorems are compiler-checked.**
The entire report is still in progress. The execution plan is
[ENTIRE_REPORT_PLAN.md](ENTIRE_REPORT_PLAN.md); the source coverage and remaining
claims are in [audit/REPORT_STATUS.json](audit/REPORT_STATUS.json).

The pinned Lean 4.19.0 build and transitive axiom audit checked all 1,445 explicit
theorems and 2,014 theorem declarations including generated auxiliaries. All 61
registered exact targets passed. Only `propext`, `Classical.choice`, and
`Quot.sound` occur; no placeholders or unchecked mathematical computations are
used. Current logs are `audit/build.log`, `audit/axioms.log`, and
`audit/report_structures_check.log`.

The original research sources are unchanged. The pre-work draft and report were
committed and pushed as `2c8bb60`. Historical environment-failure logs describe the
previous runtime, not the current proof status.

## Results and exact scope

| Export | Verified conclusion |
|---|---|
| `principalMinorHierarchy` | Inhabits the unchanged `PrincipalMinorHierarchyTarget`: actual full inverse-BFGS matrices, actual sums of principal determinants, arbitrary finite dimension |
| `fullBFGS_normalizedHierarchy` | Derives the scalar hierarchy from those matrices, with `K=4G²/c²`, `C=G²`, and `δ=d/c` |
| `reciprocalGrowth` | Inhabits the unchanged `ReciprocalGrowthTarget`: geometric and arithmetic reciprocal means diverge when predicted decreases tend to zero |
| `finiteHorizon` | The source's explicit real-power finite-horizon lower bound, including the actual tail budget and matrix potential |
| `superquadraticReciprocalGrowth` | Inhabits the unchanged `SuperquadraticReciprocalTarget`: reciprocal sums divided by `N²` tend to infinity under summability |
| `objectiveReciprocalGrowth` | Reciprocal means diverge for actual finite-convex-objective runs with bounded gradients and vanishing predicted decreases |
| `objectiveLowerBoundGrowth` | Armijo derives summability from lower-bounded values along the run; bounded gradients then give both mean divergences and superquadratic reciprocal sums |
| `compactObjectiveGrowth` | Initial-sublevel compactness supplies the gradient and value bounds, so summability and all three growth conclusions follow |
| `objectiveFiniteHorizon_of_lower_bound`, `compactObjectiveFiniteHorizon` | The exact finite-horizon bound for objective runs, with actual principal determinants and predicted-decrease tail sums |
| `hessianInvariants` | Actual Hessian update, PSD annihilated part, step annihilation, and exact determinant update |
| `localization`, `strictContourSteps` | Compact sublevels and local basins at a unique attained minimizer; vanishing accepted steps on a positive strict contour |
| `referenceEnergy` | Exact fixed-reference energy identity and finite objective-gap bound |
| `quadraticCorrectionConvergence` | Value and iterate convergence at a unique minimizer under the explicit quadratic cumulative-correction budget |
| `movingFrameCriterion` | Excludes exact frame certificates with bounded cumulative transports and inverse transports, using only vanishing predicted decreases |
| `residualFrameCriterion` | Excludes imperfect frame certificates in a fixed smooth subspace, deriving the subspace Hessian budget from the actual update |

New exact exports are `transportedCertificateConvergence` (T primary theorem,
including actual Euclidean distance to the full solution set),
`homogeneousDichotomy` (H.A without bounded iterates),
`scalarMetricConvergence` (G with arbitrary positive scalar metrics),
`scalarBFGSConvergence` (actual dimension-one specialization), and
`radialCertificateConvergence` (RS sufficient condition). Their statement review
is [audit/REPORT_CORE_STATEMENT_REVIEW.md](audit/REPORT_CORE_STATEMENT_REVIEW.md).
The second tranche checks normalization and variants in T/G, H.B recurrent
affine geometry, incoming-jump obstruction and scalar characterization in G,
and R supporting-intercept equivalence and inward sufficiency. See
[audit/REPORT_GEOMETRY_STATEMENT_REVIEW.md](audit/REPORT_GEOMETRY_STATEMENT_REVIEW.md).
The third tranche proves full same-sublevel RS/IR equivalence, local derivative-free
central equivalence, actual affine lifting, nonunique solution basins, finite and
asymptotic rate statements, both scalar nonnecessity examples, individual pair
realizability, and finite-sample feasibility. See
[audit/REPORT_CONTINUATION_STATEMENT_REVIEW.md](audit/REPORT_CONTINUATION_STATEMENT_REVIEW.md).
The fifth tranche proves the original-family Q certificate and convergence,
its explicit radial-secant separation, F transformed gauges including the inverse
derivative formulas, H.8 relative-interior convergence and metric fibers, and an
actual-objective correction to G.4. See
[audit/REPORT_FAMILIES_STATEMENT_REVIEW.md](audit/REPORT_FAMILIES_STATEMENT_REVIEW.md).
The sixth tranche closes Q's literal pruning/printed-scale claims and H's internal
low-rank/class theorems, and verifies the max-affine threshold, mixed gauge powers,
finite polyhedral/PLQ basins and the actual five-piece finite line-search obstruction.
See [audit/REPORT_STRUCTURES_STATEMENT_REVIEW.md](audit/REPORT_STRUCTURES_STATEMENT_REVIEW.md).
A barycentric geometry is audited with its objective application still explicitly
conditional in this release. Remaining F/R concrete applications, C/U/A, D/L,
source cross-references and synthesis remain open.

The original matrix growth results use `FullBFGSRun`, the algebraic specification
of the unmodified full matrix update, with bounded gradients and a positive fixed
lower bound on beta. The accepted-step weak-Wolfe inequality implies this beta
bound by `FullBFGSRun.beta_ge_of_weakWolfe`. The growth assumptions are vanishing
or summable predicted decreases, respectively. No iterate/matrix convergence or
uniform matrix bound is assumed. No L-BFGS or update modification occurs.

`AdmissibleBFGSRun` now specifies a finite convex objective, actual derivatives at
accepted iterates, positive lengths, nonzero accepted gradients, Armijo and weak
Wolfe, the unmodified full inverse-BFGS update, and **only initial** positive
definiteness. Positive definiteness and curvature at every later step are proved.
Compact-sublevel exports derive their gradient and budget bounds; the more general
exports retain their stated gradient/value bounds. No smoothness away from accepted
iterates or continuity of gradients is assumed.

The energy and frame results are **trajectory criteria**. The transported and radial objective conditions now derive their actual trace or
correction bounds. The remaining specific objective families and geometric
certificate constructions are tracked separately in the report register. No unconditional convergence for
arbitrary finite convex nonsmooth objectives or universal step-existence theorem
is claimed. See
[MATHEMATICAL_REVIEW.md](MATHEMATICAL_REVIEW.md) and
[audit/STATEMENT_REVIEW.md](audit/STATEMENT_REVIEW.md) and
[audit/OBJECTIVE_STATEMENT_REVIEW.md](audit/OBJECTIVE_STATEMENT_REVIEW.md) for the
earlier statement reviews, and
[audit/FOUNDATION_STATEMENT_REVIEW.md](audit/FOUNDATION_STATEMENT_REVIEW.md) for the
localization, energy, and frame review.

Squared norms in the matrix estimates are Euclidean sums of squares.
`FrameNorms` verifies both the Euclidean operator-norm interpretation and the
orthonormal matrix representation of every subspace. Generic localization holds
in any finite-dimensional real normed space, including Euclidean space; displayed
`Metric.ball` corollaries on `Vec n` use its default Pi norm at that radius.

## Reproduce

Pinned versions are unchanged:

- Lean: `leanprover/lean4:v4.19.0`
- mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`
- Transitive package revisions: generated and committed `lake-manifest.json`.

With Elan/Lake available:

```bash
cd bfgs_lean_stage1
bash scripts/bootstrap.sh
```

The current workspace keeps Elan in `.toolchain/elan`, dependencies and compiled
objects in `.lake`, and downloaded caches in `.cache`, all inside this repository
and ignored by Git. `bootstrap.sh` and `check.py` discover the local installation.
To install Elan locally in a fresh checkout:

```bash
mkdir -p .toolchain/elan
curl --proto '=https' --tlsv1.2 -sSfL \
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  -o .toolchain/elan-init.sh
ELAN_HOME="$PWD/.toolchain/elan" bash .toolchain/elan-init.sh \
  -y --no-modify-path --default-toolchain none
bash scripts/bootstrap.sh
```

On this macOS runtime the pinned native mathlib cache utility failed to load with
`__DATA_CONST segment missing SG_READ_ONLY flag`. Bootstrap disables the native
cache post-update hook and runs the **same pinned cache program** with
`lake env lean --run`. This concerns download tooling, not proof trust. No
toolchain or mathlib revision was changed.

For subsequent checks:

```bash
python3 scripts/check.py
```

After the audit output log has closed and intended delivery files have been
staged in Git, `python3 scripts/manifest.py` regenerates their artifact hashes in
`MANIFEST.json`. Untracked local notes are excluded from the delivery manifest.

`--static-only` is explicitly **not** Lean verification. The default checker
verifies the compiler, every locked dependency revision and clean tracked
dependency checkouts, builds the library, enumerates the
compiled environment, checks every explicit source theorem has an axiom report,
and rejects unexpected transitive axioms. `Audit.lean` additionally requires
terms of the exact original and objective-level targets and prints their definitions and full key
signatures. Verification is not inferred from names or compilation alone.

## Evidence and organization

- [audit/STATUS.json](audit/STATUS.json): actual status, source hashes, every
  explicit theorem's signature/dependencies, conditional reusable stages, and
  remaining target obligations.
- [audit/build.log](audit/build.log), [audit/axioms.log](audit/axioms.log): current
  compiler and complete axiom/type audit transcripts.
- [audit/lean_version.log](audit/lean_version.log),
  [audit/mathlib_revision.log](audit/mathlib_revision.log): actual pinned versions.
- [audit/dependencies.log](audit/dependencies.log): all locked dependency
  revisions and tracked worktree checks.
- [audit/declarations.json](audit/declarations.json): all audited theorem records.
- [PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md): source-to-proof completion map.
- [audit/HISTORY.md](audit/HISTORY.md): historical versus current evidence.

The matrix chain runs through `PrincipalMinors`, `GramSchur`,
`CompressionDeterminant`, `BFGSUpdate`, `BFGSCompression`, `PrincipalInvariance`,
`PrincipalCombinatorics`, `CoordinateGram`, `OrthogonalCoordinates`, and
`PrincipalHierarchy`. `Normalization` connects this to `ScalarHierarchy`,
`ReciprocalGrowth`, and `QuantitativeGrowth`. `EndToEnd` exports the complete
matrix-run results. Conditional helper premises are discharged in `EndToEnd`.
`PositiveUpdate`, `ConvexAnalysis`, and `DescentBudget` supply the new invariants
and objective consequences. `ObjectiveRun` constructs the actual matrix run;
`ObjectiveEndToEnd` exports the objective-level growth results against the explicit
propositions in `ObjectiveTargets`.
`HessianUpdate`, `ObjectiveEnergy`, and `EnergyBudget` establish the fixed-reference
chain. `Localization`, `StrictContours`, and `LocalizationCorollaries` establish
the geometric consequences. `MovingFrame` handles exact transport;
`SmoothSubspace`, `FrameBounds`, `ResidualBudget`, `ResidualFrames`, and
`ResidualSourceForm` handle imperfect transport. `FoundationEndToEnd` inhabits the
seven explicit additional propositions in `FoundationTargets`.

## Fourth report milestone

The full audit now includes centered smooth-plus-sublinear convergence and
recentring, the actual quadratic-plus-gauge logarithmic rates, invertible affine
certificate covariance, G's ellipsoid/range and exact pointwise-capacity geometry,
the main planar H.C dichotomy, and Q's arbitrary-finite-family foundation through
the uniform nonzero denominator theorem. See
[audit/REPORT_APPLICATIONS_STATEMENT_REVIEW.md](audit/REPORT_APPLICATIONS_STATEMENT_REVIEW.md).

G's accessible-jump discussion required an explicit qualification: accessible
jumps need not span all active-gradient differences. The corrected accessible
projection implication and a limited algebraic countermodel are proved; the
original unqualified inference is not marked verified. The source is unchanged.
Q's calibrated transport and full convergence theorem remain open, as do the
other obligations in the report register.
