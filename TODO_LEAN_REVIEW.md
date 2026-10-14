# TODO: Lean formalization review

Review date: 13 October 2026. Reviewer: AI assistant (Claude), at the author's request.

Scope: check that the Lean statements match the article's statements (`paper/`), and
look for misuse of Lean (proof holes, extra axioms, kernel bypasses, vacuous or
mis-specified definitions). Proofs were **not** read line by line, and the Lean
was **not** compiled here (no Lean toolchain on this machine). The companion's
other results were not reviewed.

## Summary

- No Lean misuse found. A static scan of `bfgs_lean_stage1/BfgsVerification/`
  (735 files) and the five article supplements under `editorial/` found:
  no `sorry`/`admit`, no `axiom` declarations, no `native_decide`,
  `ofReduceBool`, `implemented_by`, `@[extern]`, `unsafe`, `opaque`,
  `#eval`/`run_cmd`, no custom `instance`s and no custom syntax/macros
  (one harmless `local notation`). Only `maxHeartbeats`/`maxRecDepth` options.
  (The single grep hit for "admit" is English prose in a doc comment,
  `PlanarRunTransport.lean:47`.)
- The core definitions are faithful to the paper: `AdmissibleBFGSRun`,
  `inverseBFGS`/`bfgsStep`, the bracketing line search, `coordinateGradient`
  (actual Fréchet derivative), `subdifferential` (global supporting inequality),
  `IsAffineCritical` (0 ∈ aff ∂F), `ConvexTwoBranchRegularAt`,
  `RadialHessian.matrix` (derivative of the derivative), `BandCertificate`,
  `HasRadialSecantBounds`, `HasInwardTaylorBounds`, `polyhedron`, both scalar
  interpolations, and the seed polynomial and its rational centre (exact match).
- Every one of the article's main theorem/lemma/corollary statements that I
  checked has a matching Lean statement; several Lean versions are more general.
  The gaps are listed below.

## Open items

### P1: verification

- [ ] **Independent clean build and axiom check.** The repository's own records
  say that the main library and Mathlib were never rebuilt from an empty cache.
  The "PASS" evidence is AI-produced logs. On a clean machine:
  1. Install `elan`, then `cd bfgs_lean_stage1 && lake exe cache get && lake build`.
  2. Compile the article supplements, which `lake build` does **not** cover
     (see the P3 item below).
  3. Run `#print axioms` on at least these exports and confirm only `propext`,
     `Classical.choice` and `Quot.sound` appear:
     `BfgsVerification.principalMinorHierarchy`,
     `BfgsVerification.reciprocalGrowth`,
     `BfgsVerification.transportedCertificateConvergence`,
     `BfgsVerification.inwardCertificateConvergence`,
     `BfgsVerification.AdmissibleBFGSRun.centered_iterates`,
     `ArticlePositive.mixed_benchmark_global`,
     `BfgsVerification.AdmissibleBFGSRun.homogeneous_coercive_iterates_zero`,
     `BfgsVerification.ConvexCellRadial.finite_polyhedral_basin`,
     `BfgsVerification.AdmissibleBFGSRun.planar_affineCritical_cluster_on_sublevel`,
     `BfgsVerification.PlanarMaxRegular.finite_max_local_basin`,
     `BfgsVerification.PlanarQuadraticExample.fullBFGS_explicit_basin`,
     `BfgsVerification.DEmbedding.deterministic_embedding_failure`,
     `BfgsVerification.DNonStrictObjectives.embedding_same_search`,
     `BfgsVerification.SeedOrbit.actual_coercive_deterministic_failure`,
     `BfgsVerification.LGlobalFailure.actual_global_failure`,
     `ArticleBranchRegularity.smoothLocalFailure_with_branch_obstruction`.

### P2: formal gap (the Lean proves a slightly different statement)

- [ ] **The lower-curvature failure theorems are formalized only for the
  strict-inequality line search.**
  - Paper: the search in Section 6 (`paper/sections/failure.tex`, eq.
    `art:failure_tests`) uses non-strict tests (`≤` for Armijo, `≥` for weak
    Wolfe). It then states "All comparisons in the construction are strict, so
    strict acceptance tests give the same decisions."
  - The C^{2,1} construction (Theorem `art:local-failure`) is covered for both
    versions:
    - `DeterministicLineSearch` (strict);
    - `NonStrictLineSearch`, linked by
      `DNonStrictObjectives.embedding_fromMetric` / `embedding_same_search`.
  - Lower curvature: only the strict search is used.
    - `LWhitening.IdentityFailureTarget` (`LIdentityTargets.lean:7,13`) and
      `LGlobalFailure.actual_global_failure` (`LGlobalFailure.lean:8,27`) open
      `DeterministicLineSearch`.
    - No `NonStrict` counterpart exists for the lower-curvature construction.
  - Affected paper statements:
    - Theorem `art:local-failure-lower` (`paper/statements/negative_lower.tex`);
    - Proposition `art:quadratic_failure` (`paper/appendices/lower_curvature.tex:43`).
  - The mathematics is fine: `LNormalizedOracle.Conditions` already carries
    strict rejection margins (`rejects : … armijoMargin … < 0`,
    `LNormalizedOracle.lean:166`) and strict acceptance margins.
  - Fix, either:
    - (a) add an L analogue of `DNonStrict*` proving that
      `NonStrictLineSearch.fromMetric` gives the same trace along the
      lower-curvature runs and add it to the claim ledger; or
    - (b) say in the paper that the formal certificate for the lower-curvature
      construction is for the strict tests.

### P3: bookkeeping, reproducibility and paper polish

- [ ] **Article supplements are not part of the Lake package.**
  - Files: `editorial/narrative_rebuild/positive_formal/MixedBenchmark.lean`
    (Corollary `art:mixed-benchmark`),
    `editorial/satisfaction_review/branch_formal/ArticleBranchRegularity.lean`
    (the "first three branches not twice differentiable" claim),
    `editorial/article_formal/ArticleGeometry.lean`,
    `editorial/article_formal/ConvexBalance.lean` and
    `editorial/narrative_rebuild/negative_scaling.lean`.
  - They are compiled only by custom `verify.py` runners (`lake env lean …`), so
    `lake build` alone never checks the headline `u²+|v|` result.
  - Fix: add them as `lean_lib` targets in `bfgs_lean_stage1/lakefile.toml`, or
    move them into the package.
- [ ] **The determinant identity is proved but not mapped to its statements.**
  - Paper: Theorem `art:minor-hierarchy` ("At j=n … det H_+ = (α/β) det H",
    `paper/sections/energy.tex:140`) and Lemma `art:gram-compression`
    (`paper/appendices/matrix_algebra.tex:11`).
  - Lean: proved as `HessianUpdate.inverseBFGS_step_det_beta` (also inside
    `hessianInvariants`, `FoundationTargets.lean:16-22`).
  - Gap: neither declaration is listed in those two records of
    `editorial/CLAIM_LEDGER.json`. Add it.
- [ ] **"Every norm" has no literal Lean instance.**
  - Paper: Corollary `art:homogeneous-examples` (`paper/sections/global.tex:224`)
    covers every norm and every gauge with a bounded unit sublevel.
  - Lean: these cases are immediate from
    `AdmissibleBFGSRun.homogeneous_iterates_zero_of_bounded_zero_sublevel`, but no
    theorem states them. Optional: add a short corollary for an arbitrary norm
    function.
- [ ] **Paper understates the Lean result for the global lower-curvature
  failure.**
  - Paper: Proposition `art:quadratic_failure` is stated for c₁ = 10⁻⁴ and
    c₂ = 1/2 only ("Throughout this appendix …", `lower_curvature.tex:14`).
  - Lean: `LGlobalFailure.actual_global_failure` proves it for every μ > 0,
    0 < c₁ ≤ 1/3 and c₁ < c₂ < 1.
  - Options:
    - Strengthen the proposition in the paper.
    - Extending the *local*, identity-initialized Theorem
      `art:local-failure-lower` to the same range would need new Lean work.
      `IdentityFailureTarget` fixes (10⁻⁴, 1/2), and the seed orbit would have to
      be chosen once for all constants. That looks feasible because the margins
      are uniform for c₁ ≤ 1/3.

## Checked and matching (no action needed)

The paper statement is on the left; the Lean declarations whose types I compared
are on the right. Where the Lean version is more general, that is noted.

| Paper | Lean |
|---|---|
| Def `art:admissible` | `AdmissibleBFGSRun` (`ObjectiveDefinitions.lean`) |
| Lemma `art:run-invariants` | `AdmissibleBFGSRun.positive_invariants`, `hessianInvariants` |
| Lemma `art:reference-energy` | `AdmissibleBFGSRun.fixed_reference_energy(_bound)` |
| Thm `art:minor-hierarchy` | `principalMinorHierarchy : PrincipalMinorHierarchyTarget` |
| Thm `art:reciprocal-growth` | `reciprocalGrowth`, with the bridge from admissible runs via `toFullBFGSRun` and `beta_lower_bound` |
| Def `art:band-certificate`, Thm `art:certificate` | `BandCertificate`, `transportedCertificateConvergence` (C ≥ 0 and b > F* not required) |
| Thm `art:radial-equivalence` | `radial_of_inward_on_compact` (any compact K) |
| Cor `art:radial-convergence` | `radial_certificate_convergence_on_sublevel`, `inwardCertificateConvergence` |
| Thm `art:centered`, Cor `art:local-centered` | `centered_values`, `centered_iterates`, `local_centered_basin` |
| Cor `art:mixed-benchmark` | `ArticlePositive.mixed_benchmark_global` (objective is literally `(x 0)^2+|x 1|`) |
| Thm `art:homogeneous` | `homogeneous_coercive_iterates_zero` |
| Lemma `art:localization` | `Localization.neighborhood_basin`, `sublevel_compact` |
| Thm `art:polyhedral`, Cor `art:plq` | `finite_polyhedral_basin`, `piecewise_quadratic_basin`, `smooth_plus_piecewise_quadratic_basin` (cells need not be full-dimensional) |
| Thm `art:planar-cluster`, Cor `art:planar-convergence` | `planar_affineCritical_cluster_on_sublevel`, `planar_convergence_on_sublevel` |
| Cor `art:planar-max` | `finite_max_local_basin`, `finite_max_hessian_local_basin` |
| Thm `art:nonradial-example` | `fullBFGS_explicit_basin` (applies the general planar theorem, so its hypotheses are shown satisfiable), `PlanarQuadraticSeparationTarget` (eligible for c₁ = 1/4, c₂ = 1/2) |
| Lemma `art:planar-field` | `PlanarAllPairs.source_all_endpoint_estimates` |
| Thm `art:local-failure` | `DEmbedding.deterministic_embedding_failure`, `branch_contDiff`, `branch_hessian_bounds` (0 ⪯ ∇² ⪯ 64I), `branch_hessian_lipschitz`, `objective_unique_minimum`, `objective_sublevels_compact`, `objective_not_differentiable_zero`; all queries differentiable, at most 5 trials, lengths 1, 1/4, 1/16, H₀ = I, every 0 < c₁ ≤ 1/3 and c₁ < c₂ < 1 |
| Cor `art:failure_polyhedral` | `SeedOrbit.actual_coercive_deterministic_failure` (fourth branch `v − 17`, optimizer (−1, 16), value −1) |
| Lemma `art:upper_scalar_lemma` | `DScalar.scalar_function_contract` (constants max{6, 102/b} and max{6, 139264/(5b²)} match) |
| Lemma `art:root_certificate` | `AlgebraicSeed.exact_closed_box`, `box_denominators_and_ratio` (centre equals r̄ exactly) |
| Lemma `art:lower_hyperbolic` | `LReturnSpectrum.actual_spectral_contract` (0.038 < λs < 0.039, 1.564 < λu < 1.565, ρ-eigenvector with τ = 1) |
| Thm `art:local-failure-lower` | `ArticleBranchRegularity.smoothLocalFailure_with_branch_obstruction` (only the strict search; see P2) |

Notes on conventions (no action needed):

- `Vec n := Fin n → ℝ` carries Lean's sup norm. All convergence and compactness
  conclusions are norm-independent. Euclidean quantities (strong convexity,
  Lipschitz constants, Hessian operator norms, `euclideanSolutionDistance`) are
  written explicitly with `sqNorm` or `euclideanVector`.
- Functions defined at non-differentiable points (`coordinateGradient`,
  `RadialHessian.matrix` via `fderiv`), and division by zero, are always guarded
  by differentiability or positivity hypotheses wherever they enter a statement.
