# `bfgs_lean_article`: article-level Lean package

A small Lake package on top of the main library `../bfgs_lean_stage1`, which it
requires by path. It changes no file of the main library and declares no axioms.
A plain `lake build` here compiles and checks:

- the **whole main library** (`import BfgsVerification`, 736 modules);
- the **five article supplements**, which before were compiled only by their own
  `verify.py` runners. They are compiled in place, without copies:
  - `editorial/narrative_rebuild/positive_formal/MixedBenchmark.lean` (Corollary `art:mixed-benchmark`);
  - `editorial/satisfaction_review/branch_formal/ArticleBranchRegularity.lean`
    (three branches not twice differentiable at zero);
  - `editorial/article_formal/ArticleGeometry.lean` and `ConvexBalance.lean`;
  - `editorial/narrative_rebuild/negative_scaling.lean`;
- the audit-source lemmas `OriginalClaimInterpretation` cited by the claim ledger
  (`bfgs_lean_stage1/master_report/audit/sources/`);
- the new modules in `BfgsArticle/` (below);
- `BfgsArticleAxioms.lean`: generated `#guard_msgs` pins of `#print axioms` for
  every principal export in `editorial/CLAIM_LEDGER.json` and for this package's
  principal declarations. The build fails if any of them gains an axiom.

## Build

```sh
cd bfgs_lean_stage1 && lake exe cache get   # Mathlib cache (about 5.6 GB)
cd ../bfgs_lean_article && lake build       # main library + article modules
```

`lakefile.toml` sets `packagesDir = "../bfgs_lean_stage1/.lake/packages"`, so this
package reuses the main library's Mathlib checkout and cache. Use the committed
`lake-manifest.json` and do not run `lake update` here: Mathlib's update hook
assumes the default packages directory.

With `LEAN_NUM_THREADS=10` on 24 cores and 15 GB RAM, a clean build of the main
library took about 12 minutes and peaked at about 10 GB.

## Axiom audit

```sh
python3 scripts/axiom_audit.py --report AXIOM_AUDIT.json [--write-guard]
```

This runs `#print axioms` on every declaration cited for an article statement in
`editorial/CLAIM_LEDGER.json` (principal and full exports) and on this package's
principal declarations. It fails if a cited name is missing or if any axiom other
than `propext`, `Classical.choice` and `Quot.sound` appears. `AXIOM_AUDIT.json`
records the result and the exact signatures of the package declarations.
`--write-guard` regenerates `BfgsArticleAxioms.lean`.

## New modules

| Module | Content |
|---|---|
| `BfgsArticle/NonStrictTransfer.lean` | Non-strict versions of the generic search transfers: `NonStrictLineSearch.search_history_congr`, `TranslatedRun.nonstrict_local_model_search`, `ScaledCopy.Data.nonstrict_search_transfer`, `AffineWhitening.nonstrict_fromMetric_equiv`. |
| `BfgsArticle/LNonStrictGlobal.lean` | Proposition `art:quadratic_failure` with the article's non-strict search: `LGlobalFailure.nonstrict_actual_global_failure` (every `μ>0`, `0<c₁≤1/3`, `c₁<c₂<1`) and `nonstrict_source_global_failure` (`c₁=10⁻⁴`, `c₂=1/2`). |
| `BfgsArticle/LNonStrictLocal.lean` | Fixed-matrix and identity-initialized lower-curvature families with the non-strict search: `LActualCopies.nonstrict_fixed_metric_failure`, `LWhitening.nonstrict_identity_failure`, `LWhitening.nonstrictSmoothLocalFailure`, `LWhitening.nonstrictStepLocalFailure`. |
| `BfgsArticle/LNonStrictBranch.lean` | Theorem `art:local-failure-lower` endpoint: `ArticleBranchRegularity.nonstrictSmoothLocalFailure_with_branch_obstruction`. |
| `BfgsArticle/HomogeneousModels.lean` | Corollary `art:homogeneous-examples`: `AdmissibleBFGSRun.norm_conclusion` (every norm), `gauge_conclusion` (bounded unit sublevel), `finiteMaxLinear_conclusion`. |
| `BfgsArticle/LUniformGlobal.lean` | One lower-curvature orbit for every admissible pair. `LNormalizedOracle.UniformConditions` holds the seed's decision margins at `c₁∈{0,1/3}`, `c₂∈{0,1}`; `uniform_conditions_eventually` keeps them on one neighbourhood of the seed and `UniformConditions.conditions` gives the oracle conditions for every `0≤c₁≤1/3`, `0≤c₂≤1`. Proposition `art:quadratic_failure` with the initial state chosen before the constants: `LUniform.uniform_global_failure`. |
| `BfgsArticle/LUniformLocal.lean` | Theorem `art:local-failure-lower` for every `0<c₁≤1/3`, `c₁<c₂<1`: `LUniform.uniformSmoothLocalFailure` (target `UniformSmoothLocalFailureTarget`), with one objective, one family of starts with `H₀=I`, and the same iterates, matrices and complete traces for every pair. Also `uniform_identity_failure`, `uniform_fixed_metric_failure` and `branch_not_twice_differentiable_zero`. |

The library's local construction starts from `LSeedCopies.run`, an orbit chosen for
`c₁=10⁻⁴`, `c₂=1/2` only. `LUniformLocal.lean` therefore selects a new source orbit
(`LUniform.source`) and repeats the copying and whitening with the library's generic
lemmas. Its objective `LUniform.smoothObjective` is the library's
`LEmbedding.objective` whitened by the new orbit's initial matrix.

The lower-curvature declarations keep the strict trace next to the non-strict one,
for the same runs. Each non-strict proof reuses the strict margins already proved
in `LNormalizedOracle.Conditions`. Accepted trials have positive Armijo and Wolfe
margins. Rejected trials have a negative Armijo margin, so they also fail the
non-strict test.

The declarations use the main library's namespaces (`BfgsVerification.*`,
`ArticleBranchRegularity`), so that names resolve exactly as in the strict
originals. Their files are all in this package.
