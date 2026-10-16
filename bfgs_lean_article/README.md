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
- the new modules in `BfgsArticle/`, including the Lean coverage modules in
  `BfgsArticle/Coverage/` (below);
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
python3 scripts/axiom_audit.py [--jobs 6] --report AXIOM_AUDIT.json [--write-guard]
```

This runs `#print axioms` on every Lean name that `editorial/CLAIM_LEDGER.json`
cites, for the article and for the companion (every export field of every record,
and the declaration lists of the article supplements), on every Lean name of the
Lean coverage registers (`editorial/lean_coverage/register/`), and on this
package's principal declarations. It fails if a cited name is missing or if any
axiom other than `propext`, `Classical.choice` and `Quot.sound` appears. The audit
imports `BfgsArticle`, so the names of a coverage module resolve only once
`BfgsArticle.lean` imports it. The names are split across `--jobs` concurrent Lean
processes (with 6: about 5 minutes for 3862 names on 24 cores, 6.5 minutes for
the 5420 names of 15 October 2026 and 7.9 minutes for the 5506 names of
16 October on a 10-core MacBook). Private helper
names (`_private.…`) in the supplements' declaration lists cannot be named outside
their module; they are listed in the report, and their axioms are part of those of
the public declarations that use them. `AXIOM_AUDIT.json` records the result, the
commit and tree state at the start of the run, and the exact signatures of the
package declarations. `--write-guard` regenerates `BfgsArticleAxioms.lean`.

## Kernel replay

```sh
git clone https://github.com/leanprover/lean4checker /path/to/lean4checker
cd /path/to/lean4checker && git checkout v4.19.0 && lake build   # same Lean version
cd -  # back to bfgs_lean_article
python3 scripts/kernel_replay.py --checker-repo /path/to/lean4checker --self-test --report KERNEL_REPLAY.json
```

`#print axioms` trusts that every declaration in the compiled `.olean` files was
checked by the kernel. lean4checker re-checks that: for each module it loads the
module's imports and replays every declaration of the module through the Lean
kernel, so a declaration that entered the environment without a kernel check
(for example through `set_option debug.skipKernelTC`) makes it fail. The script
runs it on every project module (the import closure of this package's default
targets: the main library, the supplements and this package), one module per
process, `--jobs` at a time. The two root modules contain only `import` lines and
are listed instead of replayed. Mathlib and Lean core are not replayed. With
`--self-test` the checker's own `test.sh` runs first and must detect its
deliberately forged test declarations. `KERNEL_REPLAY.json` records the result
and the checker's tag, commit and binary hash. With the default 8 jobs, the
replay of the 783 modules of 15 October 2026 took 25 to 27 minutes on a 10-core
MacBook; the 786-module M42 replay of 16 October took 26.8 minutes.

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
| `BfgsArticle/AdmissibleRunExistence.lean` | Existence of admissible runs, so that statements about every run are not vacuous. `AdmissibleRunExistence.exists_wolfe_step` and `exists_admissible_run`: if `F` is convex, bounded below, differentiable at all but countably many points of every line through a point of differentiability, and has no point of differentiability with gradient zero, then from every point of differentiability, for every `H₀≻0` and all `0<c₁<c₂<1`, an infinite admissible run exists (every step strict Armijo and strict weak Wolfe). For Theorem `art:nonradial-example`: `PlanarQuadraticExample.exists_admissible_run` and `nonradial_example_nonvacuous`. The article's registers cite it, and several companion coverage modules import it. |
| `BfgsArticle/HypothesisExamples.lean` | M42 joint objective/certificate/run witnesses: `HypothesisExamples.Mixed.joint_witness` for `u²+|v|`, `HypothesisExamples.Quadratic.joint_witness` for a full-rank Euclidean quadratic calibration in arbitrary dimension, and `HypothesisExamples.Gauge.joint_obstruction` for a coercive max-linear objective with no differentiable weak-Wolfe first step from the stated identity-initialized data. |
| `BfgsArticle/TwoQuadraticExample.lean` | M42's positive-parameter two-quadratic family. `TwoQuadraticExample.paper_planar_hypotheses`, `finite_max_hypotheses` and `joint_witness` prove the literal planar assumptions, the indexed active-gradient conditions, universal convergence, and an actual infinite run for every differentiable start, SPD matrix and valid constant pair. The `Radial` namespace also proves a fixed-band radial obstruction for the specialization `(1,1,2)`. |

The two M42 mathematical modules and the literal article coverage were
independently reviewed on 16 October 2026
(`editorial/main_results_scope_20261016/verification/`, relative to the repository
root). The new coverage module has 29 named theorems, including direct statements
about the mixed run's least spectral value. The article additions and the
Chapter 7 caveat have 54 new classified items. Clean module compilations and
standard-axiom checks passed. The full package build with the new coverage import
also passes (105 seconds on the MacBook, no new warnings). The reviewed
correspondence integration is complete (103 rows). Fresh package-wide evidence
on clean commit `74900ef` passed on 16 October: 5506 audited declarations,
standard axioms only, and 786 modules replayed through the kernel with the
checker self-test passed. `BfgsArticleAxioms.lean` remains the same 182-name guard.
The current reports include these additions; the 15 October release archive
records the earlier edition. See
`editorial/main_results_scope_20261016/verification/EVIDENCE.md` in the repository.

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

## Coverage modules

`BfgsArticle/Coverage/Article/` (16 modules) and
`BfgsArticle/Coverage/Companion/` (18 modules) are the Lean coverage of the
article and the companion, both complete: one module per TeX file, namespaces
`BfgsCoverage.Article.<Name>` and `BfgsCoverage.Companion.<Name>`. Each
declaration states a claim of the documents, and its docstring names the claim's
register item and source lines. The registers in
`editorial/lean_coverage/register/` link every item to its declarations. Method
and rules: `editorial/lean_coverage/README.md`; progress: `TODO_LEAN_COVERAGE.md`
at the repository root. `BfgsArticle.lean` imports every finished coverage
module, so `lake build` checks it and the axiom audit includes its names.
