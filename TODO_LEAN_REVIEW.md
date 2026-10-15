# TODO: Lean formalization review

Review date: 13 October 2026. Reviewer: AI assistant (Claude), at the author's request.

Scope: check that the Lean statements match the article's statements (`paper/`), and
look for misuse of Lean (proof holes, extra axioms, kernel bypasses, vacuous or
mis-specified definitions). Proofs were **not** read line by line. The companion's
other results were not reviewed.

**Status (13 October 2026, second pass):** Lean 4.19.0 is now installed. The library
was built from scratch here, and every item below except P3d (an optional paper edit)
is resolved. Resolutions are recorded under each item and in
`bfgs_lean_article/README.md`.

**Status (15 October 2026):** the Lean coverage of every claim of the article and
the companion is complete (fourth pass below). Three items are open: the stale
release receipts (expected), the optional linter warnings, and the Chapter 7 runs
that may not exist.

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

- [x] **Independent clean build and axiom check.** The repository's own records
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

  **Done.**
  - Build: Lean 4.19.0 via elan. Mathlib came from the official cache for the
    pinned revision (Mathlib itself was not recompiled, which is standard). The
    whole main library was compiled from scratch:
    - 736 of 736 modules built, in 11 min 41 s with `LEAN_NUM_THREADS=10`, peak
      about 10 GB RAM;
    - no errors and no `sorry` warnings;
    - 1244 linter warnings, all style: unused variables, tactics that never
      run or do nothing, `<;>` where `;` suffices, and 6 deprecations.
  - Supplements: all five now compile through the standard `lake build` of the
    new package `bfgs_lean_article/` (see P3).
  - Axioms: `bfgs_lean_article/scripts/axiom_audit.py` runs `#print axioms` on
    every Lean name that `editorial/CLAIM_LEDGER.json` cites, for the article and
    (since 14 October) the companion, every Lean name of the coverage register
    (`editorial/lean_coverage/register/`), and the new package's principal
    declarations: 5403 declarations at commit `9f03d7c` (15 October, with every
    coverage module; 3862 at `a2028c9`, 2026 before the companion was added, 3177
    before the coverage register).
    - Every cited name exists.
    - Every declaration depends only on `propext`, `Classical.choice` and
      `Quot.sound` (5396 use all three; five use only `propext`; two use only
      `propext` and `Quot.sound`).
    - The result is recorded in `bfgs_lean_article/AXIOM_AUDIT.json`.
    - The 182 principal exports are pinned with `#guard_msgs` in
      `bfgs_lean_article/BfgsArticleAxioms.lean`, so `lake build` fails if one
      of them gains an axiom.
  - Kernel replay (15 October, commit `9f03d7c`, with every coverage module):
    lean4checker v4.19.0 replayed every declaration of all 783 project modules
    through the kernel; no failures (`bfgs_lean_article/KERNEL_REPLAY.json`). Its
    own self-test, which must reject deliberately forged declarations, passed
    first. The replay of 14 October (commit `023f555`) covered the 749 modules
    that existed before the coverage modules.
  - Found along the way: 14 ledger-cited names
    (`BfgsVerification.OriginalClaimInterpretation.*`, supporting exports of
    `art:mixed-benchmark` and `art:mixed-inward-remainder`) live in an
    audit-source file outside every build target
    (`bfgs_lean_stage1/master_report/audit/sources/OriginalClaimInterpretation.lean`).
    The new package now compiles that file as well.

### P2: formal gap (the Lean proves a slightly different statement)

- [x] **The lower-curvature failure theorems are formalized only for the
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

  **Done, option (a)**, in `bfgs_lean_article/BfgsArticle/`. All new theorems
  state the non-strict trace **and** the strict trace for the same runs.
  - `LNonStrictGlobal.lean`, for Prop `art:quadratic_failure`:
    - `LGlobalFailure.nonstrict_actual_global_failure`, for every μ > 0,
      0 < c₁ ≤ 1/3 and c₁ < c₂ < 1;
    - `nonstrict_source_global_failure`, for c₁ = 10⁻⁴, c₂ = 1/2.

    These rest on non-strict versions of the oracle searches
    (`LNormalizedOracle.Conditions.nonstrict_fromMetric_search`), which reuse
    the strict margins.
  - `LNonStrictLocal.lean`:
    - `LActualCopies.nonstrict_fixed_metric_failure`, for `art:lower_local_model`;
    - `LWhitening.nonstrict_identity_failure`, `nonstrictSmoothLocalFailure` and
      `nonstrictStepLocalFailure`.

    These carry the trace through the scaled copies and the fixed whitening using
    non-strict transfer lemmas (`NonStrictTransfer.lean`).
  - `LNonStrictBranch.lean`, for Thm `art:local-failure-lower`:
    `ArticleBranchRegularity.nonstrictSmoothLocalFailure_with_branch_obstruction`.
  - Ledger: the new names are added to the records `art:local-failure-lower`,
    `art:lower_curvature`, `art:lower_objective`, `art:regularity-map`,
    `art:lower_local_model` and `art:quadratic_failure` (see P3).
  - The paper's sentence "All comparisons in the construction are strict, so
    strict acceptance tests give the same decisions" is now formally backed for
    both constructions.

### P3: bookkeeping, reproducibility and paper polish

- [x] **Article supplements are not part of the Lake package.**
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

  **Done, without touching `bfgs_lean_stage1`.**
  - Its `lakefile.toml`, root module and 761 other inputs are hash-pinned by
    `editorial/BASELINE.json` and `master_report/audit/fresh/INPUTS.json`, which
    every supplement `verify.py` checks. So the supplements are instead compiled
    in place by the new package `bfgs_lean_article/`: one `lean_lib` per
    supplement folder, with `srcDir` pointing at the existing files.
  - `cd bfgs_lean_article && lake build` now compiles:
    - the whole main library;
    - all five supplements;
    - `OriginalClaimInterpretation`;
    - the new modules;
    - the axiom pins.
  - The supplements' own `#print axioms` lines report only the three standard
    axioms.
- [x] **The determinant identity is proved but not mapped to its statements.**
  - Paper: Theorem `art:minor-hierarchy` ("At j=n … det H_+ = (α/β) det H",
    `paper/sections/energy.tex:140`) and Lemma `art:gram-compression`
    (`paper/appendices/matrix_algebra.tex:11`).
  - Lean: proved as `HessianUpdate.inverseBFGS_step_det_beta` (also inside
    `hessianInvariants`, `FoundationTargets.lean:16-22`).
  - Gap: neither declaration is listed in those two records of
    `editorial/CLAIM_LEDGER.json`. Add it.

  **Done.**
  - The ledger is generated by `editorial/assemble_claim_ledger.py` from the
    sealed component reviews. Re-running the unchanged generator reproduced the
    committed ledger byte for byte.
  - Additions are therefore a new, separate input:
    - `editorial/lean_review_20261013/LEDGER_ADDITIONS.json`, merged by
      `editorial/ledger_addenda.py`, which adds only and records a
      `formal_addenda` field on each touched record;
    - the generator gains one import and one call.
  - `art:minor-hierarchy` now cites `inverseBFGS_step_det_beta`,
    `hessianInvariants` and `HessianInvariantTarget`. `art:gram-compression`
    cites `inverseBFGS_step_det_beta`.
  - The P2 and P3c theorems are added the same way.
  - `editorial/CLAIM_LEDGER.json` and `companion/PROOF_CORRESPONDENCE.html`
    were regenerated.
- [x] **"Every norm" has no literal Lean instance.**
  - Paper: Corollary `art:homogeneous-examples` (`paper/sections/global.tex:224`)
    covers every norm and every gauge with a bounded unit sublevel.
  - Lean: these cases are immediate from
    `AdmissibleBFGSRun.homogeneous_iterates_zero_of_bounded_zero_sublevel`, but no
    theorem states them. Optional: add a short corollary for an arbitrary norm
    function.

  **Done** in `bfgs_lean_article/BfgsArticle/HomogeneousModels.lean`. Each
  theorem gives the full conclusion of Thm `art:homogeneous`: F(0) = 0, F > 0
  off zero, F(x_k) → 0 and x_k → 0, for every admissible run.
  - `AdmissibleBFGSRun.norm_conclusion`: any `N : Seminorm ℝ (Vec n)` with
    `N x = 0 → x = 0`, i.e. every norm.
  - `gauge_conclusion`: positively homogeneous of degree one, with bounded
    `{F ≤ 1}`.
  - `finiteMaxLinear_conclusion`: bounded zero sublevel.
- [x] **Paper understates the Lean result for the global lower-curvature
  failure.** *(Done on the author's instruction, 13 October 2026.)*
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
  - Note (second pass): the paper's own proof already covers the general range.
    - The seed margins in `paper/sections/failure.tex:155-158` hold for every
      c₁ ≤ 1/3 (Armijo) and every c₂ > 0 (Wolfe).
    - The proof of the proposition (`lower_curvature.tex:151-179`) uses only
      those margins near the seed.
    - So strengthening it needs only the hypothesis and the sentence at
      `lower_curvature.tex:13-14` (constants fixed "throughout this appendix")
      to change. That sentence would then apply from the copy construction on.
    - Since this changes a theorem statement, it is left for the author.

  **Done** in `paper/appendices/lower_curvature.tex`:
  - Prop `art:quadratic_failure` now reads "Let μ>0 and fix 0<c₁≤1/3 and
    c₁<c₂<1. For every neighborhood V of zero, …". This matches
    `LGlobalFailure.nonstrict_actual_global_failure`.
  - The appendix's opening sentence now says the constants are a fixed pair
    in that range, as in Thm `art:local-failure`, and that Thm
    `art:local-failure-lower` takes c₁ = 10⁻⁴, c₂ = 1/2.
  - The proof of Lemma `art:lower_hyperbolic` now cites the margins of
    Section `art:failure` for every admissible pair.
  - The copy construction picks the orbit with c₁ = 10⁻⁴, c₂ = 1/2.
  - Theorem `art:local-failure-lower` is unchanged; its Lean form fixes
    (10⁻⁴, 1/2).
  - Checks:
    - The paper was rebuilt with TeX Live 2026 (TinyTeX). It is still 49
      pages, and only pages 43, 44 and 47 changed.
    - Those three pages were inspected visually.
    - The LaTeX warnings are the same as before the edit.
    - The unedited source rebuilds to the same text as
      `release/BFGS_Journal_Article.pdf`, apart from how large delimiters
      are encoded in the PDF text layer.
    - `release/` PDFs predate this edit.
  - Companion, updated on the author's request through logged transformations
    in `editorial/generate_companion.py` (the frozen source chapters are
    unchanged):
    - Chapter 13 fixes the constants to the same range and states Theorem
      13.1 (global failure on Q_μ) for every such pair. The agreement lemma
      notes that the seed decisions are strict for every pair. The local
      embedding takes c₁ = 10⁻⁴, c₂ = 1/2.
    - Chapter 1's N3 summary states the range.
    - `companion/current_verification.tex` gains a short "13 October 2026 Lean
      review" paragraph.
    - The companion was rebuilt and is now 108 pages; the extra page comes from
      that paragraph. The changed pages were inspected visually.
    - A logged `\needspace` keeps the "Rebuild the corrected report" heading
      with its commands.
    - Pages 100–108 are the old pages 99–107 shifted by one page.

### New items from the second pass

- [ ] **Release receipts are now stale (expected).**
  - The frozen editorial checks pin file hashes. After this pass:
    - `editorial/scientific_exposition_20260913/refresh_correspondence.py --check`
      reports a stale `mapping_refresh.json`, because it pins the hash of
      `editorial/assemble_claim_ledger.py`;
    - the release manifests no longer match `CLAIM_LEDGER.json`.
  - `verify_release_inputs.py`, `check_documents.py` and
    `verify_historical_baseline.py` need the TeX-built PDFs and Node.js, which
    the Linux machine of 13 October lacked. The MacBook has them.
  - A new release run (`editorial/build.sh` and the release scripts) will refresh
    them. Plan (15 October 2026): `editorial/release_plan_20261015/PLAN.md`, a
    read-only study that dry-ran the release scripts on the MacBook. The 13
    September release was made on this MacBook, in
    `/Users/yxie/Documents/ChatGPT/BFGS-non-smooth` (at `db4dc37`, with the sealed
    Lean host cache and the earlier editions' archives): keep that checkout
    untouched. Its tooling (phase A of the plan's section 6) was written,
    independently reviewed and fixed on 15 October 2026
    (`editorial/release_20261015/TOOLING_REVIEW.md`): T1 in
    `editorial/verify_historical_baseline.py`, T2 in `editorial/validate_archive.py`
    and the new `editorial/verify_historical_correspondence.py`, T3 in
    `editorial/verify_release_inputs.py`, T4 in `editorial/release_20261015/` (its
    table of changes is filled in the release run) and T5 in
    `editorial/package_release.py`. The run follows the order in
    `editorial/release_20261015/README.md` ("Run order"), which replaces Phase 2
    of the plan: the Lean evidence comes after every change to the claim ledger,
    the coverage registers and the counts printed in
    `companion/current_verification.tex`, since the release-input check binds it
    to them. The checks to settle in the release run (numbers of the plan):
    - [ ] C1: the 13 September check `refresh_correspondence.py --check` fails at
      HEAD; it rejects every statement change, and passes at its release commit
      `3e8b5c6`. Retire it as historical (replay it unchanged in a worktree at
      `3e8b5c6`) and give its current role to C2's revision. Tooling ready:
      `editorial/verify_historical_correspondence.py` replays it at `3e8b5c6` and
      records its result at HEAD; `validate_archive.py` runs it.
    - [ ] C2: the three "Reviewed source contracts" checks of
      `verify_release_inputs.py` fail (hashes of the corrected files). Fix: a new
      bounded correspondence revision, baseline `3e8b5c6`, that lists every
      changed statement and display with its correction item and Lean coverage
      item (tooling T4 of the plan). Tooling ready:
      `editorial/release_20261015/refresh_correspondence.py` (`--propose`,
      `--write`, `--check`); its `CHANGES.json` is filled for the final sources
      and `--write` is run in step 4 of the run order.
    - [ ] C3: the ledger's copied `proof_locations` (for example those of
      `lower_curvature.tex`, below) are refreshed by C2's revision (T4's
      `--write`).
    - [ ] C4: `verify_historical_baseline.py` fails on the files added under
      `bfgs_lean_article/`. Fix: allow added paths there too, with a recorded
      reason (T1; tested by the study). Tooling ready (T1); the September
      editorial Lean files are now also required unchanged since `3e8b5c6`.
    - [ ] C5: `validate_archive.py` cannot use this repository as its Lean host
      (no `bfgs_lean_stage1/.toolchain`; the rebuilt `.lake` fails the seal,
      although its `.olean` files are byte-identical). Use the sealed September
      host. Settled: an APFS clone (`cp -cR`) of its `bfgs_lean_stage1/.lake`
      and `.toolchain`, outside the macOS temporary directory (for example
      `/Users/yxie/Projects/release_host_<date>/bfgs_lean_stage1/`), checked once
      with `cache_binding.py --check`; the workspace links to the copy, never to
      the September checkout itself (`editorial/release_20261015/README.md`,
      "Release host").
    - [ ] C6: the cache check of `verify_release_inputs.py` fails here ("only
      partially available"). Run it where `.lake` and `.toolchain` both point at
      the September host, or where both are absent; keep the rule. With the
      APFS copy of C5 both point at the copy.
    - C7–C9 pass: `editorial/BASELINE.json` and the frozen inputs (do not
      re-baseline), `generate_companion.py --check`, `check_documents.py`.
    - [ ] C10: regenerate the render manifest (`render_review.py`) and review
      every page.
    - [ ] C11: no release script checks the October Lean evidence. Rerun the axiom
      audit and the kernel replay on the final pre-freeze commit, and add
      read-only checks that bind them to the release (T3); the archive validation
      also runs `check_coverage.py --strict` (T2). Tooling ready:
      `verify_release_inputs.py` has two more checks (23 in all). The first
      requires that the audit and the replay pass and ran on a clean tree at an
      ancestor of HEAD, recounts (without Lean) the names and modules they must
      have checked, compares the counts printed in
      `companion/current_verification.tex`, and requires that no Lean file, Lake
      configuration, script of `bfgs_lean_article/scripts`, ledger or register
      changed after them.
    - [ ] C12: freeze only when `check_coverage.py --strict` exits 0 (decision D7,
      with the author). Tooling ready: the second new check of
      `verify_release_inputs.py` runs `check_coverage.py --strict`.
    - [ ] C13: rewrite `release/README.md`; several of its statements are false
      now ("The revision adds no Lean theorem", 107 companion pages, the
      reproduction command of C1).
    - [ ] C14: `release/RELEASE.json`, `release/SOURCE_MANIFEST.json` and
      `editorial/logs/*` are regenerated by the run.
    - [ ] C15: the printed edition date "Author-review edition, 13 September 2026"
      (`paper/master.tex:29`, `companion/master.tex:16`, the companion's page
      footers in `companion/preamble.tex:62,65`) becomes the freeze date
      (decision D1, with the author).
    - [ ] C16: the archive's `AUTHOR_REVIEW_README.md` (template in
      `editorial/package_release.py`) should give the commands for the October
      package `bfgs_lean_article` (T5). Tooling ready (T5).
    - [ ] C17: update the 13 September records `editorial/STATUS.json`,
      `NEXT_STATE.json`, `COMPLETION_GATES.json` and `AI_AND_AUTHOR_ACTIONS.md`
      (the AI statement is M37 of `TODO_MANUSCRIPT_REVIEW.md`).
    - [ ] C18: after the release, close this item and the "Known stale" entries
      of `HANDOFF.md` and `AGENTS.md`.
    - Preserve the 13 September edition under
      `release/history/20260913_exposition/` (plan, section 4).
    - Linking the September checkout itself into a scratch clone lets elan and
      git write into it outside its seal: the phase-A dry runs of 15 October
      added three scratch paths to its `bfgs_lean_stage1/.toolchain/elan/known-projects`
      and took transient index locks in the nine dependency checkouts under
      `bfgs_lean_stage1/.lake/packages/` (the seal is unaffected; the cache binding
      passed before and after). A full scratch validation against an APFS copy
      passed and left the checkout unchanged; hence the host of C5.
    - Limits of T4 (`editorial/release_20261015/README.md`, "Limits, by design"):
      text outside its units (prose outside the root and deduction passages,
      unmapped tables and figures and the files they input, headings) needs only
      `--write`, no row; correction items are checked for existence only, so the
      review of each row checks their relevance (`--propose` prints their texts);
      a `TODO_LEAN_REVIEW.md` title cited by a row must stay unchanged; a named
      statement or active TeX input added or removed, a negative-review proof
      moved to another file and a numbered display without `\label` are refused
      and need an extension. Besides statements and displays it covers tables
      and figures, proofs, the algorithm, macro definitions, the full text of the
      two appendices the September revision preserved, and the root and
      deduction passages.
    - `release/work/` stays as an empty directory after an archive validation.
  - Since the P3d edit, the `proof_locations` line numbers and passage hashes
    for `paper/appendices/lower_curvature.tex` in the ledger are also stale.
    They are copied from the sealed 13 September negative review and are now
    off by several lines (the M6 edits in `TODO_MANUSCRIPT_REVIEW.md` added four
    more). The records' `location` fields are recomputed and current.
  - `refresh_correspondence.py` cannot refresh these, because it rejects any
    statement change. That needs a new correspondence revision.
- [ ] **Lean linter warnings (optional, cosmetic).**
  - The main library emits 1244 style warnings.
  - Cleaning them would change hash-pinned library files, so do it only together
    with a deliberate re-baseline.

### Third pass

- [x] **Lower-curvature failure for every admissible pair at once.** Theorem
  `art:local-failure-lower` and Proposition `art:quadratic_failure` now hold for
  every $0<c_1\le1/3$, $c_1<c_2<1$ with one orbit, objective and family of starts.
  New modules `bfgs_lean_article/BfgsArticle/LUniformGlobal.lean` and
  `LUniformLocal.lean`; details under M6 in `TODO_MANUSCRIPT_REVIEW.md`.

### Fourth pass (14 October 2026)

- [x] **Axiom audit of the companion's Lean names.** 1141 names cited only by
  the companion were outside the audit. They are now included (3177 names in
  all); every one exists and uses only the standard axioms. Since the Lean
  coverage began, the audit also checks every Lean name of the coverage
  registers (3862 names at `a2028c9`; 5403 at `9f03d7c`, with every coverage
  module, 15 October).
- [x] **Independent kernel replay.** lean4checker re-checked every declaration of
  every project module (749 modules at `023f555`; 783 at `9f03d7c`, with every
  coverage module, 15 October; the two root modules only import). See the P1 item
  above.
- [x] **Literal Lean coverage of every claim** of the article and the companion:
  tracked in `TODO_LEAN_COVERAGE.md`. Complete: the article on 14 October, the
  companion on 15 October. The discrepancies it found are M7–M29 and the
  wording points W1–W43 in `TODO_MANUSCRIPT_REVIEW.md`.
- [ ] **Companion Chapter 7 (H): run statements that may be vacuous.** Theorem 7.B
  (ii) (`companion/chapters/07_H.tex:72-89`, `C/07_H/heading/002`) and the
  common-tilt family $f(u,t)=t+\max_i b_i^\top u$ (lines 94–100, 448–464:
  `disp/005`, `prose/011`, `disp/027`, `prose/043`, `prose/046`) speak about
  infinite admissible runs, but no run on these objectives is known. Proved
  (`BfgsCoverage.Companion.Ch07H`): no admissible run exists on a finite max-linear
  objective whose slopes lie on one affine line missing 0, in any dimension
  (`maxLinear_line_no_run`); hence none for any objective of Theorem 7.B (ii) in
  dimension at most 2 (`maxLinear_affine_free_no_run`), and none on the family when
  the $b_i$ lie on one line (`tilt_collinear_no_run`), in particular with at most
  two distinct $b_i$ (`tilt_two_values_no_run`) and for every member in
  $\mathbb R^2$ (`tilt_plane_no_run`). Open: slopes not on one line (at least three
  pieces, dimension at least 3), stated as `TiltNoInfiniteRunQuestion`
  (`C/07_H/prose/045`, `OPEN`). The text conditions every run statement on infinite
  runs and disclaims finite termination (lines 99–100, 461–463 and 731), so this is
  not a discrepancy, but it calls the family "useful" (line 94) without a run on it.
  For the author: settle existence, or say that these statements may be vacuous.
  `AdmissibleRunExistence.exists_admissible_run` does not apply: these objectives
  are unbounded below.

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
| Thm `art:local-failure-lower` | `ArticleBranchRegularity.smoothLocalFailure_with_branch_obstruction` (strict search), and `ArticleBranchRegularity.nonstrictSmoothLocalFailure_with_branch_obstruction` (strict and non-strict search, `bfgs_lean_article`) |
| Prop `art:quadratic_failure` | `LGlobalFailure.actual_global_failure` (strict), `LGlobalFailure.nonstrict_actual_global_failure` (strict and non-strict, `bfgs_lean_article`); every μ > 0, 0 < c₁ ≤ 1/3, c₁ < c₂ < 1 |
| Cor `art:homogeneous-examples` | `AdmissibleBFGSRun.norm_conclusion`, `gauge_conclusion`, `finiteMaxLinear_conclusion` (`bfgs_lean_article`) |

Notes on conventions (no action needed):

- `Vec n := Fin n → ℝ` carries Lean's sup norm. All convergence and compactness
  conclusions are norm-independent. Euclidean quantities (strong convexity,
  Lipschitz constants, Hessian operator norms, `euclideanSolutionDistance`) are
  written explicitly with `sqNorm` or `euclideanVector`.
- Functions defined at non-differentiable points (`coordinateGradient`,
  `RadialHessian.matrix` via `fderiv`), and division by zero, are always guarded
  by differentiability or positivity hypotheses wherever they enter a statement.
