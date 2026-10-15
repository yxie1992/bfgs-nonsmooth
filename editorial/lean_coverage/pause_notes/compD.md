> Pause note of the `compD` coverage agent (companion 12_D + appendices/seed_certificate), written on 14 October
> 2026 on the Linux machine and moved here for the handoff (see `HANDOFF.md`).
> Paths are repository-relative. Scratch files under `/tmp/opencode/compD/` did not
> survive; the note contains the sources of the scripts that matter. Ledger hints:
> `python3 editorial/lean_coverage/companion_hints.py` writes
> `editorial/lean_coverage/hints/<stem>.json`.

# compD pause note (agent for companion Chapter D + seed appendix)

Paused 14 Oct 2026 on coordinator request, during the reading/analysis phase.
**Nothing written to the repository yet**: no module file, no register edit, no Lean run.
(`git status` shows only the coordinator's AGENT_BRIEFS.md / README.md edits.) No scratch
files exist yet (`/tmp/opencode/compD/` was never created). Hints file used:
`editorial/lean_coverage/hints/12_D.json` (regenerable by `editorial/lean_coverage/companion_hints.py`).

## Task (unchanged)
TeX: `companion/chapters/12_D.tex` (502 lines), `companion/appendices/seed_certificate.tex` (199).
Registers: `editorial/lean_coverage/register/C_12_D.json` (62 mech. items, all status null),
`C_seed_certificate.json` (19 items, all null) + prose items to add.
Modules (to create): `bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch12D.lean`
(ns `BfgsCoverage.Companion.Ch12D`) and `.../Companion/SeedCertificate.lean`
(ns `BfgsCoverage.Companion.SeedCertificate`). They must NOT import each other; may import
`BfgsArticle.Coverage.Article.*` (Failure, NegativeUpper, SeedCertificate). Checker:
`python3 editorial/lean_coverage/check_coverage.py --strict --allow-discrepancies companion/chapters/12_D.tex companion/appendices/seed_certificate.tex` must exit 0.
Lean: `export PATH="$HOME/.elan/bin:$PATH"`; in `bfgs_lean_article/`:
`LEAN_NUM_THREADS=4 lake env lean BfgsArticle/Coverage/Companion/<Name>.lean`; one process at a time.

## Done (reading)
Brief + README; model MatrixAlgebra.lean; Failure.lean (all 2574 lines: reusable
`seedStep/seedStart/seedPoint/seedDir/seedSlope/fullUpdate`, `seed_*`, `trial_table`,
`accepted_armijo_iff/ratios`, `cone_orbit_scaling`, `downhill_direction`,
`cone_limit_nonstationary`, `failure_polyhedral`, scalar thms `scalar_constants`,
`ramp_center_coordinate`, `ramp_primitive`, `primitive_formulas`, `phi_formulas`, `phi_unique`,
`upper_scalar_lemma`, `positive_interval_derivatives`, `constant_derivative_lengths`,
`scalar_nodes`, objective thms `upper_objective`, `objective_branch_hessians`,
`objective_minimizer`, `center_arguments`, `upper_local_model`, `local_model_branches`,
`center_value_slope`, `query_slab`, `query_values`, `query_norm_bound`, `baseQueryMax`,
`no_uniform_lower_curvature`, `regularity_map_first_row`, `failure_starts_null`);
NegativeUpper.lean (`local_failure` = model for D:main); A_seed_certificate.json (all items);
header + declaration list of Article/SeedCertificate.lean (not its bodies);
library: DDisplayPrecision, DDisplayActual (head), DeterministicLineSearch, DLiteralTargets,
DNonStrictObjectives, DEmbeddingTarget (`deterministic_embedding_failure`), DScalarTarget
(`scalar_function_contract`); CLAIMS.json D spans + edits (50_dl.json: D-round-x3/H2/c2/ell,
D-actual-closure-evidence, D-actual-trial-certificates); prepare_shared_appendix.py;
check_coverage.py; extract_items.py.

## Decisions / findings so far
1. **Ch. D search is STRICT**: `DeterministicLineSearch.fromMetric` (Armijo `F(x+a•p) < F x + c₁*a*dot g p`,
   Wolfe `c₂*dot g p < dot (coordinateGradient F (x+a•p)) p`), exactly lines 34-44. Need strict
   analogues of article `fromMetric_fuel_mono`, `search_fuel_succ`, `implemented_run_unique`,
   `specified_search` (article ones are NonStrict; duplicate in Ch12D). Strict library runs:
   `SeedOrbit.run` + `orbit_search`; `coerciveRun` + `coercive_orbit_search`;
   `DEmbedding.run hn c₁ c₂ …` + `DEmbedding.run_search`. Line 45 "non-strict … identical orbit":
   `DLiteralTargets.nonStrictRun` / article `Failure.strict_tests_same_decisions`.
2. **M11 does not recur in Ch. D**: constants fixed (l.52 c₁=10⁻⁴,c₂=1/2 for D:main; l.204 for
   the table; l.233 extends to all 0<c₁≤1/3, c₁<c₂<1). Verified l.233: Armijo ratios
   0.76658/0.39319/0.37521 > 1/3; Wolfe ratios -1, -U/129≈-0.18638, (1-c)/(-T)≈-0.81712 < 0;
   strict Armijo holds iff c₁<r_j, so all c₁≤1/3 ok; strict Wolfe for every c₂>0; rejections
   raise G. So table, query lists, l.233 are correct as printed.
3. **Decimals** ("≃", "approximately", 12-digit tables): state as nearest rounding,
   `|actual − printed| < unit/2` via `DDisplayPrecision.corrected_error` (printed companion
   values = `DDisplayPrecision.corrected`). Index map of `DDisplayActual.values`: 0 ρ (unit
   10⁻³⁰); 1-8 (z_j)_1,(z_j)_2 for j=0..3; 9-17 G(z_j+αp_j) rows 0..8; 18-20 G(z_j);
   21/23/25 Armijo ratios r₀,r₁,r₂; 22/24/26 Wolfe ratios; 27-29 c_2,ℓ_2,u_2;
   30-32 c_{b*},ℓ_{b*},u_{b*} (DScalarRamp.center/lowerLength/upperLength). Whole-box version
   for ρ: `raw_bounds_on_original_ball` + `corrected_interval`.
4. **Appendix = article appendix with renames** (companion line = article line − 1).
   Default: each item `SAME_AS` the A/seed_certificate item with note. Exceptions:
   (a) `lemma/comp:root_certificate` (37-40): "(D:rho) holds" now = ρ=129R/(V(U+129))
       ≃ 0.060199206107543764815373666287 → own theorem: unique root, positive factors,
       and on the whole box |ρ − 0.0601992…287| < 10⁻³⁰/2 (plus 0.060<ρ<0.061). Printed
       proof only gives 60/1000<ρ<61/1000 → note on `proof/001` (PROOF), not a discrepancy.
   (b) l.190 "The same interval operations give the value enclosures in that table": the
       companion table (section label comp:trial_table) shows 12-digit decimals, no
       enclosures; query-box intervals (width 10⁻⁶) can't give them → planned DISCREPANCY
       (imprecision) on a prose item; corrected claim = 10⁻⁴ enclosures
       (`BfgsCoverage.Article.SeedCertificate.table_value_enclosures`) + DDisplayPrecision.
       Same entry: "Table~\ref{comp:trial_table}" (l.186) points to a \section (prints
       "Table 12.3", no numbered table) — typo; fix in prepare_shared_appendix.py links.
   (c) closing sentence l.197-199 "complete the proof of the seed and query assertions in
       Chapter D": correct as printed here → PROOF (single `of`, e.g. C/12_D/disp/015) or
       SAME_AS a list of the Ch.D seed items; not a discrepancy (unlike A/…/prose/012).
       `proof/002` → PROOF of C/12_D/disp/015 (D:closure), other thms in `lean`.
   Checker rules: PROOF/PART_OF need exactly one `of`; SAME_AS may be a list but must not
   target DISCREPANCY items (A/failure/lemma/art:seed_cycle, A/failure/table/art:trial_table,
   A/seed_certificate/prose/012 are DISCREPANCY).
5. **D:main** (47-62) ≠ art:local-failure: C² (not C^{2,1}), c₁=10⁻⁴,c₂=1/2 and then every
   0<c₁≤1/3,c₁<c₂<1 ("same function, initial points, matrices, and trial decisions"), strict
   search, index n, p_n = `DEmbedding.center n`, ≤5 trials, trajectories in arbitrarily small
   nbhd for large n (`DEmbedding.trajectories_uniformly_small`) → own theorem modelled on
   `NegativeUpper.local_failure` with strict `fromMetric`.
6. Trial table l.205-218 is a tabular (no table env) → not mechanical; add prose items
   (rows/cells/decisions, header "G(z_j+αp_j)"). Notation: ϑ=θ, ε₀=ε, c_b=t_b
   (`DScalarRamp.center`), ℓ_b/u_b, d_*=(-1,16), p_n=x̄_n.
7. Items to check still: l.298 (0≤P_b'≤96, ∫P_b=1−c_b), l.342 (≤102a_n/b), l.374-379
   (139264/(5b²) = (1+ϑ)/(b²(1−ϑ))·3/(2ε₀²) checked by hand ✓), l.380 "does not make them
   analytic or uniformly strongly convex" (non-analytic needs a proof!), l.405-413 Hessian
   bounds/‖g_i‖<2/60000, l.253 0∉conv (`DLiteralIdentities.zero_not_mem_gradient_hull`),
   l.264 weights, l.189 formalization sentence (NON_CLAIM but cover secant/Hessian-update
   equivalence/PD: `hessianUpdate`, `DBoxDenominators.*`), l.486-489 norm bound,
   "Relation to earlier work" (NON_CLAIM, literature).

## Remaining (in order)
1. Read rest of Article/SeedCertificate.lean bodies needed (root_certificate, query thms).
2. Write Companion/SeedCertificate.lean (small: root_certificate with D:rho rounding,
   discrepancy corrected statement, non-vacuity example) and its register.
3. Write Ch12D.lean (strict-search helpers, D:main, seed items, table prose items,
   decimals, scalar section, objective, final orbit, non-vacuity example) and register.
4. Lean-check each module (one process), then the checker; final answer per brief.
