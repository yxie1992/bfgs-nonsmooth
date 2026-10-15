> Pause note of the `compC` coverage agent (companion 09_C), written on 14 October
> 2026 on the Linux machine and moved here for the handoff (see `HANDOFF.md`).
> Paths are repository-relative. Scratch files under `/tmp/opencode/compC/` did not
> survive; the note contains the sources of the scripts that matter. Ledger hints:
> `python3 editorial/lean_coverage/companion_hints.py` writes
> `editorial/lean_coverage/hints/<stem>.json`.

# Pause note: companion chapter 09_C (planar switching), agent "compC"

Paused on 14 October 2026 at the coordinator's request, still in the reading and planning phase.

## State on disk

- **I have edited no repository file.** `editorial/lean_coverage/register/C_09_C.json` is
  untouched: 63 mechanical items, every `status` is null, and `discrepancies` is `[]`.
  `bfgs_lean_article/BfgsArticle/Coverage/Companion/` does not exist yet, so `Ch09C.lean` has not
  been created. The two modified files that `git status` shows (`AGENT_BRIEFS.md`, `README.md`)
  were already modified when I started.
- No Lean process has been run.
- Scratch files in `/tmp/opencode/compC/`. Both can be regenerated if /tmp is lost:
  - `hints_by_span.txt`: the ledger export names for each span of 09_C. It was built from
    `editorial/lean_coverage/hints/09_C.json`. That file can be rebuilt with
    `editorial/lean_coverage/companion_hints.py`, or from the `exports` of the `C.span.k` claims in
    `bfgs_lean_stage1/master_report/CLAIMS.json`.
  - `sig.py`: a signature lookup in `DECLARATION_INDEX.json`. Usage:
    `python3 sig.py NAME...` gives the signature and source location; `python3 sig.py -g REGEX`
    lists the matching names. Source:
    ```python
    import json, sys, re
    D = json.load(open('bfgs_lean_stage1/master_report/DECLARATION_INDEX.json'))
    args = sys.argv[1:]; mode = 'exact'
    if args and args[0] == '-g': mode = 'grep'; args = args[1:]
    for a in args:
        if mode == 'grep':
            for k in sorted(k for k in D if re.search(a, k) and '._proof' not in k and 'match_' not in k):
                e = D[k]; print(k, '|', e.get('kind'), '|', e.get('source_path','').replace('bfgs_lean_stage1/',''), e.get('source_range',{}).get('start_line'))
        else:
            k = a if a in D else ('BfgsVerification.'+a if 'BfgsVerification.'+a in D else None)
            if k is None: print('NOT FOUND', a); continue
            e = D[k]; print('==', k, '|', e.get('kind'), '|', e.get('source_path',''), e.get('source_range'))
            print(e.get('signature','').replace('BfgsVerification.', ''))
    ```

## What I have read (no need to read it again in full)

- `AGENT_BRIEFS.md`: the lessons and the companion-agent sections. `README.md`.
  `check_coverage.py`: for `LEAN` the first `lean` name must be declared in Ch09C; docstring
  `Item \`id\` (\`file:a-b\`)` lines must equal the register lines; `DEFINITION` names may be
  anywhere; `SAME_AS`/`PART_OF`/`PROOF` need existing ids, and `PART_OF`/`PROOF` exactly one.
- The model `MatrixAlgebra.lean` and `A_matrix_algebra.json` (style and docstring format).
- The whole of `companion/chapters/09_C.tex`.
- `paper/sections/local.tex:150-440` and `paper/appendices/planar_geometry.tex` (all of it). These
  are the article's versions of almost all of 09_C.
- Registers `A_planar_geometry.json` and `A_local.json`: all items and their Lean names (both have
  no discrepancies).
- `PlanarGeometry.lean`: the header, lines 1-420, 700-1029 and the declaration list. The standing
  hypotheses are written literally (`hregular` in TeX form, with `regularity_of_literal`). The main
  theorem is `planar_field`, and every display has a theorem: `corner_curve`, `corner_velocity`,
  `height`/`fieldFormula` (defs), `height_eq_library`, `field_eq_fieldFormula`, `exists_angle`,
  `fieldFormula_periodic`, `corner_field_formula`, `corner_field`, `smooth_pairing`,
  `tangent_cancellation`, `derivative_triangular`, `derivative_coefficients_bounded`,
  `transversality_limits`, `transversality_contradiction`, `determinant_derivative`,
  `log_determinant_derivative_bound`, `comparison_functions`, `one_sided_comparison`,
  `log_determinant_increment`, `transport_constants`, `branch_cocoercivity`,
  `same_branch_secant`, `crossing_tie_point`, `crossing_numerator`, `crossing_pairings`,
  `crossing_step_bound`, `crossing_secant`. Non-vacuity data: `nonradial_standing`, `pTie`,
  `chartTie`, `xCross`/`zCross`, `cross_pair_eligible`, `smooth_pair_eligible`.
- `Local.lean`: the header, lines 1222-1989 and the declaration list. Theorems:
  `affineCritical_set_eq` (C_aff definition), `least_norm_point` (gᵀa=‖a‖², rate one),
  `affineCritical_and_stationarity`, `affineCritical_not_stationary_example` (max{u,2u}: affine
  critical but not stationary), `affineCorrect_iff_equal_rate`, `regular_of_paper`,
  `planar_cluster` (hypotheses: F convex, `IsLeast (range F) Fstar`, b > Fstar,
  `IsCompact {F ≤ b}`, `hstrict ∀ t, Fstar<t → t≤b → no frontier segment`, `hreg` in TeX form on
  `F p ≤ b ∧ ¬IsAffineCritical`, `R : AdmissibleBFGSRun 2 F`, `R.x 0 ∈ {F ≤ b}`),
  `planar_cluster_segment_values`, `planar_cluster_field`, `planar_cluster_energy`,
  `planar_convergence` (values, `euclideanSolutionDistance`, `argmin F = {xstar} → x_k → xstar`),
  `planar_max` (∃ ε basin, conclusion values AND iterates), `planar_max_hessian_contours`,
  `planar_max_barycentric`, `planar_max_balance_continuous`, `planar_max_affine_correct_near`,
  `planar_max_regular_near`, `strict_contours_short_chords`, `corner_moves_with_level`,
  `finitely_many_corners`, `common_normal_exposes_segment`, `tangent_step_det_zero`,
  `armijo_charges_transport`, `run_transport_budget`, `example_eq`, `nonradial_example`,
  `example_model_facts`, `example_box_facts`, `example_coefficients`, `example_tie_expansion`,
  `example_tie`, `example_radial_jump`, `example_pair_values`, `example_ratio_limits`,
  `hessian_bound_strict_contours`, `strict_contours_without_hessian_bound`. Non-vacuity with a run:
  `UnexcitedMetric.run` for u²+|v|, b=1 (`unexcited_strict_contours`,
  `unexcited_affineCritical_eq_zero`, `sq_add_lin_convex`; example at Local.lean:3315).
- Library: `AdmissibleBFGSRun` (ObjectiveDefinitions.lean:30). Its fields are exactly the
  companion's admissibility at lines 59-69: H₀ ≻ 0, α_k > 0, g_k ≠ 0, `hasGradient`, `step`
  (s_k = bfgsStep = -α_k H_k g_k), `update` (inverseBFGS), `armijo`, `weak_wolfe`,
  0<c₁<c₂<1. `R.q k`, `R.d k = α_k q_k`. `PlanarConvergence.lean`:
  `R.planar_affineCritical_cluster_on_sublevel`, `R.planar_convergence_on_sublevel` (also
  `Metric.infDist` to argmin), `PlanarConvergence.local_convergence_basin` (unique minimizer, open
  Ω ∋ star with regularity and `AffineCorrectAt` on Ω, b > F star with strict contours up to b
  ⇒ ∃ ε>0, ∀ R, F(x₀) < F star + ε → values and iterates converge). The end-to-end wrappers are
  `planarAffineCriticalCluster`, `planarConvergence` and `planarLocalBasin`.
- The CLAIMS.json edits for module C (10_ac.json): `C.initial-SPD-derived-curvature` (lines
  70: exports `positive_definite`, `q_pos`, `curvature_pos`), `C.strict-contour-proof` (proof of
  lem:steps: `segment_value_lower`, `cluster_pair_segment_constant`,
  `StrictContours.level_mem_frontier`, `differences_tendsto_zero_of_strict_contour`),
  `C.same-field-buffer-quantifiers` (line 247: `PlanarAllPairs.source_all_endpoint_estimates`),
  `C.transport-right-derivative-proof`, `C.same-branch-local-gradient-estimate`
  (`CenteredSmoothSublinear.bregman_lower_of_descent`,
  `exists_cocoercivity_constant_on_compact`, `PlanarCrossing.smooth_local_secant`),
  `C.tame-alternative-proof-and-domain` (RealAlgebraicGeometry...),
  `C.noncritical-constant-rank-domain`, `C.canonical-C1-regularity`, `C.patched-C1-field`
  (ConstantRankFields...), and `C.no-higher-dimensional-transport` (`spatialCanonicalWarning`,
  `spatialQuadraticRadial`).

## Correspondence between companion and article (to verify word for word before using SAME_AS)

| 09_C item / lines | Article item | Article Lean |
|---|---|---|
| theorem C:thm:cluster (55-57), hypotheses 35-53 | A/local/theorem/art:planar-cluster | Local.planar_cluster |
| disp/002 (C_aff) | A/local/disp/006 | Local.affineCritical_set_eq |
| disp/004, disp/005 (AW, update) | A/energy/definition/art:admissible, disp/001, disp/002 | Energy.admissible_iff, update_formula, armijo_weak_wolfe, library_formulas |
| corollary C:cor:AC (72-74), first two sentences | A/local/corollary/art:planar-convergence | Local.planar_convergence; the "local version" (third sentence) uses PlanarConvergence.local_convergence_basin |
| corollary C:cor:max (76-91) | A/local/corollary/art:planar-max | Local.planar_max (the companion concludes only x_k → x_*), planar_max_hessian_contours (companion: "replacement" for the hypothesis, so compose) |
| disp/010 (gᵀa=‖a‖²), 116 | A/local/prose/021 | Local.least_norm_point |
| disp/013 (segment values) | A/local/disp/007 | Local.planar_cluster_segment_values |
| lemma C:lem:steps | (inside the article's proof) | steps_tendsto_zero_of_strict_contour; check its signature |
| 168-181 corners, disp/014, disp/015 (C:eq:vel) | A/planar_geometry/disp/003 | PlanarGeometry.corner_curve, corner_velocity |
| disp/016, disp/017 (C:eq:h), disp/018 (C:eq:w) | A/planar_geometry/disp/004, disp/005 | height, fieldFormula, height_eq_library, field_eq_fieldFormula |
| disp/019 (C:eq:nearcorner) | A/planar_geometry/disp/006 | corner_field_formula, corner_field |
| disp/020 (C:eq:visibility) | A/planar_geometry/disp/007 | smooth_pairing |
| disp/021 (angle identity), disp/022 (triangular) | A/planar_geometry/disp/008, disp/009 | tangent_cancellation, derivative_triangular, derivative_coefficients_bounded |
| lemmas C:lem:trans, C:lem:transport, C:lem:secant (249-305) | A/planar_geometry/lemma/art:planar-field (items 2 and 3) | planar_field |
| disp/024 | A/planar_geometry/disp/010 | transversality_limits |
| disp/026, disp/027, disp/028, disp/029 | A/planar_geometry/disp/011, 012 (and 013 for the barrier) | determinant_derivative, log_determinant_derivative_bound, comparison_functions, log_determinant_increment |
| disp/031, disp/032, disp/033 (secant) | A/planar_geometry/disp/016, 017, 018 | crossing_numerator, crossing_pairings, crossing_step_bound |
| disp/034 to disp/037 (E_k, M_k, energy, telescoping) | A/local/disp/009 (energy) | Local.planar_cluster_energy; telescoping: ScalarTransport.reciprocal_sum_le, scalar_frame_reciprocal_sum_bound |
| disp/038 (Gram formula) | A/local/disp/012 | Local.planar_max_barycentric |
| disp/039 to disp/044 (quadratic example) | A/local/theorem/art:nonradial-example, disp/013 to disp/017 | example_eq, nonradial_example, example_coefficients, example_tie_expansion, example_radial_jump, example_pair_values |
| 461-492 (any dimension; 3-D warning) | none | ConstantRankFields.*, spatialCanonicalWarning, spatialQuadraticRadial (still to read) |
| 392-398 (tame alternative) | none | RealAlgebraicGeometry.semialgebraic_* (still to read) |

## Decisions taken (tentative)

1. Named results get their own wrapper theorems in Ch09C (status LEAN), proved by the article
   theorems or the library. These are cheap to write, and they state the companion's exact
   version (e.g. cor:max concludes only x_k → x_*; the Hessian bound replaces the contour
   hypothesis). Use SAME_AS to A/... only for prose that restates an article claim exactly, with a
   note on notation.
2. Standing assumptions for §§2-5 (lines 103-323) are the §1 hypotheses written as in
   `Local.planar_cluster` (`hstrict`, `hreg` in TeX form), plus, from §4, ℓ with F_* < ℓ ≤ b and
   C ⊆ {F = ℓ} compact, with no affine-critical point and the regularity hypothesis at each point
   (`hCreg`, literal TeX form, as in PlanarGeometry). The proofs specialize the article's
   PlanarGeometry theorems; strict convexity of K_ℓ comes from `hstrict ℓ`.
3. In the companion, §4 (lines 161-237) is NOT inside a proof environment. Every factual sentence
   there therefore needs a prose item (rule: outside proofs, all claims). This includes: the C²
   corner curve; isolation on level ℓ; smooth neighborhoods; finitely many curves; the velocity
   detecting increase and being C¹; normal arcs of width < π with nᵀv_j > 0; disjoint arcs and
   positive separation; existence of cutoffs; h being a convex combination of positive numbers,
   bounded and bounded away from 0, C¹ in t; periodicity; the near-corner formula on both sides;
   the continuous, locally Lipschitz extension; C¹ off the curves; uniform bounds; unit pairing at
   switching points; the uniform visibility lower bound; tangent-line preservation; bounded
   coefficients. Map them to the PlanarGeometry/Local theorems (the article's undisplayed proof
   steps already exist as theorems), written as wrappers or SAME_AS where exact.
4. disp/004 and disp/005: DEFINITION, with lean = `BfgsVerification.AdmissibleBFGSRun`,
   `inverseBFGS`, `bfgsStep` and the Energy unfolding theorems (or an own unfolding theorem in
   Ch09C). The prose at line 70 (t_k>0 derived, PD preserved) is LEAN through
   `R.positive_definite`, `R.q_pos`, `R.curvature_pos`, plus `curvature_lower_bound`.
5. Non-vacuity: reuse `UnexcitedMetric.run` (u²+|v|, b=1) as in Local.lean:3315 for the
   run-level statements, and `PlanarGeometry.nonradial_standing` / the quadratic example for the
   field statements.

## Points to check for possible discrepancies

- Lines 201-202: "The supports are disjoint, so this is a convex combination of positive numbers"
  needs 0 ≤ χ_j ≤ 1. The article states 0≤χ_j≤1; the companion does not. This may be an
  imprecision; check whether "cutoff" implies values in [0,1].
- Lemma C:lem:steps is stated with only "F(x_k)↓ℓ>F_*, K_ℓ strictly convex". Its proof uses
  compactness (the run starts in the compact K of §1) and an admissible run. Check that the
  library lemma's hypotheses match.
- Line 271: "λ² ≤ 1 + C'd for sufficiently small d". The article has d ≤ 1.
- Line 136: "A finite convex function has bounded subgradients on a compact set" is a standard
  fact and needs a LEAN prose item (`convex_supporting_bound_on_compact`,
  `bounded_gradients_of_compact_set`).
- Line 43: "stationarity implies affine criticality but not conversely" (example in Local.lean).
- Line 451: "RS fails on a positive band in every neighborhood of zero": find the companion's
  definition of RS (Chapter R?) and compare with `not_radial_secant_on_neighborhood`.
- Lines 484-491: the 3-D numbers (d=ε², t=ε²(ε²+2ε+4)/3, det[g,s,y]=(4/3)ε²(1+ε), eligibility
  for c₁=1/4, c₂=1/2, v(x+s) ∉ span{v(x),s}). Verify against `spatialCanonicalWarning`.
- Lines 392-398 (tame alternative): check against `RealAlgebraicGeometry.semialgebraic_*`.
- Lines 499-512 (relation to earlier work): mostly NON_CLAIM (bibliography). Cover the
  mathematics they assert ("derivative cancellation", "radial obstruction excludes RS").
- Check M7-M11 in `TODO_MANUSCRIPT_REVIEW.md` for parallel passages (not done yet).

## What remains (everything substantive)

1. Read: lines 1990-3484 of Local.lean (barycentric, the example theorems, examples);
   PlanarGeometry.lean 420-700 and 1030-2802; the library signatures for lem:steps,
   ConstantRankFields, spatialCanonicalWarning, RealAlgebraicGeometry, PlanarQuadraticExample
   (RS definition); `TODO_MANUSCRIPT_REVIEW.md` M7-M11; `companion/preamble.tex`.
2. Create `bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch09C.lean`, namespace
   `BfgsCoverage.Companion.Ch09C`. Imports: `BfgsArticle.Coverage.Article.Local`,
   `BfgsArticle.Coverage.Article.PlanarGeometry`, possibly `...Energy`, plus the library modules for
   §8 and §6.1. First check that the oleans of these article modules exist (no `lake build`).
3. Compile with `export PATH="$HOME/.elan/bin:$PATH"; cd bfgs_lean_article && LEAN_NUM_THREADS=4
   lake env lean BfgsArticle/Coverage/Companion/Ch09C.lean` (one Lean process at a time).
4. Fill `C_09_C.json`: statuses for the 63 items, prose items `C/09_C/prose/NNN` (anchor, lines),
   and discrepancies.
5. Run `python3 editorial/lean_coverage/check_coverage.py --strict --allow-discrepancies
   companion/chapters/09_C.tex` until it exits 0.
6. Write the final answer in the brief's format.
