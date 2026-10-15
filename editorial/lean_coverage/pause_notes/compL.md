> Pause note of the `compL` coverage agent (companion 13_L), written on 14 October
> 2026 on the Linux machine and moved here for the handoff (see `HANDOFF.md`).
> Paths are repository-relative. Scratch files under `/tmp/opencode/compL/` did not
> survive; the note contains the sources of the scripts that matter. Ledger hints:
> `python3 editorial/lean_coverage/companion_hints.py` writes
> `editorial/lean_coverage/hints/<stem>.json`.

# Pause note: companion chapter 13_L (agent compL)

Paused on the coordinator's request, 14 Oct 2026. Resume only after a message saying RESUME.

## State on disk

- **Nothing in the repository has been created or modified by me.** There is no module
  `bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch13L.lean` yet, and
  `editorial/lean_coverage/register/C_13_L.json` is untouched (all 52 mechanical items
  still have `status: null`). `git status` showed only the coordinator's own edits
  (AGENT_BRIEFS.md, README.md).
- Scratch: `/tmp/opencode/compL/` exists and is empty. Ledger hints:
  `editorial/lean_coverage/hints/13_L.json` (17 records; span ranges L.span.2 27-70,
  .3 75-131, .4 136-182, .5 187-248, .6 253-338, .7 343-390, .8 395-406, plus the
  narrative record `companion.lower.actual_branch_regularity` at line 412).
- No Lean process was started.

## Done so far (reading only)

Read: AGENT_BRIEFS.md (lessons and companion brief), README.md, the whole TeX
`companion/chapters/13_L.tex`, the register skeleton, the hints, and in full the article
coverage modules `Coverage/Article/NegativeLower.lean` and `Coverage/Article/LowerCurvature.lean`
with registers `A_negative_lower.json`, `A_lower_curvature.json`; also the item lists of
`A_seed_certificate.json` and `A_failure.json` (lines < 330), `paper/appendices/lower_curvature.tex`,
and `paper/sections/failure.tex` lines 1-140. Listed the declarations in
`BfgsArticle/LUniformGlobal.lean` and `LUniformLocal.lean` (not yet read in detail).

## Main finding

The chapter is very close to the article appendix `art:lower_curvature` and Theorem
`art:local-failure-lower`. Plan: import `BfgsArticle.Coverage.Article.LowerCurvature`
and `BfgsArticle.Coverage.Article.NegativeLower` (and, if needed,
`...Article.Failure` / `...Article.SeedCertificate` for the seed items). Reuse their
theorems, and use `SAME_AS A/...` only when the hypotheses match word for word (never
point at a DISCREPANCY item: A/failure/lemma/art:seed_cycle, A/failure/table/art:trial_table,
A/lower_curvature/prose/010, A/seed_certificate/prose/012 are discrepancies).

Notation map (companion → article/Lean): (b,e) = (ζ,η); r = (M₃)₁₁ = ρ̂ =
`LNormalizedReturn.returnFactor`; T_μ = `LNormalizedReturn.returnMap μ`; P_* =
`LNormalizedReturn.seed`; φ_b (companion) = ψ_b (article) = `LScalar.phi b` (same formulas:
interval formula, φ(0)=0, x²/2 for x<0, 1+x-b for x≥b; check once more when writing); ϑ_b = t_b
= `LScalarRamp.center b`; ε = 1/1024; n = ℓ; p_n = x̄_ℓ = `LEmbedding.copyCenter`; C_* =
`LEmbedding.offset`; x̄_k,H̄_k (seed orbit) = `LUniform.source.x/H`; H̄₀ = `LUniform.initialMetric`;
A = `LUniform.coordinateMatrix`; F̃ = `LUniform.smoothObjective`; μ̲, L̄ =
`LUniform.lowerConstant/upperConstant`; (c,d) = (seedC, seedD); Q_μ = `LQuadraticSeed.objective μ`.
Line search: `NonStrictLineSearch.fromMetric`, stated for every budget N ≥ 5 via
`fromMetric_fuel_mono` (copy the helper into my namespace or use the article one); trial lists
`trialHistory (phase k)`; pair hypotheses `0<c₁, c₁≤1/3, c₁<c₂, c₂<1` (`LUniform.Admissible`).

## Item plan (draft, to verify)

- disp/001 (pair range, 30-32), prose 29 (search description), disp/002 (update): DEFINITION
  (NonStrictLineSearch.fromMetric/search/nextTrial; inverseBFGS; article
  `Failure.specified_search`, `Failure.failure_update`, `Failure.fullUpdate`). Line 40
  ("strict margins, no equality-convention issues"): LEAN via
  `Failure.strict_tests_same_decisions_lower` (check statement). Line 33 (chosen before the
  pair): SAME_AS both theorems.
- theorem L:thm:global (+disp/003): new coverage theorem: ∃ g : three slopes, ∀ μ>0, Q_μ
  μ-strongly convex (Euclidean), coercive, unique nonsmooth minimizer x_*≠0; ∀ V ∈ 𝓝 0 ∃ (x₀,H₀≻0)
  and run (x,H) chosen before the pair; x→0, 0 ∉ ∂Q_μ(0); all queries differentiable and in V
  (decide whether also x₀ ∈ V and H₀ small: "initial states ... arbitrarily close to the
  origin in the sense of Section L:sec:blowup"; LUniform.uniform_global_failure gives the run;
  check if it yields H small, else consider H_{3m}→0); every branch Hessian = μI globally
  (`LQuadraticSeed.branch_hessian`); accepted lengths 1,1/4,1/16. Build from
  `LowerCurvature.quadratic_failure` + `quadratic_minimizer` + `minimizer_nonsmooth` +
  LQuadraticSeed strong convexity/coercivity lemmas.
- Line 49: "global failure: approaching the wrong vertex ≠ the minimizer" SAME_AS global
  theorem; "does not contradict our local PLQ theorem" NON_CLAIM (logical remark).
- theorem L:thm:local (+disp/004): new coverage theorem modelled on
  `NegativeLower.local_failure_lower` (F, κ, compact sublevels, unique nonsmooth minimizer 0,
  0<μ̲≤L̄ with Hessian bounds, H₀=I starts →0, runs same for every pair, limits p_n→0
  nonstationary, uniform query locality) PLUS the four-branch representation (C^{1,1},
  uniformly strongly convex, globally gradient-Lipschitz) AND the alternative step version
  (Hessian one fixed PD matrix μH̄₀ wherever twice differentiable; countable polyhedral
  nonsmooth part). Library: `LActualCopies.stepFailure`, `LActualCopies.smoothFailure`,
  `LWhitening.stepIdentityFailure`, `step_actual_hessian_bounds`, `step_decomposition`,
  `step_residual_countable_max`, `LUniform.uniform_identity_failure` (needs uniformity over
  pairs for the step version too: check whether a uniform step version exists; if not, prove
  via `LUniform.uniform_identity_failure` with step CopyData).
  "not a finite smooth-branch representation" (line 59): read as a disclaimer (cf. line 403
  "No claim of four smooth branches is made"); decide NON_CLAIM-part note vs ambiguity
  discrepancy.
- Line 61: "satisfies the literal classical-Hessian assumption, and even strong convexity"
  SAME_AS L:thm:local; "not a local counterexample with four globally C² branches" LEAN
  (`LowerCurvature.branch_second_differentiability`); "That stronger combination remains
  unproved here" → OPEN `def ... : Prop` (model `BfgsCoverage.Article.Verification.C2StronglyConvexLocalFailure`;
  check whether SAME_AS an article OPEN item fits exactly).
- Line 3: "local finite-branch functions ... lose second differentiability at the accumulation
  point" → DISCREPANCY (imprecision, M8 pattern; only three of four branches), proposed
  wording "three of the four branches ...", Lean `LowerCurvature.branch_second_differentiability`.
  "Positive lower curvature requires a separate construction": decide NON_CLAIM (motivation)
  or SAME_AS A/failure/prose/010. "no claim combines uniform strong convexity with C^{2,1}
  branch regularity": NON_CLAIM disclaimer (or OPEN).
- Seed section 75-122: disp/005 g_i DEFINITION (seed_slopes); disp/006 U..Y DEFINITION
  (SeedCertificate.factors_def); disp/007 root equations in the 10⁻³⁰ box + disp/008 c₀,d₀
  (center_def, root_certificate); line 94 existence/uniqueness → LEAN/SAME_AS
  A/seed_certificate/lemma/art:root_certificate (software sentence otherwise NON_CLAIM);
  disp/009 ρ formula with 129R/(V(U+129)) ∈ (0.060,0.061) and z₀ (Failure.seed_rho,
  seed_points; check the form 129R/(V(U+129)) equals the article's formula); disp/010
  M₁, M₃=ρI, z₃=ρz₀ (Failure.seed_closures); line 105 (z_{j+1}=z_j-α_jM_jg_j; unique active
  gradients incl. g₀ at z₃); disp/011 query lists (Failure.seed_search, every admissible pair);
  line 111 claims (rejections raise value: rejected_raise_value; decrease ratios >1/3:
  accepted_armijo_ratios; new/old directional-derivative ratios negative: seed_margins;
  unique active branches: seed_query_bounds; persistence in a neighbourhood of the normalized
  seed state: LNormalizedOracle.uniform_conditions_eventually; "This strictness is essential
  below" NON_CLAIM); line 113 ((-1,16) negative pairings, 0∉conv); disp/012 + line 118
  (LowerCurvature.gbar_def, gbar_least_norm); disp/013 L:eq:minimizer (quadratic_minimizer;
  for every μ>0); line 122 (minimizer_nonsmooth, Q_μ(0)=0).
- Section 136-182: line 137 "Adding a quadratic changes the BFGS iterates" LEAN
  (LowerCurvature.seed_not_orbit), rest NON_CLAIM/plan; disp/014 DEFINITION
  (normalized_coordinates_def); P_* prose DEFINITION (boundary_seed_def); disp/016 substep
  DEFINITION (return_substep_def); disp/017 return map DEFINITION (return_map_def); line 162
  claims (seed_return; "only positive τ represents BFGS" → part of the agreement lemma or
  NON_CLAIM); lemma L:lem:agreement: new theorem with an OPEN neighbourhood (take interior of
  the N from `LowerCurvature.lower_hyperbolic` part (i)); proof/001 PROOF; disp/018 (value/τ =
  G(Z)+μτ‖Z‖²/2) LEAN (LNormalizedOracle.physical_value_of_active, or direct).
- Section 187-248: disp/019 shape map (shape_map_def); disp/020 J decimals: need
  |J_ij − displayed| bounds (ledger: twenty-decimal kernel enclosures, lower-left must end
  427498; look in LShapePrecision / LShapeFineCertificate); disp/021 eigenvalue intervals
  (LShapeSpectrum.source_shape_roots); line 205 signs throughout the root box
  (shape_box + characteristic_signs); "no floating-point eigensolver" NON_CLAIM; disp/022
  Jacobian with last column μa, μb: needs a NEW proof that the τ-column of the first four
  rows is μ times a μ-independent vector (T_μ depends on τ only through μτ in rows 1-4) —
  search the library for a scaling lemma first; line 216 claims (internal_boundary_translate,
  returnFactor_boundary_translate, last row); disp/023 eigenvalues (charpoly factorization,
  lower_hyperbolic part (ii)); line 222 (no unit-circle/zero eigenvalue, exactly two stable,
  invertible, local diffeomorphism: LReturnSpectrum.actual_no_unit_complex_root,
  LReturnLocalInverse.actual_local_inverse); line 224 (ρ ≠ other eigenvalues, eigenvector with
  v_τ=1: actual_scale_eigenvector; stable subspace ⊄ {τ=0}); proof/002 PROOF (lean:
  LowerCurvature.stable_manifold_positive_scale, LUniform.uniform_global_failure);
  disp/024 (x_{3m}=τ_m z_m→0, H_{3m}=τ_m M(b_m,e_m)→0) LEAN from LUniform.Orbit
  (Orbit.x/H = physicalPoint/physicalMetric at period/phase); line 239 NON_CLAIM.
- Section 253-338: disp/025 DEFINITION (embedding_constants_def); disp/026
  (parameter_values) + "only two distinct values"; disp/027 (ramp_constants_def); line 267 +
  disp/028 ramp: DEFINITION (ramp_def_bi, cubicRamp) plus claims "monotone C¹ ramp" (search
  LScalarRamp for monotone/contDiff); disp/029 ∫₀¹P_b = 1-ϑ_b and 0≤P_b'≤768 (search
  LScalarRamp.integral_ramp, rampDerivative_bounds); disp/030 + line 281 DEFINITION
  (lower_scalar_def_bi, lower_scalar_unique); lemma L:lem:scalar new theorem for b = b_i:
  convex, nonnegative, coercive, unique minimizer 0, C^{1,1}, C² on (0,∞) and (-∞,0) (search
  library: LScalar ... contDiffOn), not twice differentiable at 0 (lower_scalar_not_twice_bi),
  node values/slopes (lower_scalar_nodes_bi), plateau (lower_plateau_bi), 0≤φ''≤max{1,768/b}
  (lower_scalar_regularity_bi); disp/031, disp/032 PART_OF the lemma; proof/003 PROOF;
  disp/033 (lower_scalar_derivatives_bi), disp/034 (lower_plateau_lengths_bi) LEAN;
  disp/035 DEFINITION (lower_objective_def); line 316 claims (branches_regular,
  branch_gradient_constants; "first three Hessian upper bounds < 439,446,27 wherever those
  Hessians exist" may need a new lemma: Lipschitz gradient ⇒ Hessian quadratic form ≤ L‖v‖²
  at twice-differentiable points, or a library branch Hessian bound; fourth branch Hessian μI:
  LEmbedding.branch_last_second_hasFDerivAt; "Thus the maximum is μ-strongly convex": search
  LEmbedding.objective strong convexity; software sentence NON_CLAIM); disp/036 + line 322
  (lower_objective_minimizer; F'(0;h)=max{0,h₂} needs a directional-derivative statement —
  search library "directional"); line 324 (finite_max_local_taylor); disp/037
  (lower_objective_hessian); line 329 NON_CLAIM.
- Section 343-390: line 345 definitions (copy_constants_def); disp/038 (f_i(p_n+a_ny) two
  equalities for |q_iᵀy|≤1/2, every n: LEmbedding.branch_copy / local_model_reasons);
  line 351 fourth branch residual negative (local_model_reasons); disp/039 (lower_local_model,
  n ≥ 1); line 355 (choose the orbit: copy_runs.2.1); disp/040 DEFINITION (starts);
  disp/041 + line 359 (copy_runs, copy_transfer); line 363 claims (copy_transfer); disp/042,
  line 369 (0 ∉ ∂F(p_n): search LUniform.failure_centers_nonstationary-like statement for
  LEmbedding.objective; x₀^{(n)}→0), disp/043 (copy_limits); line 373 (copy_runs: one fixed SPD
  H₀); "Fixing identity initialization" paragraph (whitening_setup, whitening_identities,
  whitening_initial); disp/044 (whitening_constants + lowerConstant_pos, upperConstant
  finite); line 381 SAME_AS/LEAN (four-branch part of L:thm:local).
- Section 395-406 (step variant): DEFINITION of the step scalar function and objective
  (find library names: LActualCopies step data / LWhitening.step_*); claims convex,
  countably piecewise affine, same node values/slopes/plateau; local copy works unchanged
  (LActualCopies.stepFailure); line 398 sentences (F = μ‖x‖²/2 + p, inactive branches with
  q_iᵀx=0, q₀,q₁ independent, locally finite polyhedral, locally affine at differentiable
  points, origin nonsmooth); disp/045 ∇²F = μI at twice-differentiable points
  (LWhitening.step_actual_hessian_bounds or similar); line 403 (Hessian μH̄₀ after the
  whitening; remaining version of L:thm:local; "No claim of four smooth branches" NON_CLAIM).
- Relation to earlier work 410-417: 411 NON_CLAIM; 413 "negative-results comparisons in
  Chapter D apply ..." NON_CLAIM (comparison); **"This chapter uses the fixed line-search pair
  displayed in this chapter; D's wider parameter family is not imported."** → check
  `companion/chapters/12_D.tex` for D's parameter family; if D's family is the same
  (0<c₁≤1/3, c₁<c₂<1, now stated "for every pair"), record a DISCREPANCY (leftover from the
  fixed-pair edition; fix is a generator transformation) and say so in the final answer;
  "first three branches ... fail to be twice differentiable at the accumulation point" LEAN
  (branch_second_differentiability); "simpler global example does not establish failure near
  its true minimizer" NON_CLAIM; literature NON_CLAIM. 415 NON_CLAIM (stable-manifold
  principle classical; note: proved in Lean as LReturnStableGraph / AnalyticStableGraph). 417
  affine invariance: LEAN/SAME_AS via whitening_identities (literature result used, proved in
  Lean); "single fixed transformation" description.

## Remaining work (in order)

1. Read `BfgsArticle/LUniformGlobal.lean`, `LUniformLocal.lean` in detail, and the library
   L* modules (LActualCopies, LWhitening, LGlobalTargets, LScalar*, LShapePrecision /
   LShapeFineCertificate, LNormalizedReturn, LReturnSpectrum, LReturnLocalInverse) using
   `bfgs_lean_stage1/master_report/DECLARATION_INDEX.json` (names in the hints file).
2. Read `companion/preamble.tex`, conventions of `companion/chapters/01_I.tex`
   (infinite-admissible-run convention), `12_D.tex` (parameter family, for line 413), the
   model `Coverage/Article/MatrixAlgebra.lean` + `A_matrix_algebra.json`, the article
   discrepancy list M7-M11 in `TODO_MANUSCRIPT_REVIEW.md`, `CLAIMS.json` edits of the L spans,
   and `editorial/lean_coverage/check_coverage.py` (what DEFINITION/SAME_AS/prose fields it
   enforces; docstring line check).
3. Write `Ch13L.lean` (namespace `BfgsCoverage.Companion.Ch13L`), check with
   `export PATH="$HOME/.elan/bin:$PATH"; cd bfgs_lean_article && LEAN_NUM_THREADS=4 lake env lean BfgsArticle/Coverage/Companion/Ch13L.lean`
   (one Lean process at a time; no lake build/update/clean; no native_decide; no warnings).
   Scratch tests in `/tmp/opencode/compL/`.
4. Fill `C_13_L.json` (statuses, prose items `C/13_L/prose/<nnn>` with anchor + lines,
   discrepancies) and run
   `python3 editorial/lean_coverage/check_coverage.py --strict --allow-discrepancies companion/chapters/13_L.tex`
   until exit 0.
5. Final answer per brief: counts by status, declarations with items, discrepancies, items not
   covered, substantial new proofs, check times, notes for other agents.

## Open decisions / risks

- Discrepancy candidates: line 3 (M8 pattern, likely), line 413 (fixed-pair leftover, pending
  12_D check), line 59 "not a finite smooth-branch representation" (likely disclaimer, not a
  discrepancy), line 351 "n ≥ 1" (sufficient, not wrong).
- Possibly substantial new proofs: μa/μb Jacobian column (τ enters only through μτ), branch
  Hessian upper bounds 439/446/27 at twice-differentiable points, F'(0;h)=max{0,h₂},
  C² of φ_b on (0,∞), initial state H₀ small (if read so in L:thm:global), J decimal display
  bounds, uniform-over-pairs step-variant failure if the library lacks it.
