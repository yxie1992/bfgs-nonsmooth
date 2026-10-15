> Pause note of the `compM` coverage agent (companion 02_M), written on 14 October
> 2026 on the Linux machine and moved here for the handoff (see `HANDOFF.md`).
> Paths are repository-relative. Scratch files under `/tmp/opencode/compM/` did not
> survive; the note contains the sources of the scripts that matter. Ledger hints:
> `python3 editorial/lean_coverage/companion_hints.py` writes
> `editorial/lean_coverage/hints/<stem>.json`.

# Pause note: companion chapter 02_M (agent compM)

Paused 14 Oct 2026 on coordinator request. Resume only after a message saying RESUME.

## Task (unchanged)
Cover `companion/chapters/02_M.tex` (288 lines). Register
`editorial/lean_coverage/register/C_02_M.json` (52 mechanical items, all `status: null`, plus prose
items to add, ids `C/02_M/prose/<nnn>`). Module `BfgsArticle.Coverage.Companion.Ch02M` =
`bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch02M.lean`, namespace
`BfgsCoverage.Companion.Ch02M`. Binding rules: `editorial/lean_coverage/AGENT_BRIEFS.md` sections
"Lessons from the article" + "Companion coverage agent", and `editorial/lean_coverage/README.md`.
Finish: `python3 editorial/lean_coverage/check_coverage.py --strict --allow-discrepancies
companion/chapters/02_M.tex` exits 0; Lean: from `bfgs_lean_article/`,
`export PATH="$HOME/.elan/bin:$PATH"; LEAN_NUM_THREADS=4 lake env lean BfgsArticle/Coverage/Companion/Ch02M.lean`
(one Lean process at a time; never lake build/update/clean; no native_decide; no warnings).
Final answer: counts by status, declarations with items, discrepancies, items not covered,
substantial new proofs, check times, notes for other agents. Edit no other file; do not commit.

## State on disk
- NOTHING written in the repository yet. `Ch02M.lean` does not exist (the directory
  `Coverage/Companion/` exists, empty). `C_02_M.json` untouched. (`git status` shows only
  AGENT_BRIEFS.md and README.md modified, which were modified before I started.)
- No Lean check has been run yet.
- Scratch: `/tmp/opencode/compM/sig.py` (only helper; recreate if lost): run from repo root,
  `python3 /tmp/opencode/compM/sig.py <full Lean names>` prints module, source range and
  signature from `bfgs_lean_stage1/master_report/DECLARATION_INDEX.json`
  (dict name -> {signature, module, source_path, source_range}).
- Hints: `editorial/lean_coverage/hints/02_M.json` (ledger export lists per span; copy of the
  relevant names is below in case /tmp is lost).

## Done (reading)
Brief + README; model `Coverage/Article/MatrixAlgebra.lean` + `A_matrix_algebra.json`;
`Coverage/Article/Energy.lean` (all 1938 lines) + `A_energy.json` (all items, discrepancy on
A/energy/prose/012 = M10); `Local.lean` lines 1-260 (Euclidean conventions, `localization`,
`localization_sphere_min`, `localization_radial_lower`); the whole TeX chapter; `01_I.tex` 1-70
(infinite admissible run convention at 01_I.tex:40-47: nonzero gradients at differentiable
accepted iterates, positive lengths, fixed 0<c1<c2<1 Armijo/weak Wolfe; Euclidean space);
`check_coverage.py`; TODO_MANUSCRIPT_REVIEW.md M7-M11; library files
`FoundationEndToEnd.lean`, `FoundationTargets.lean` (HessianInvariantTarget, LocalizationTarget,
StrictContourTarget, ReferenceEnergyTarget, QuadraticCorrectionTarget, ExactFrameCertificate +
MovingFrameCriterionTarget, ResidualFrameCertificate + ResidualFrameCriterionTarget),
`Localization.lean`, `StrictContours.lean`, `Definitions.lean` (FullBFGSRun, principalSum,
reciprocalMean/GeometricMean, Reciprocal/Superquadratic targets), `ObjectiveDefinitions.lean`
(AdmissibleBFGSRun fields: convex, x, H, g, α, c₁, c₂, c₁_pos, c₁_lt_c₂, c₂_lt_one,
initial_posDef, alpha_pos, gradient_nonzero, hasGradient, step, update, armijo, weak_wolfe;
q, d = α q, beta, initialSublevel).

## Key facts found
- Energy.lean reusable theorems (namespace `BfgsCoverage.Article.Energy`): `run_notation`,
  `notation_display`, `run_invariants` (H≻0, q,d,t>0, c₁d≤Δ≤d, t≥ωd, Hessian update, Bhat PSD,
  Bhat s=0, finite value limit → Summable d), `reference_notation`, `reference_energy`,
  `energy_step`, `principalSum_def`, `principal_sums_coefficients` (e_j = esymm of eigenvalues,
  coefficients of det(I+zH), orthogonal invariance), `principal_trace_det`, `minor_hierarchy`,
  `compression_bound`, `eigenbasis_gram_sum`, `reciprocal_growth`, `potential_eq_weighted`,
  `run_bounds`, `normalized_hierarchy`, `potential_pos`, `q_le_potential`,
  `potential_contraction`, `reciprocal_sum_superlinear(_of_minimizer)`, `summability_stronger`,
  `superquadratic_growth` (= M:superquad), `finite_horizon_bound` (= M:finitehorizon, with
  hypotheses G>0, ‖g_k‖≤G, Summable d, DJ = ∑' i, d (J+i), K0 = 4G²/ω², V on PosDef, m ≥ 2),
  `finite_reciprocal_sum_le`, `normalization_bounds`, helpers `sqNorm_le_of_norm_le`,
  `sqNorm_bound_of_bounded`, `norm_sq_eq_sqNorm`, `euclideanVector_sub`; non-vacuity run
  `Energy.Example.run` (quad x²/2, x_k=2^{-k}, H=1, α=1/2, c=(1/4,3/4)) with `run_bounded`,
  `run_summable`, `run_d`, `quad_sublevel_compact`, `quad_isLeast`.
- MatrixAlgebra.lean theorems (namespace `BfgsCoverage.Article.MatrixAlgebra`):
  `kappa_eq_and_curvature`, `update_split` (disp H₊=𝓕+α/(βq)vvᵀ), `compression_posDef`,
  `compression_formula`, `compression_determinant`, `gram_schur` (both Schur identities),
  `gram_dets_nonneg`, `compression_gram_bound` (M:compression), `compression_update`,
  `compression_add_rank_one` (det changes by exactly ρ det A u), `u_bounds` (0≤u≤q, increase ≤
  (α/β)det A), `full_dimension_case`, `det_update`, `gram_compression`. Standing-assumption forms:
  hH, hs : s = -α • (H *ᵥ g), hα, hq_def, hq, hβ_def : β = -dot y (H *ᵥ g) / q, hβ,
  hHplus : Hplus = inverseBFGS H s y, Z with Zᵀ * Z = 1, 1 ≤ j ≤ n, v, κ = dot g (H *ᵥ y),
  P = 1 - κ⁻¹ • outer v y, F = P * H * Pᵀ, A = Zᵀ * H * Z, a = Zᵀ *ᵥ (H *ᵥ g),
  b = Zᵀ *ᵥ (H *ᵥ y), r = dot y (H *ᵥ y), u = dot a (A⁻¹ *ᵥ a), w, z similarly.
  Gram_H(y,Z) = `metricGram H (fromCols (replicateCol Unit y) Z)`,
  Gram_H(g,y,Z) = `metricGram H (fromCols (Matrix.of ![g, y])ᵀ Z)`.
- Local.lean (namespace `BfgsCoverage.Article.Local`): Euclidean ball/sphere forms
  `{x | ‖euclideanVector (x - c)‖ < r}`, `localization_sphere_min` (needs hn : 1 ≤ n, U, r,
  closed Euclidean ball ⊆ U, δ = sInf over `{u | ‖euclideanVector u‖ = r}` of F(x*+u)-F(x*):
  IsLeast + δ>0), `localization_radial_lower` (‖x−x*‖/r δ ≤ F x − F x*), helpers
  `euclid_norm_sq`, `continuous_euclid_norm`, `euclid_ball_open_convex`, `dot_le_euclid`.
- Library Localization.* lemmas are for a general normed space (on `Vec n` that is the SUP
  norm); use Local.lean's Euclidean forms instead.
- Library names from the ledger (verify signatures with sig.py): span 1:
  AdmissibleBFGSRun.{cluster_pair_segment_constant, hessian_update, positive_invariants,
  predicted_decrease_bounds, segment_value_lower, steps_tendsto_zero_of_strict_contour,
  summable_predicted_decreases_of_value_limit}, Localization.{low_sublevel_subset_ball,
  neighborhood_basin, radial_lower_bound, sphere_gap, sublevel_bounded, sublevel_compact},
  StrictContours.level_mem_frontier, convex_supporting_bound_on_compact (ConvexOn F, IsCompact K
  → ∃ G>0, ∀ x∈K, ∀ g with supporting inequality, sqNorm g ≤ G²), hessianInvariants,
  hessianUpdate, localization, strictContourSteps. Span 2: diagonal_coordinate_gram_sum_eq,
  insert_product_sum_eq, orthogonal_coordinate_gram_sum_eq, principalGramSumIdentity,
  principal_product_augmented_sum_eq. Span 3: SharpPotentialDegree.{
  optimized_potential_eq_polynomial, potentialPolynomial_eval, potentialPolynomial_natDegree,
  principal_optimized_bound, principal_optimized_polynomial, run_optimized_bound,
  run_optimized_root_tendsto, shifted_potential_root_tendsto, weightedPotential_mul_le_pred},
  sharpPrincipalPotential. Span 4: AdmissibleBFGSRun.{fixed_reference_energy,
  fixed_reference_energy_bound, moving_frame_energy, moving_frame_reciprocal_sum_bound,
  normalized_frame_trace_recurrence, objective_tendsto_min_of_negligible_corrections},
  EnergyIdentities.{fixed_reference, moving_frame}, movingFrameCriterion,
  quadraticCorrectionConvergence, referenceEnergy. Span 5: AdmissibleBFGSRun.{
  residual_frame_step, residual_frames_on_tail_incompatible_source,
  smooth_subspace_projection_trace_bound, smooth_subspace_projection_trace_update,
  smooth_subspace_residual_budget}, EnergyIdentities.gram_add_kernel, FrameBounds.{
  gram_trace_add_le, gram_trace_square, gram_trace_transport_le, scalar_young},
  FrameNorms.{operatorSqBound_iff_opNorm_sq, orthonormal_matrix_for_subspace},
  SmoothSubspace.residual_energy_le, residualFrameCriterion.

## Decisions taken (tentative where marked)
- Run = `R : AdmissibleBFGSRun n F` (chapter line 9 inherits the inventory convention; F finite
  convex is in the structure). c = `1 - R.c₂` (article's ω). Norms Euclidean
  (`‖euclideanVector v‖`, `sqNorm`). "Bounded gradients" = `∃ Λ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ`.
- Write own wrapper theorems (import `BfgsArticle.Coverage.Article.Energy`, `.MatrixAlgebra`,
  `.Local`) for companion items with different notation/hypotheses (G instead of Λ, c instead of
  ω, companion theorem statements); use SAME_AS (with a note) only for displays literally equal
  to article items. Planned SAME_AS candidates: disp/008 → A/matrix_algebra/disp/002;
  disp/010 → A/matrix_algebra/disp/005; disp/011, disp/012 → A/matrix_algebra/disp/006 (halves);
  disp/013 (M:compression) → A/matrix_algebra/disp/007; disp/015 → A/energy/disp/015 (companion
  omits the middle sum). Wrappers are acceptable too if hypothesis matching looks doubtful.
- disp/009 (pure definitions A,a,b,r,u,w,z, no "≻0" claim): DEFINITION, with a small theorem
  (e.g. A ≻ 0 so A⁻¹ is a true inverse) as lean name. disp/014: own LEAN theorem from
  MatrixAlgebra.compression_update + compression_add_rank_one + u_bounds.
- Theorem M:hierarchy: own theorem (H SPD from "For SPD H" line 63; α>0 implicit: "ordinary"
  update needs t = αβq > 0); proof via Energy.minor_hierarchy. disp/007 PART_OF.
- Prose line 63 (e_j via eigenvalues, e_{n+1}=0, e_1=tr, e_n=det): DEFINITION with unfolding
  theorem (principalSum = esymm of eigenvalues for symmetric H; principalSum_terminal;
  principal_trace_det).
- Lemma M:localization: own theorem, Euclidean: hn : 1 ≤ n, U ∈ 𝓝 x*, r>0, closed Euclidean
  ball ⊆ U (unused, `_`), ω = sInf over Euclidean sphere; conclusions: sphere nonempty, ω is a
  minimum (IsLeast), ω>0, and ∀ R : AdmissibleBFGSRun n F, F(R.x 0) − F x* < ω →
  {F ≤ F(R.x 0)} ⊆ open Euclidean ball ∧ ∀ k, R.x k ∈ ball (title says "invariant").
  disp/005 PART_OF; disp/006 LEAN (radial bound ≥ ‖x−x*‖/r ω ≥ ω); proof/001 PROOF (also list
  sublevel_bounded/compact + dimension-zero theorem if written).
- Lemma M:strictcontours: own theorem: K = {F ≤ b} compact, ∀ k, R.x k ∈ K, F(x_k) → ℓ
  (decrease automatic by Armijo; maybe add `_hmono : Antitone`), F_* via
  `IsLeast (Set.range F) Fstar` (attained anyway on a compact sublevel), ℓ > F_*, no nontrivial
  segment in `frontier {w | F w ≤ ℓ}` → `Tendsto R.displacement atTop (𝓝 0)`. Proof via
  `R.steps_tendsto_zero_of_strict_contour` (initial sublevel compact = closed subset of K).
- Theorem M:average: own wrapper of Energy.reciprocal_growth (note library generalization
  `reciprocalGrowth` for FullBFGSRun with c ≤ β_k). Theorem M:superquadratic: own wrapper of
  Energy.finite_horizon_bound + superquadratic_growth; NOTE G and V_η are not defined in the
  statement (they come from the proof of M:average) — record as note or typo-level discrepancy
  (decide); D_J > 0 is automatic (d_k > 0).
- Prose items to add (non-exhaustive, numbering in text order): line 3 (NON_CLAIM), line 9 three
  sentences (NON_CLAIM: provenance/convention), line 22 "∑d_k<∞ on a run with finite limiting
  value" (LEAN: summable_predicted_decreases_of_value_limit), line 26/30 metric Cauchy–Schwarz
  "(g_kᵀz)² ≤ q_k zᵀB_kz" and "B_ks_k = −α_kg_k" (LEAN), line 32 bounded subgradients on compact
  K (LEAN via convex_supporting_bound_on_compact, Euclidean form) and its proof sentences /
  "does not require differentiability" (fold into same item or NON_CLAIM), line 63 (DEFINITION),
  line 173 two sentences (NON_CLAIM scope; comparison M:average weaker assumptions → LEAN via
  summability_stronger or SAME_AS), lines 182 (DEFINITION r_k,a_k,E_k; disp/025 R_k), line 190
  cancellation identity (LEAN, ring) and "a_k ≥ F(x_k) − F_*" (LEAN, R.gap_le_referencePairing),
  line 194 three sentences (see risks), lines 196-211 moving frame (disp/028 supposition,
  disp/029 LEAN moving_frame_energy, disp/030 LEAN normalized_frame_trace_recurrence, line 211
  "Positivity gives ∑q⁻¹ = O(N), contradicting Theorem M:average" LEAN via
  moving_frame_reciprocal_sum_bound / movingFrameCriterion; last two sentences NON_CLAIM),
  line 246 "tr(P_SB_k) ≤ C_S+L_Sk" is inside the proof (not an item), line 275 three sentences,
  lines 279-288 "Relation to earlier work" (mostly NON_CLAIM literature; "The BFGS update, secant
  equation, positive-definiteness preservation and determinant identity are classical" asserts
  facts → cover by LEAN/SAME_AS: secant equation, R.positive_definite, det identity).

## Risks / discrepancy candidates to check on resume
1. Line 194 "Thus ∑_{k<N}R_k = o(∑ q_k⁻¹) excludes a positive gap": from (M:energybound) this
   needs ∑ q_k⁻¹ → ∞ (else R_k = 0 and η²S_N ≤ E_0 gives no contradiction), i.e. bounded
   gradients + d_k → 0 (M:average) — parallel of M10. Check the hypotheses of the library's
   `objective_tendsto_min_of_negligible_corrections`; decide DISCREPANCY (needs a real
   counterexample or unprovability argument) vs LEAN/SAME_AS with note listing implicit
   hypotheses (lesson: only DISCREPANCY if false as phrased).
2. Line 194 "With the summability assumptions of Theorem M:superquadratic, an O(N²) cumulative
   correction suffices": library `QuadraticCorrectionTarget` uses minimizer + uniqueness
   (+ check whether bounded gradients/∑d_k needed); compare carefully.
3. Line 211 "contradicting Theorem M:average": needs bounded gradients + d_k → 0, not stated in
   the paragraph (hypothetical tail) — another M10 parallel; library MovingFrameCriterionTarget
   has G and d→0 hypotheses.
4. M:residualtheorem vs library ResidualFrameCertificate (uses R.shift J, U orthonormal basis of
   S with P_S = U Uᵀ, OperatorSqBound, frobSq, residual_range (U Uᵀ) Z = Z): check every
   hypothesis word for word (e.g. "‖P_Sy_k‖² ≤ L_St_k" for all k on the tail; constants
   real/nonnegative; frames V_k with p columns).
5. disp/024 "liminf N⁻² ∑ q_k⁻¹ ≥ c/(2D_J)": find the exact library statement
   (SharpPotentialDegree.run_optimized_root_tendsto etc.).
6. Non-vacuity: Energy.Example.run (bounded gradients, summable d) for run theorems; matrix
   examples as in Energy/MatrixAlgebra; strict contours/localization: quad run (F=x²/2,
   unique minimizer 0, but ℓ > F_* hypothesis with F(x_k) → ℓ cannot hold for that run since
   F(x_k) → 0 — need a different witness or a satisfiable general form; note Lemma
   M:strictcontours may be vacuous-looking: think of a run with positive limiting level, e.g.
   1-D |x| runs stall? Probably state non-vacuity of hypotheses minus the run, or find a run
   whose values converge to ℓ > min — check library `UnexcitedMetric.run` (u²+|v|) or Global's
   absRun / Verification's fourMaxRun / Failure runs that fail to converge).

## Remaining (all of it)
1. Verify signatures of all library names above (sig.py) and read the relevant library
   proofs (SharpPotentialDegree, moving frame, residual frames, ObjectiveEnergy).
2. Write Ch02M.lean: header docstring (conventions, item table, non-vacuity), helpers,
   theorems in TeX order with docstrings ``Item `C/02_M/...` (`companion/chapters/02_M.tex:a-b`)``,
   non-vacuity examples; compile (one process).
3. Fill C_02_M.json (statuses, lean names, notes, prose items with anchor/lines,
   discrepancies entries with item/description/severity/proposed/lean).
4. Run the checker until exit 0; record check times; final answer in the brief's format.

## Scratch helper content (`/tmp/opencode/compM/sig.py`)

```python
import json, sys
idx=json.load(open('bfgs_lean_stage1/master_report/DECLARATION_INDEX.json'))
for name in sys.argv[1:]:
    e = idx.get(name)
    if e is None:
        hits = [k for k in idx if k.endswith(name)]
        print("NOT FOUND:", name, "candidates:", hits[:10])
        continue
    print("==", name)
    print("  module:", e.get('module'), e.get('source_path'), e.get('source_range'))
    print("  sig:", e.get('signature'))
```
