> Pause note of the `compR` coverage agent (companion 04_R), written on 14 October
> 2026 on the Linux machine and moved here for the handoff (see `HANDOFF.md`).
> Paths are repository-relative. Scratch files under `/tmp/opencode/compR/` did not
> survive; the note contains the sources of the scripts that matter. Ledger hints:
> `python3 editorial/lean_coverage/companion_hints.py` writes
> `editorial/lean_coverage/hints/<stem>.json`.

# Pause note: companion chapter 4 (R), agent compR

Written 14 October 2026 at the coordinator's PAUSE REQUEST. Continue only after RESUME.

## State on disk

- **No repository file has been changed by this agent.** `editorial/lean_coverage/register/C_04_R.json`
  is still the untouched mechanical register (54 items, all `status: null`). The module
  `bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch04R.lean` does not exist yet. No Lean
  process was started. (`git status` shows only the coordinator's edits to `AGENT_BRIEFS.md`
  and `README.md`.)
- Phase reached: reading and planning finished for the setup, Theorem R:thm:equiv and its two
  proof subsections, the central-difference paragraph, the intercept section and the plan of all
  prose items. Library reading for sections 4.3 (four-piece), 4.4-4.6 still to do (list below).

## Scratch files (`/tmp/opencode/compR/`, may be lost)

- `lookup.py` — declaration lookup in `bfgs_lean_stage1/master_report/DECLARATION_INDEX.json`
  (`python3 lookup.py 'REGEX' ...` prints kind/module/path/range/signature; `-f` full signature;
  `-m MODULE` lists a module). Recreate from this copy:

```python
#!/usr/bin/env python3
import json, re, sys, pickle, os
ROOT = 'the repository root'
CACHE = '/tmp/opencode/compR/declidx.pickle'
if os.path.exists(CACHE):
    d = pickle.load(open(CACHE, 'rb'))
else:
    raw = json.load(open(ROOT + '/bfgs_lean_stage1/master_report/DECLARATION_INDEX.json'))
    d = {k: {kk: v.get(kk) for kk in ('signature', 'module', 'source_path', 'source_range', 'kind')} for k, v in raw.items()}
    pickle.dump(d, open(CACHE, 'wb'))
args = sys.argv[1:]
if args and args[0] == '-m':
    for k, v in sorted(d.items()):
        if v.get('module') == args[1] and '._proof' not in k and '.match_' not in k:
            print(k, '|', v.get('kind'), '|', v.get('source_range'))
    sys.exit()
full = '-f' in args
for pat in [a for a in args if a != '-f']:
    r = re.compile(pat)
    for k, v in d.items():
        if r.search(k) and '._proof' not in k and '.match_' not in k and '._eq_' not in k and '._unfold' not in k:
            print('==', k, '|', v.get('kind'), '|', v.get('module'), '|', v.get('source_path'), v.get('source_range'))
            sig = v.get('signature') or ''
            print('   ', sig if full else sig[:1500])
```

- `declidx.pickle` — cache of the index (regenerated automatically by `lookup.py`).
- `hints_list.txt` — the ledger export lists per span, regenerable with
  `python3 -c "import json; [print(r['id'], *(r.get('lean') or []), sep='\n   ') for r in json.load(open('editorial/lean_coverage/hints/04_R.json')) if not r['id'].startswith('companion.unnamed')]"`
  (hints file itself: `editorial/lean_coverage/hints/04_R.json`; its generator is
  `editorial/lean_coverage/companion_hints.py`).

## Read so far

Brief (`AGENT_BRIEFS.md`: lessons + companion agent), `README.md`, model `MatrixAlgebra.lean` +
`A_matrix_algebra.json`, `Global.lean` (all 2375 lines) + `A_global.json` (all notes),
`PositivePartition.lean` + register, `Local.lean` lines 1-840 + `A_local.json` item list,
`check_coverage.py`, `TODO_MANUSCRIPT_REVIEW.md` (M7-M11), `04_R.tex` (all), `12_D.tex` 70-269
(seed c,d; run x_{3m+j}=ρ^m z_j; Ḡ(u,v)=max{u,-u-v/8,cu+dv,v-17}, minimizer (-1,16)),
`01_I.tex` 25-184 (infinite admissible run = `AdmissibleBFGSRun`; zero gradient = termination).
Library read in full: `RadialCertificate.lean`, `RadialEquivalence.lean`, `InwardRadial.lean`,
`RadialReverse.lean`, `RadialNormConvention.lean`, `RadialCentralDifference.lean`.

## Still to read (library / context)

`InterceptExamples`, `OriginalClaimInterpretation` (article supplement, path
`bfgs_lean_stage1/master_report/audit/sources/OriginalClaimInterpretation.lean`),
`ReconstructedFourPiece` + `ReconstructedFourPieceTargets`, `ObjectiveValueScale(Targets)`,
`SeedOrbit` (coercive part), `ConvexCellRadial`, `RadialPower` (PoweredGaugeRadial?),
`RectangularNuclear`, `CenteredSpectral`, `AffineKinks`(Algebra), `FirstDifference`,
`EuclideanResidual`, `FiniteMaxRadial`, `ParabolicRadialBoundary`, `NuclearSymmetric2`
(+ `NuclearRotatedPairs`, `NuclearGram`, `CenteredRectangularNuclear` per group hints);
`Local.lean` 840-end (lasso, `euclidean_residuals_local_form`/`_basin`, `plq_different_hessians`,
`example_radial_jump`) and the `A_local.json` notes of prose/009, 016, 017, disp/016;
`companion/preamble.tex`; `CLAIMS.json` `edits` of the R spans (`master_report/edits/`).

## Decisions taken

1. Module `BfgsArticle.Coverage.Companion.Ch04R`, namespace `BfgsCoverage.Companion.Ch04R`;
   may import `BfgsArticle.Coverage.Article.Global`, `.Local`, `.PositivePartition` and reuse
   their theorems, but every LEAN item's first name must be declared in Ch04R.
2. Setting written out in each theorem as in `Global.lean`: `hF : ConvexOn ℝ univ F`,
   `hmin : ∀ x, F xstar ≤ F x`, `b`, `hb : F xstar < b`, `K`, `hK_def : K = {x | F x ≤ b}`,
   `hK : IsCompact K`; constants `R G`, `hR : 0 < R`, `hG : 0 < G`,
   `hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R`,
   `hGK : ∀ x ∈ K, ∀ v, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G`
   (norms Euclidean; the chapter's G is the article's Λ).
3. Own definitions, literal to the TeX: `RS F xstar K` with `∃ C : ℝ` (TeX "C_η<∞", no sign),
   `IR F xstar K` with `∃ M θ : ℝ, 0 < θ ∧ θ ≤ 1/2` (M real), written with dot products; unfolding
   theorems `RS ↔ RadialCertificate.HasRadialSecantBounds` (literal) and
   `↔ Global.RadialSecantCondition` (C ≥ 0 version), same for IR with `HasInwardTaylorBounds`
   (via `inward_error_eq`) and `Global.InwardModelCondition`. Also `SP` (= `HasInterceptBounds`),
   `CentralCondition` (= `HasNestedCentralBounds`, written with r = x - x_*).
4. The subsections "Proof that (IR) implies (RS)" (lines 89-116) and "Proof that (RS) implies
   (IR)" (122-151) are proofs: add prose items (status `PROOF`, of
   `C/04_R/theorem/R:thm:equiv`) covering them; their displays get LEAN theorems under the standing
   assumptions at that point (band η, constants M, θ from IR, resp. θ = min{1/2, η/(4GR)},
   C = C_{η/2} from RS, differentiable x (and z), z = x - t r_x, a = (g-h)ᵀr_x). Lines 173-177
   (derivative-free paragraph) are treated as the proof of the equivalence claimed with disp/022.
5. disp/008-013 restated in the module (not SAME_AS the article's displays), because the article
   versions assume M ≥ 0 and C ≥ 0; with M real the bound N² ≤ max{2M,4GR/θ}T still holds
   (apply `inward_probe_quadratic_bound` with max M 0).
6. Theorem R:thm:plq: "a neighborhood" = `N ∈ 𝓝 xstar` (use `interior N` and
   `PositivePartition.polyhedral`); "C^{1,1} extension" read as `LocallyC11On (V i) (f i)` (as the
   proof only uses Lipschitz bounds on a small ball), plus a specialization with a global
   Lipschitz gradient on V_i; conclusion `∃ ε > 0, ∀ R, F (R.x 0) ≤ F xstar + ε →
   Tendsto R.x atTop (𝓝 xstar)` (TeX says only "converges to x_*"); full-dimensionality unused
   (`_hfull`). disp/040 restated from `Local.polyhedral_inward_taylor` with the companion's radius R.
7. disp/001 ("K = {F ≤ b}, b > F_*, compact") and the sentence of line 30: standing assumptions →
   NON_CLAIM with reason naming the hypotheses (as the article's `A/global/prose/006`); disp/002
   → LEAN (existence of such R, G: `Global.exists_subgradient_and_radius_bounds`); "Such a
   subgradient bound exists because a finite convex function is locally Lipschitz" → LEAN
   (check Mathlib `ConvexOn.locallyLipschitz` + the bound).

## Item plan (statuses intended; Lean names provisional)

Section 4.1: line 3 intro → prose SAME_AS `A/global/corollary/art:mixed-benchmark` (first clause),
SAME_AS [`A/global/prose/021`,`A/global/disp/009`] (second), SAME_AS `C/04_R/theorem/R:thm:plq`
(last sentence). disp/003 DEFINITION (notation g,h,y,s,T,N; theorem `notation_eq`). disp/004 LEAN
(D_F(z,x) ≥ 0, only x differentiable); prose l.49 SAME_AS disp/004 ([BB] comparison is literature).
disp/005 LEAN (T = D(z,x)+D(x,z), 0 ≤ T ≤ 4GR; `secantCurvature_eq_errors`,
`secantCurvature_le_four_mul`). disp/006 DEFINITION `RS`; l.53 NON_CLAIM (history); l.60 three
sentences PART_OF disp/006. l.62 run convention: DEFINITION (`AdmissibleBFGSRun`,
`Article.Energy.admissible_iff`) / NON_CLAIM for "all-ray existence not asserted".

Section 4.2: theorem/R:thm:equiv LEAN `equiv` (RS ↔ IR on K; `radial_iff_inward_on_compact_sublevel`;
plus inward point in K, `Global.inward_point_mem`); disp/007 DEFINITION `IR`. l.83: label sentence
NON_CLAIM; "t is a fraction of the distance" SAME_AS `A/global/prose/011`; "factor ‖r_x‖² ...
η/G ≤ ‖r_x‖ ≤ R" LEAN (`RadialNormConvention.inward_iff_norm_scaled_on_compact`,
`positive_band_radius_lower`, with the companion's G). IR⇒RS displays 008-013 LEAN
(`inward_probe`, `radialNumerator_swap`, `inward_probe_quadratic_bound`). RS⇒IR: disp/014 LEAN
(θ_η ∈ (0,1/2]); disp/015 LEAN (F(z) ≥ F(x) - GtR ≥ F_*+3η/4, any x ∈ K on the band; see
`RadialApproximation.inward_positive_band_margin`); disp/016 a ≥ 0 (t = 0: gradients equal);
disp/017 `inward_secant_identities`; disp/018 (case a > 0, then t > 0); disp/019 stated in the
case a > 0 (then C > 0). Caveat to note in the PROOF item: the a = 0 case "D ≤ ta = 0 ≤ 4Ct²"
and "M_η = 8C_{η/2}" need C_{η/2} ≥ 0; this holds whenever the η-band has a differentiable point
(an opposite-side pair has T > 0), library uses 8·max(C,0). Probably not a discrepancy.

Section 4.2.3: disp/020 DEFINITION (φ_d); l.162 "control the change of its scalar derivative
uniformly over directions" → LEAN new: under RS, ∀η ∃L, unit d, ρ' < ρ both on the η-band,
differentiable: 0 ≤ gᵀd - hᵀd ≤ L(ρ - ρ') with L = C_η G²/η²; "Angular derivatives may jump" →
LEAN via benchmark u²+|v| (`Global.mixed_inward_condition`, `mixed_not_differentiable`);
disp/021 SAME_AS `A/global/prose/017`; "checking a.e. is not enough" SAME_AS `A/global/prose/018`;
disp/022 LEAN `central_equivalence` (`central_of_radial_on_sublevel`,
`radial_of_central_on_smaller_sublevel`, `local_radial_iff_nested_central`) with def
`CentralCondition`; l.173-177 prose PROOF of disp/022 (lean: `inward_error_le_central`,
`central_difference_le_five_of_pair_radial`, `dense_radial_differentiable_triples`); disp/023 LEAN
(a_+ ≤ Ct, a_- ≤ Ct/(1-t)²; `outward_error_le_of_pair_radial` style); "outward point need not
remain in K" → LEAN: F(x)=b, t>0 ⇒ F(x_*+(1+t)r_x) ≥ F(x)+t(F(x)-F_*) > b.

Section 4.3: disp/024 LEAN (b_F identity, ≥ 0; `optimizerIntercept`); l.193 "= D_F(x_*,x)" LEAN
(`optimizerIntercept_eq_error`); disp/025 LEAN (`radialNumerator_eq_error_intercepts`); disp/026
LEAN equivalence RS ↔ SP (`radial_iff_intercept_on_compact`) + def `SP`; "RS with C ⇒ SP with
2C+2T_max and conversely" LEAN (`intercept_bound_of_radial`, `radial_bound_of_intercept`); "full
gradient need not be Lipschitz" LEAN (benchmark: SP holds, gradient jumps across v=0); "√T not a
metric" NON_CLAIM; "degree one ⇒ b_F ≡ 0" LEAN (`InterceptExamples.homogeneous_intercept_zero`);
disp/027 LEAN b_F = u² (`quadratic_absolute_intercept`); Euler (l.213) LEAN `degree_euler`
(homogeneity with Real.rpow, t^0 = 1 at t = 0); disp/028 LEAN `degree_intercept_at_reference`;
l.217: no minimizer needed PART_OF disp/028, reference zero + constant term LEAN, definition of
homogeneity DEFINITION, degree zero ⇒ constant LEAN; l.219-220 p > 0 LEAN
(`compact_nonnegative_homogeneity_positive_degree`); disp/029 LEAN; l.220-224 proof → prose PROOF;
l.226 + disp/030 LEAN (`compact_homogeneous_minimizer_eq_zero`,
`compact_homogeneous_optimizer_intercept`, `zero_value_eq_zero_of_compact_sublevel`); l.230
witness z = x_* LEAN; F ≡ 1 counterexample LEAN (`positive_constant_*`, `degree_zero_intercept`,
`unrestricted_zero_degree_formula_fails`, `degree_zero_positive_sublevel_not_compact`); "explain the
breadth" NON_CLAIM. Four-piece paragraph: disp/031-038 and prose l.253-281 → `ReconstructedFourPiece.*`,
`ObjectiveValueScale.*`, `SeedOrbit.coercive_*`, `reconstructedFourPieceFailure` (each claim:
δ>0, a>0, branch formula, optimizer (-1,5), value -1, branch values -1,-1,-29/4, errors 0,0,25/4,
run transform, Ĥ₀ ≻ 0, Armijo/Wolfe preserved, x̂_k → 0, values ↓ a-1 > -1, 0 nonstationary,
phase errors, curvatures a·T_k → 0, points above band -1+a, SP and RS fail on K); history
sentences NON_CLAIM. Need an exhibited run (non-vacuity) = the transformed run itself.

Section 4.4: theorem LEAN (decision 6), disp/039 PART_OF, proof/001 PROOF (lean:
`ConvexCellRadial.actual_gradients_eq_on_cell`, `full_derivative_eq_on_cell`,
`incident_neighborhood`, `local_cells_inward`), disp/040 LEAN. l.309: PLQ + loss SAME_AS
`A/local/corollary/art:plq` (note: uniqueness from the theorem, smooth ⊂ C^{1,1}_loc); "different
Hessians and jumps" SAME_AS `A/local/prose/009` (check); "Convexity ... essential" NON_CLAIM
(hypothesis emphasis; runs are only defined for convex F) — reconsider; "max of convex quadratics"
SAME_AS `A/local/prose/010`.

Section 4.5: l.320 NON_CLAIM (scope). disp/041 LEAN (γ((1-t)z) = (1-t)γ(z)); "zero radial Taylor
error" SAME_AS `A/global/prose/021`; "includes polyhedral, Euclidean, spectral, nuclear norms,
asymmetric gauges" LEAN (each sublinear: `CenteredSpectral`, `RectangularNuclear` objective_*);
disp/042 LEAN; "second derivative bounded on t ≤ 1/2" LEAN (`RadialPower.*second_derivative_bounded`);
"1<p<2 without Lipschitz gradient" LEAN (|x|^{3/2}); disp/043 + "covered" LEAN
(`AdmissibleBFGSRun.mixed_powers_convergence`, `mixed_linear_powers_convergence`; representation is
global, so no M7 omission — verify the library hypotheses); "terms need not be coercive" LEAN
(example). 4.5.2 residual decomposition LEAN (`AffineKinks.*`), local basins LEAN
(`local_absolute/hinge/quantile/kink_basin`, `FirstDifference.local_fullBFGS`), "minimizer not
required zero" PART_OF, polyhedral regularizers SAME_AS [`A/local/prose/008`,
`A/local/corollary/art:plq`], "extended-valued constraints" NON_CLAIM. 4.5.3 SAME_AS
`A/local/prose/016`; "satisfy the local condition when unique" LEAN
(`EuclideanResidual.local_euclidean_residual_basin` + local IR); "not every spectral penalty
smooth" NON_CLAIM or LEAN (nuclear norm not differentiable at diag(1,0)). 4.5.4 disp/044 LEAN
(`FiniteMaxRadial.local_finite_max_inward/_radial/_basin`), "agree in the scalar derivative" LEAN
(`maximum_hasDerivAt_of_active_agreement`), "continuous selection, common Lipschitz bound" LEAN
(`maximum_deriv_continuousOn`, `_lipschitzOn`), "J|t|+O(t²), not O(t²)" LEAN
(`finite_max_central_absolute`, `_not_isBigO`), "exact no-jump part" LEAN
(`finite_max_central_quadratic_iff`), "not necessary for BFGS convergence" SAME_AS
[`A/local/theorem/art:nonradial-example`, `A/local/disp/016`] (check).

Section 4.6: parabolic ridge disp/045 LEAN (unique minimizer 0), switching curve, gradient
difference (-2u,2), radial product -u², ray kink, disp/046 descending pair, disp/047 ratio
(u²-ε)²/(3ε) → ∞, RS fails in every neighborhood (`ParabolicRadialBoundary.*`); "not a
nonconvergent trajectory" NON_CLAIM. Spectral: disp/048 objective (`NuclearSymmetric2`), strongly
convex + unique minimizer, cancellation, disp/049 orthonormal, a = sin²θ > 0 (hypothesis
sin θ ≠ 0; note), disp/050 pair, nuclear norms differentiable, descending -4aε, y = 2(1+ε)U,
disp/051 T, N, ratio → ∞, F(W)-F(X_*) = 2a, points → X_*, RS fails at a nonzero rank-deficient
minimizer (`not_radial_secant_on_neighborhood`, `minimizer_matrix_rank`), centered nuclear norm
covered (`centered_nuclear_convergence`); "no failure claimed" NON_CLAIM.

Relation to earlier work (436-443): bibliographic sentences NON_CLAIM; "only supporting endpoint
differentiable" SAME_AS disp/004; Euclidean norm (GL18) SAME_AS `A/global/prose/037`; LO NON_CLAIM;
"wider gauge and mixed-power conclusions use the radial argument" SAME_AS the disp/043 item;
SVT: LEAN small theorem X_* = soft-threshold of C at level 1 (attribution unchecked).

## Discrepancy candidates (none confirmed yet)

- M7 parallel: so far no companion statement drops the containment (4.5.1 uses a global
  representation); still check intro l.3, 4.5.2, 4.5.3, R:thm:plq wording.
- disp/019 a = 0 case / "M_η = 8C_{η/2}" with C real (see above; likely fine, note only).
- "a = sin²θ > 0" needs sin θ ≠ 0 (read as hypothesis; note only).

## Next steps after RESUME

1. Read the remaining library modules (list above) with `lookup.py`, confirm signatures.
2. Write `Ch04R.lean` section by section, checking with
   `export PATH="$HOME/.elan/bin:$PATH"; cd bfgs_lean_article && LEAN_NUM_THREADS=4 lake env lean
   BfgsArticle/Coverage/Companion/Ch04R.lean` (one Lean process at a time; no warnings).
3. Fill `C_04_R.json` (statuses, lean names, notes, prose items `C/04_R/prose/nnn` with anchor and
   lines), discrepancies if any; run `python3 editorial/lean_coverage/check_coverage.py --strict
   --allow-discrepancies companion/chapters/04_R.tex` until exit 0; non-vacuity examples (benchmark
   `UnexcitedMetric.run`, `Global.absRun`, transformed four-piece run).
4. Final answer in the brief's format.
