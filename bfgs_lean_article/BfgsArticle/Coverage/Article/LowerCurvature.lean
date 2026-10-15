import BfgsArticle.LUniformLocal
import BfgsVerification.LReturnSpectrum
import BfgsVerification.LShapeMapDifferentiability
import BfgsVerification.LShapeSpectrum
import BfgsVerification.LScalarTargets
import BfgsVerification.LScalarPeaks
import BfgsVerification.LEmbeddingGeometryTargets
import BfgsVerification.LEmbeddingGradientBounds
import BfgsVerification.LEmbeddingSourceDetails
import BfgsVerification.LReturnStableGraph

/-!
# Lean coverage: `paper/appendices/lower_curvature.tex`

Appendix `art:lower_curvature` ("Positive lower curvature through a perturbed cycle"): the
quadratic perturbation $Q_\mu$ of the seed, Proposition `art:quadratic_failure`, the
normalized return map, Lemma `art:lower_hyperbolic` and its proof, the four-branch objective,
and the copies with one fixed whitening that prove Theorem `art:local-failure-lower`.
Register: `editorial/lean_coverage/register/A_lower_curvature.json`.

## Notation

* $g_0,g_1,g_2$ are `SeedCycle.g0`, `SeedCycle.g1`, `SeedCycle.g2 seedC seedD` (also
  `SeedOrbit.gradient seedC seedD i`), at the root $(c_\circ,d_\circ)$ =
  (`SeedOrbit.seedC`, `SeedOrbit.seedD`); $G(x)=\max_ig_i^Tx$ is
  `SeedOrbit.objective seedC seedD`, $\rho$ of `art:seed_rho` is `SeedOrbit.seedRatio`, $z_j$
  of `art:seed_points` is `SeedOrbit.point seedC seedD seedRatio j`.
* $Q_\mu$ is `LQuadraticSeed.objective μ`, its branches $\mu\|x\|^2/2+g_i^Tx$ are
  `LQuadraticSeed.branch μ i`, $\bar g$ is `LQuadraticSeed.gbar`.
* The normalized state $(z,\zeta,\eta,\tau)$ is `w : LNormalizedReturn.State = Vec 5`, with
  `point w = z`, `shape w = M(ζ,η)` and `scale w = τ`; $\mathcal T_\mu$ is
  `LNormalizedReturn.returnMap μ`, $\hat\rho$ is `LNormalizedReturn.returnFactor μ`, $P_*$ is
  `LNormalizedReturn.seed`.
* The implementation is `NonStrictLineSearch.fromMetric` (the specified search of
  `paper/sections/failure.tex:22-35`, see the module `NegativeLower` for the reading), stated
  for every trial budget `N ≥ 5` (`fromMetric_fuel_mono`); runs are `AdmissibleBFGSRun`; the
  attempted lengths of phase `j` are `trialHistory j`.
* Euclidean norms are `‖euclideanVector v‖`, squared norms `sqNorm v`.
* The four-branch construction: $\mu=1/4096$ is `LEmbedding.mu`, $c_*$ is
  `LEmbedding.center`, $q_i$ is `LEmbedding.slope i`, $b_i$ is `LEmbedding.parameter i`,
  $r=1/128$ is `LScalarGeometric.theta`, $a_\ell=r^\ell$ is `LScalarGeometric.scale ℓ`,
  $t_b$ and $\varepsilon$ are `LScalarRamp.center b` and `LScalarRamp.epsilon`, $\psi_b$ is
  `LScalar.phi b`, $f_i$ and $F$ are `LEmbedding.branch i` and `LEmbedding.objective`,
  $\bar x_\ell$ is `LEmbedding.copyCenter ℓ`, $C_*$ is `LEmbedding.offset`.

The register lists every item and the Lean names that cover it.

## Items

| Item | Lines | Lean |
|---|---|---|
| `disp/001`, `disp/002`, `disp/003` (`art:quadratic_minimizer`) | 26-39 | `quadratic_def`, `gbar_def`, `quadratic_minimizer` |
| prose `003`-`007`, `035` | 5-42 | `gbar_least_norm`, `minimizer_nonsmooth`, `common_quadratic`, `seed_not_orbit`, `quadratic_gradient_small` |
| prose `010` (corrected, M8: three of the four branches) | 11-13 | `branch_second_differentiability` |
| `proposition/art:quadratic_failure` | 44-51 | `quadratic_failure` |
| prose `036` | 53-57 | `stable_manifold_positive_scale` |
| `disp/004`-`disp/006`, prose `008`, `009`, `041`, `042` | 60-83 | `normalized_coordinates_def`, `boundary_seed_def`, `return_substep_def`, `return_map_def`, `seed_return` |
| `lemma/art:lower_hyperbolic` (with `disp/007`) | 85-96 | `lower_hyperbolic` |
| `disp/008`-`disp/011` | 112-147 | `shape_certificate`, `shape_box`, `characteristic_signs`, `return_block_form` |
| `disp/012`-`disp/017`, prose `012`-`018` | 205-247 | `embedding_constants_def`, `parameter_values`, `ramp_constants_def`, `ramp_def_bi`, `lower_scalar_def_bi`, `lower_scalar_derivatives_bi`, `lower_scalar_nodes_bi`, `lower_scalar_monotone_flat_bi`, `lower_scalar_regularity_bi`, `lower_plateau_lengths_bi`, `lower_plateau_bi`, `lower_scalar_not_twice_bi` |
| `disp/018`, `disp/019`, prose `019`-`023` | 250-278 | `lower_objective_def`, `branches_regular`, `ridge_restriction`, `branch_gradient_constants`, `lower_objective_minimizer`, `finite_max_local_taylor`, `lower_objective_hessian` |
| `disp/020`-`disp/022`, prose `025`-`033` | 282-328 | `copy_constants_def`, `lower_local_model`, `local_model_reasons`, `copy_runs`, `copy_transfer`, `copy_limits`, `whitening_setup`, `whitening_identities`, `whitening_initial`, `whitening_constants` |

The statements about $\psi_b$ are made, as in the appendix, for the two values $b=b_i$
(`b = LEmbedding.parameter i`, the theorems with suffix `_bi`); the same names without the suffix
state them for every $1.7\le b\le34$.

An `example` at the end shows that the standing assumptions can hold at once.
-/

noncomputable section
open scoped Topology BigOperators Pointwise ContDiff
open Set Filter Matrix BfgsVerification SeedOrbit SeedCycle

namespace BfgsCoverage.Article.LowerCurvature

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Helpers -/

/-- `‖euclideanVector v‖² = sqNorm v`. -/
theorem euclid_norm_sq (v : Vec 2) : ‖euclideanVector v‖ ^ 2 = sqNorm v :=
  FrameNorms.euclidean_norm_sq (euclideanVector v)

/-- A squared Euclidean Lipschitz bound gives the Euclidean Lipschitz bound. -/
theorem euclid_le_of_sqNorm_le {u v : Vec 2} {L : ℝ} (hL : 0 ≤ L)
    (h : sqNorm u ≤ L ^ 2 * sqNorm v) : ‖euclideanVector u‖ ≤ L * ‖euclideanVector v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  rw [mul_pow, euclid_norm_sq, euclid_norm_sq]
  exact h

/-- The specified search does not depend on the trial budget once it succeeds: a success
within `fuel` trials is the same success with any larger budget. -/
theorem search_fuel_mono {n : ℕ} {F : Vec n → ℝ} {x p g : Vec n} {c₁ c₂ : ℝ} :
    ∀ (fuel : ℕ) (l : ℝ) (h : Option ℝ) (a α : ℝ) (hist : List ℝ),
      NonStrictLineSearch.search F x p g c₁ c₂ fuel l h a = (some α, hist) →
      ∀ N, fuel ≤ N → NonStrictLineSearch.search F x p g c₁ c₂ N l h a = (some α, hist) := by
  intro fuel
  induction fuel with
  | zero =>
    intro l h a α hist hs
    rw [NonStrictLineSearch.search] at hs
    exact absurd hs (by simp)
  | succ fuel ih =>
    intro l h a α hist hs N hN
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [NonStrictLineSearch.search] at hs ⊢
    by_cases hA : NonStrictLineSearch.Armijo F x p g c₁ a
    · by_cases hW : NonStrictLineSearch.Wolfe F x p g c₂ a
      · simp only [hA, hW, if_true] at hs ⊢
        exact hs
      · simp only [hA, hW, if_true, if_false] at hs ⊢
        obtain ⟨h1, h2⟩ := Prod.mk_inj.mp hs
        have hr : NonStrictLineSearch.search F x p g c₁ c₂ fuel a h (NonStrictLineSearch.nextTrial a h) =
            (some α, (NonStrictLineSearch.search F x p g c₁ c₂ fuel a h
              (NonStrictLineSearch.nextTrial a h)).2) := Prod.ext h1 rfl
        rw [ih _ _ _ _ _ hr N (by omega), ← h2, ← h1]
    · simp only [hA, if_false] at hs ⊢
      obtain ⟨h1, h2⟩ := Prod.mk_inj.mp hs
      have hr : NonStrictLineSearch.search F x p g c₁ c₂ fuel l (some a)
          (NonStrictLineSearch.nextTrial l (some a)) =
          (some α, (NonStrictLineSearch.search F x p g c₁ c₂ fuel l (some a)
            (NonStrictLineSearch.nextTrial l (some a))).2) := Prod.ext h1 rfl
      rw [ih _ _ _ _ _ hr N (by omega), ← h2, ← h1]

/-- `fromMetric` with any budget at least `fuel` returns a success obtained within `fuel`. -/
theorem fromMetric_fuel_mono {n : ℕ} {F : Vec n → ℝ} {x : Vec n} {H : Mat n} {c₁ c₂ : ℝ}
    {fuel : ℕ} {α : ℝ} {hist : List ℝ}
    (hs : NonStrictLineSearch.fromMetric F x H c₁ c₂ fuel = (some α, hist)) (N : ℕ) (hN : fuel ≤ N) :
    NonStrictLineSearch.fromMetric F x H c₁ c₂ N = (some α, hist) :=
  search_fuel_mono fuel 0 none 1 α hist hs N hN

/-! ### The strongly convex global example -/

/-- $G(x)=\max_ig_i^Tx$. -/
theorem seed_objective_eq_max (x : Vec 2) :
    SeedOrbit.objective seedC seedD x = max (max (dot g0 x) (dot g1 x)) (dot (g2 seedC seedD) x) := by
  apply le_antisymm
  · apply LQuadraticSeed.seed_objective_le
    intro i
    fin_cases i
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact le_max_right _ _
  · refine max_le (max_le ?_ ?_) ?_
    · exact LQuadraticSeed.seed_branch_le 0 x
    · exact LQuadraticSeed.seed_branch_le 1 x
    · exact LQuadraticSeed.seed_branch_le 2 x

/-- Item `A/lower_curvature/disp/001` (`paper/appendices/lower_curvature.tex:27-29`): "Use the
slopes $g_0,g_1,g_2$ and the function $G$ of Section~\ref{art:failure} and let
\[ Q_\mu(x)=\tfrac\mu2\|x\|^2+G(x),\qquad\mu>0." \]
`LQuadraticSeed.objective μ` is $Q_\mu$, with $G(x)=\max\{g_0^Tx,g_1^Tx,g_2^Tx\}$. -/
theorem quadratic_def (μ : ℝ) (x : Vec 2) :
    LQuadraticSeed.objective μ x = μ / 2 * sqNorm x + SeedOrbit.objective seedC seedD x ∧
      SeedOrbit.objective seedC seedD x =
        max (max (dot g0 x) (dot g1 x)) (dot (g2 seedC seedD) x) :=
  ⟨rfl, seed_objective_eq_max x⟩

/-- Item `A/lower_curvature/disp/002` (`paper/appendices/lower_curvature.tex:31-34`):
\[ \bar g=\frac{(1,-16)^T}{257}=\frac{129}{257}g_0+\frac{128}{257}g_1. \] -/
theorem gbar_def :
    LQuadraticSeed.gbar = (1 / 257 : ℝ) • ![1, -16] ∧
      LQuadraticSeed.gbar = (129 / 257 : ℝ) • g0 + (128 / 257 : ℝ) • g1 := by
  refine ⟨?_, LQuadraticSeed.gbar_weights⟩
  ext i
  fin_cases i <;> norm_num [LQuadraticSeed.gbar]

/-- The slopes $\{g_0,g_1,g_2\}$ are the library's `LQuadraticSeed.slopes`. -/
theorem slopes_eq : LQuadraticSeed.slopes = {g0, g1, g2 seedC seedD} := by
  ext g
  simp only [LQuadraticSeed.slopes, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [SeedOrbit.gradient]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- Item `A/lower_curvature/prose/003` (`paper/appendices/lower_curvature.tex:35-37`): "[$\bar g$]
is the least-norm point of $\operatorname{conv}\{g_0,g_1,g_2\}$:
$g_0^T\bar g=g_1^T\bar g=\|\bar g\|^2=1/257$, whereas $g_2^T\bar g>1/257$." Least norm in the
Euclidean norm, and the only point of least norm. -/
theorem gbar_least_norm :
    LQuadraticSeed.gbar ∈ convexHull ℝ {g0, g1, g2 seedC seedD} ∧
      (∀ g ∈ convexHull ℝ {g0, g1, g2 seedC seedD},
        ‖euclideanVector LQuadraticSeed.gbar‖ ≤ ‖euclideanVector g‖) ∧
      (∀ g ∈ convexHull ℝ {g0, g1, g2 seedC seedD},
        ‖euclideanVector g‖ = ‖euclideanVector LQuadraticSeed.gbar‖ → g = LQuadraticSeed.gbar) ∧
      dot g0 LQuadraticSeed.gbar = 1 / 257 ∧ dot g1 LQuadraticSeed.gbar = 1 / 257 ∧
      sqNorm LQuadraticSeed.gbar = 1 / 257 ∧ 1 / 257 < dot (g2 seedC seedD) LQuadraticSeed.gbar := by
  rw [← slopes_eq]
  refine ⟨LQuadraticSeed.gbar_mem_convexHull, fun g hg => LQuadraticSeed.gbar_least_norm hg,
    fun g hg he => ?_, LQuadraticSeed.gbar_dot_first.1, LQuadraticSeed.gbar_dot_first.2,
    LQuadraticSeed.gbar_sqNorm, LQuadraticSeed.gbar_dot_third⟩
  apply LQuadraticSeed.gbar_unique_least_sqNorm hg
  have h1 := FrameNorms.euclidean_norm_sq (euclideanVector g)
  have h2 := FrameNorms.euclidean_norm_sq (euclideanVector LQuadraticSeed.gbar)
  change ‖euclideanVector g‖ ^ 2 = sqNorm g at h1
  change ‖euclideanVector LQuadraticSeed.gbar‖ ^ 2 = sqNorm LQuadraticSeed.gbar at h2
  rw [← h1, ← h2, he]

/-- Item `A/lower_curvature/disp/003`, equation `art:quadratic_minimizer`
(`paper/appendices/lower_curvature.tex:38-40`): "Therefore the unique minimizer is
\[ x_*=-\bar g/\mu,\qquad \min Q_\mu=-1/(514\mu)." \] -/
theorem quadratic_minimizer (μ : ℝ) (hμ : 0 < μ) (xs : Vec 2) (hxs : xs = -(μ⁻¹ • LQuadraticSeed.gbar)) :
    (∀ x, LQuadraticSeed.objective μ xs ≤ LQuadraticSeed.objective μ x) ∧
      (∀ x, LQuadraticSeed.objective μ x = LQuadraticSeed.objective μ xs → x = xs) ∧
      LQuadraticSeed.objective μ xs = -1 / (514 * μ) := by
  have he : xs = LQuadraticSeed.minimizer μ := by
    rw [hxs, LQuadraticSeed.minimizer, neg_smul]
  subst he
  exact ⟨LQuadraticSeed.objective_minimum hμ, fun x hx => LQuadraticSeed.objective_unique_minimum hμ hx,
    LQuadraticSeed.minimizer_value hμ⟩

/-- Item `A/lower_curvature/prose/004` (`paper/appendices/lower_curvature.tex:41-43`): "At $x_*$
the first two branches tie with distinct gradients, so the minimizer is nonsmooth. At zero the
subdifferential is the nonstationary triangle of the original seed." The branches of $Q_\mu$ are
$\mu\|x\|^2/2+g_i^Tx$ with gradients $\mu x+g_i$. -/
theorem minimizer_nonsmooth (μ : ℝ) (hμ : 0 < μ) (xs : Vec 2) (hxs : xs = -(μ⁻¹ • LQuadraticSeed.gbar)) :
    (∀ i, LQuadraticSeed.branch μ i xs = LQuadraticSeed.objective μ xs ↔ i = 0 ∨ i = 1) ∧
      LQuadraticSeed.branchGradient μ xs 0 ≠ LQuadraticSeed.branchGradient μ xs 1 ∧
      ¬ DifferentiableAt ℝ (LQuadraticSeed.objective μ) xs ∧
      ConvexSubdifferential.subdifferential (LQuadraticSeed.objective μ) 0 =
        convexHull ℝ {g0, g1, g2 seedC seedD} ∧
      (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential (LQuadraticSeed.objective μ) 0 := by
  have he : xs = LQuadraticSeed.minimizer μ := by
    rw [hxs, LQuadraticSeed.minimizer, neg_smul]
  subst he
  refine ⟨LQuadraticSeed.minimizer_active_iff hμ, ?_, LQuadraticSeed.minimizer_not_differentiable hμ,
    by rw [LQuadraticSeed.origin_subdifferential hμ.le, slopes_eq],
    LQuadraticSeed.origin_nonstationary hμ.le⟩
  intro h
  have h0 := congrFun h 0
  norm_num [LQuadraticSeed.branchGradient, SeedOrbit.gradient, g0, g1] at h0

/-- Item `A/lower_curvature/prose/005` (`paper/appendices/lower_curvature.tex:19-20`): "A common
positive quadratic leaves the active-branch geometry unchanged and makes every sublevel
compact." A branch of $Q_\mu$ is active exactly when the same branch of $G$ is active. -/
theorem common_quadratic (μ : ℝ) (hμ : 0 < μ) :
    (∀ (i : Fin 3) (x : Vec 2), LQuadraticSeed.branch μ i x = LQuadraticSeed.objective μ x ↔
      dot (SeedOrbit.gradient seedC seedD i) x = SeedOrbit.objective seedC seedD x) ∧
      ∀ a : ℝ, IsCompact {x | LQuadraticSeed.objective μ x ≤ a} := by
  refine ⟨fun i x => ?_, LQuadraticSeed.objective_sublevels_compact hμ⟩
  change LQuadraticSeed.quadratic μ x + _ = LQuadraticSeed.quadratic μ x + _ ↔ _
  exact add_right_inj _

/-- The second coordinate of $z_0$ is negative. -/
theorem seed_point_second_neg : SeedOrbit.point seedC seedD seedRatio 0 1 < 0 := by
  have hr := source_ratio_pos_lt_one
  have hd := root_tight_box.2
  change (seedRatio * seedD - 1 / 64) / (1 - seedRatio) < 0
  apply div_neg_of_neg_of_pos
  · have : seedRatio * seedD < 0 := mul_neg_of_pos_of_neg hr.1 (by linarith [hd.2])
    linarith
  · linarith [hr.2]

/-- Item `A/lower_curvature/prose/006` (`paper/appendices/lower_curvature.tex:5-6`), with prose
item `A/lower_curvature/prose/035` (lines 20-21): "Adding a positive quadratic changes the seed
orbit, so exact homogeneity alone no longer supplies a trajectory." / "It perturbs the
gradients, however, so the homogeneous seed is no longer an exact orbit." For $\mu>0$ no
full-BFGS run on $Q_\mu$ from the seed state $(z_0,I)$ has $z_1$ as its next iterate. -/
theorem seed_not_orbit (μ : ℝ) (hμ : 0 < μ) (R : AdmissibleBFGSRun 2 (LQuadraticSeed.objective μ))
    (hx : R.x 0 = SeedOrbit.point seedC seedD seedRatio 0) (hH : R.H 0 = 1) :
    R.x 1 ≠ SeedOrbit.point seedC seedD seedRatio 1 := by
  intro h1
  have hact := (source_base_certificate 0).active
  have hg : R.g 0 = LQuadraticSeed.branchGradient μ (SeedOrbit.point seedC seedD seedRatio 0) 0 := by
    have h := R.hasGradient 0
    rw [hx] at h
    rw [← DeterministicLineSearch.actual_coordinateGradient h,
      DeterministicLineSearch.actual_coordinateGradient
        (LNormalizedOracle.objective_hasGradient_of_active μ hact)]
  have hstep := R.step 0
  rw [h1, hx, hH, hg] at hstep
  have h2 := congrFun hstep 1
  have hz := seed_point_second_neg
  have hα := R.alpha_pos 0
  have e1 : (SeedOrbit.point seedC seedD seedRatio 1) 1 = (SeedOrbit.point seedC seedD seedRatio 0) 1 := by
    simp [SeedOrbit.point]
    rfl
  have e2 : (bfgsStep (1 : Mat 2) (LQuadraticSeed.branchGradient μ (SeedOrbit.point seedC seedD seedRatio 0) 0)
      (R.α 0)) 1 = -(R.α 0 * (μ * (SeedOrbit.point seedC seedD seedRatio 0) 1)) := by
    simp [bfgsStep, LQuadraticSeed.branchGradient, SeedOrbit.gradient, g0]
    left
    rfl
  rw [Pi.add_apply, e1, e2] at h2
  have h3 : R.α 0 * (μ * SeedOrbit.point seedC seedD seedRatio 0 1) = 0 := by linarith
  exact mul_ne_zero hα.ne' (mul_ne_zero hμ.ne' hz.ne) h3

/-- Item `A/lower_curvature/prose/007` (`paper/appendices/lower_curvature.tex:21-22`): "Close to
the corner, the quadratic gradient is small relative to the fixed slopes." Near zero
$\|\mu x\|\le\varepsilon\|g_i\|$ for every slope, for any $\varepsilon>0$. -/
theorem quadratic_gradient_small (μ : ℝ) (hμ : 0 < μ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 (0 : Vec 2), ∀ i : Fin 3,
      ‖euclideanVector (μ • x)‖ ≤ ε * ‖euclideanVector (SeedOrbit.gradient seedC seedD i)‖ := by
  have hone (i : Fin 3) : 1 ≤ ‖euclideanVector (SeedOrbit.gradient seedC seedD i)‖ := by
    have he := FrameNorms.euclidean_norm_sq (euclideanVector (SeedOrbit.gradient seedC seedD i))
    change ‖euclideanVector (SeedOrbit.gradient seedC seedD i)‖ ^ 2 =
      sqNorm (SeedOrbit.gradient seedC seedD i) at he
    have hsq : 1 ≤ sqNorm (SeedOrbit.gradient seedC seedD i) := by
      have hd := root_tight_box.2
      fin_cases i
      · norm_num [sqNorm, SeedOrbit.gradient, g0, Fin.sum_univ_two]
      · norm_num [sqNorm, SeedOrbit.gradient, g1, Fin.sum_univ_two]
      · simp only [sqNorm, SeedOrbit.gradient, g2, Fin.sum_univ_two]
        simp
        obtain ⟨hd1, hd2⟩ := hd
        nlinarith [sq_nonneg seedC]
    nlinarith [norm_nonneg (euclideanVector (SeedOrbit.gradient seedC seedD i))]
  have hc : Continuous fun x : Vec 2 => ‖euclideanVector x‖ :=
    (PiLp.continuous_equiv_symm 2 _).norm
  have hlt : ∀ᶠ x in 𝓝 (0 : Vec 2), ‖euclideanVector x‖ < ε / μ := by
    apply hc.continuousAt.eventually (gt_mem_nhds _)
    change ‖euclideanVector (0 : Vec 2)‖ < ε / μ
    rw [show euclideanVector (0 : Vec 2) = 0 from rfl, norm_zero]
    positivity
  filter_upwards [hlt] with x hx i
  rw [show euclideanVector (μ • x) = μ • euclideanVector x from rfl, norm_smul, Real.norm_eq_abs,
    abs_of_pos hμ]
  have h1 := hone i
  have h2 : μ * ‖euclideanVector x‖ < ε := by
    rw [lt_div_iff₀ hμ] at hx
    linarith
  nlinarith [norm_nonneg (euclideanVector x)]

/-! ### Proposition `art:quadratic_failure` -/

/-- Item `A/lower_curvature/proposition/art:quadratic_failure`, Proposition
`art:quadratic_failure` (`paper/appendices/lower_curvature.tex:45-52`), as printed before the
correction of 15 October 2026 (M33, reader point R-F-1), which added the initial point to the
last sentence; the corrected proposition is `quadratic_failure_initial_point`.

"Let $\mu>0$. For every neighborhood $V$ of zero, some initial state $(x_0,H_0)$, $H_0\succ0$,
produces for every fixed pair $0<c_1\le1/3$, $c_1<c_2<1$ the same deterministic full-BFGS run on
$Q_\mu$, converging to zero with positive objective values decreasing to zero. Its accepted
lengths repeat $1,1/4,1/16$, and all accepted and rejected query points are differentiable and
belong to $V$."

The initial state and the run (`x`, `H`) are chosen before the pair; for every admissible pair
the implementation's run from $(x_0,H_0)$ has exactly these iterates and matrices. The queries at
step `k` are `x k + a • bfgsStep (H k) (∇Q_μ(x k)) 1` for the attempted lengths `a` of the
search, which are `trialHistory (phase k)` for every pair. -/
theorem quadratic_failure (μ : ℝ) (hμ : 0 < μ) (V : Set (Vec 2)) (hV : V ∈ 𝓝 (0 : Vec 2)) :
    ∃ (x₀ : Vec 2) (H₀ : Mat 2), H₀.PosDef ∧
      ∃ (x : ℕ → Vec 2) (H : ℕ → Mat 2), x 0 = x₀ ∧ H 0 = H₀ ∧
        Tendsto x atTop (𝓝 0) ∧ (∀ k, 0 < LQuadraticSeed.objective μ (x k)) ∧
        StrictAnti (fun k => LQuadraticSeed.objective μ (x k)) ∧
        Tendsto (fun k => LQuadraticSeed.objective μ (x k)) atTop (𝓝 0) ∧
        (∀ k, ∀ a ∈ trialHistory (phase k),
          DifferentiableAt ℝ (LQuadraticSeed.objective μ)
            (x k + a • bfgsStep (H k) (coordinateGradient (LQuadraticSeed.objective μ) (x k)) 1) ∧
          x k + a • bfgsStep (H k) (coordinateGradient (LQuadraticSeed.objective μ) (x k)) 1 ∈ V) ∧
        ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
          ∃ R : AdmissibleBFGSRun 2 (LQuadraticSeed.objective μ),
            R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ R.x = x ∧ R.H = H ∧
            (∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric (LQuadraticSeed.objective μ) (R.x k) (R.H k)
              c₁ c₂ N = (some (R.α k), trialHistory (phase k))) ∧
            ∀ m, R.α (3 * m) = 1 ∧ R.α (3 * m + 1) = 1/4 ∧ R.α (3 * m + 2) = 1/16 := by
  obtain ⟨x, H, hH0, hruns⟩ := LUniform.uniform_global_failure hμ V hV
  obtain ⟨R₀, hx, hH, -, -, hxlim, -, hvlim, hpos, hdec, -, -, -, -, hq, -, -, -⟩ :=
    hruns (1/10000) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgrad (k : ℕ) : coordinateGradient (LQuadraticSeed.objective μ) (x k) = R₀.g k := by
    rw [← hx]
    exact DeterministicLineSearch.actual_coordinateGradient (R₀.hasGradient k)
  refine ⟨x 0, H 0, hH0, x, H, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hx]; exact hxlim
  · intro k; rw [← hx]; exact hpos k
  · rw [← hx]; exact strictAnti_nat_of_succ_lt hdec
  · rw [← hx]; exact hvlim
  · intro k a ha
    obtain ⟨q, hqk, rfl⟩ := trial_history_witness (phase k) ha
    obtain ⟨h1, -, h3⟩ := hq k q hqk
    rw [hx, hH] at h1 h3
    rw [hgrad k]
    exact ⟨h1, h3⟩
  · intro c₁ c₂ hc₁ hc₁' hc hc₂
    obtain ⟨R, hRx, hRH, hRc₁, hRc₂, -, -, -, -, -, hα, hsearch, -⟩ := hruns c₁ c₂ hc₁ hc₁' hc hc₂
    refine ⟨R, hRc₁, hRc₂, hRx, hRH, fun k N hN => fromMetric_fuel_mono (hsearch k) N hN,
      fun m => ⟨?_, ?_, ?_⟩⟩
    · rw [hα]; simp [phase, SeedOrbit.length, Nat.mul_mod_right]
    · rw [hα]
      have : (3 * m + 1) % 3 = 1 := by omega
      simp [phase, SeedOrbit.length, this]
    · rw [hα]
      have : (3 * m + 2) % 3 = 2 := by omega
      simp [phase, SeedOrbit.length, this]

/-- Item `A/lower_curvature/proposition/art:quadratic_failure`, Proposition
`art:quadratic_failure` (`paper/appendices/lower_curvature.tex:45-52`), as corrected on
15 October 2026 (M33, reader point R-F-1).

"Let $\mu>0$. For every neighborhood $V$ of zero, some initial state $(x_0,H_0)$, $H_0\succ0$,
produces for every fixed pair ${0<c_1\le1/3}$, $c_1<c_2<1$ the same deterministic full-BFGS run
on $Q_\mu$, converging to zero with positive objective values decreasing to zero. Its accepted
lengths repeat $1,1/4,1/16$, and its initial point and all accepted and rejected query points
are differentiable and belong to $V$."

As `quadratic_failure`, with the initial point: $Q_\mu$ is differentiable at $x_0$ and
$x_0\in V$ (the start of copy $\ell$ in Section D.3 needs the local model there). -/
theorem quadratic_failure_initial_point (μ : ℝ) (hμ : 0 < μ) (V : Set (Vec 2))
    (hV : V ∈ 𝓝 (0 : Vec 2)) :
    ∃ (x₀ : Vec 2) (H₀ : Mat 2), H₀.PosDef ∧
      ∃ (x : ℕ → Vec 2) (H : ℕ → Mat 2), x 0 = x₀ ∧ H 0 = H₀ ∧
        Tendsto x atTop (𝓝 0) ∧ (∀ k, 0 < LQuadraticSeed.objective μ (x k)) ∧
        StrictAnti (fun k => LQuadraticSeed.objective μ (x k)) ∧
        Tendsto (fun k => LQuadraticSeed.objective μ (x k)) atTop (𝓝 0) ∧
        (DifferentiableAt ℝ (LQuadraticSeed.objective μ) x₀ ∧ x₀ ∈ V) ∧
        (∀ k, ∀ a ∈ trialHistory (phase k),
          DifferentiableAt ℝ (LQuadraticSeed.objective μ)
            (x k + a • bfgsStep (H k) (coordinateGradient (LQuadraticSeed.objective μ) (x k)) 1) ∧
          x k + a • bfgsStep (H k) (coordinateGradient (LQuadraticSeed.objective μ) (x k)) 1 ∈ V) ∧
        ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
          ∃ R : AdmissibleBFGSRun 2 (LQuadraticSeed.objective μ),
            R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ R.x = x ∧ R.H = H ∧
            (∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric (LQuadraticSeed.objective μ) (R.x k) (R.H k)
              c₁ c₂ N = (some (R.α k), trialHistory (phase k))) ∧
            ∀ m, R.α (3 * m) = 1 ∧ R.α (3 * m + 1) = 1/4 ∧ R.α (3 * m + 2) = 1/16 := by
  obtain ⟨x, H, hH0, hruns⟩ := LUniform.uniform_global_failure hμ V hV
  obtain ⟨R₀, hx, hH, -, -, hxlim, -, hvlim, hpos, hdec, -, -, -, hxV, hq, -, -, -⟩ :=
    hruns (1/10000) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgrad (k : ℕ) : coordinateGradient (LQuadraticSeed.objective μ) (x k) = R₀.g k := by
    rw [← hx]
    exact DeterministicLineSearch.actual_coordinateGradient (R₀.hasGradient k)
  refine ⟨x 0, H 0, hH0, x, H, rfl, rfl, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← hx]; exact hxlim
  · intro k; rw [← hx]; exact hpos k
  · rw [← hx]; exact strictAnti_nat_of_succ_lt hdec
  · rw [← hx]; exact hvlim
  · rw [← hx]; exact (R₀.hasGradient 0).differentiableAt
  · rw [← hx]; exact hxV 0
  · intro k a ha
    obtain ⟨q, hqk, rfl⟩ := trial_history_witness (phase k) ha
    obtain ⟨h1, -, h3⟩ := hq k q hqk
    rw [hx, hH] at h1 h3
    rw [hgrad k]
    exact ⟨h1, h3⟩
  · intro c₁ c₂ hc₁ hc₁' hc hc₂
    obtain ⟨R, hRx, hRH, hRc₁, hRc₂, -, -, -, -, -, hα, hsearch, -⟩ := hruns c₁ c₂ hc₁ hc₁' hc hc₂
    refine ⟨R, hRc₁, hRc₂, hRx, hRH, fun k N hN => fromMetric_fuel_mono (hsearch k) N hN,
      fun m => ⟨?_, ?_, ?_⟩⟩
    · rw [hα]; simp [phase, SeedOrbit.length, Nat.mul_mod_right]
    · rw [hα]
      have : (3 * m + 1) % 3 = 1 := by omega
      simp [phase, SeedOrbit.length, this]
    · rw [hα]
      have : (3 * m + 2) % 3 = 2 := by omega
      simp [phase, SeedOrbit.length, this]

/-! ### The normalized three-step return map -/

/-- Item `A/lower_curvature/disp/004` (`paper/appendices/lower_curvature.tex:61-64`): the
normalized coordinates
\[ x=\tau z,\qquad H=\tau M(\zeta,\eta),\qquad
   M(\zeta,\eta)=\begin{pmatrix}1&\zeta\\\zeta&\eta\end{pmatrix},\qquad\tau>0. \]
A state `w = (z₁, z₂, ζ, η, τ)` has `point w = z`, `shape w = M(ζ,η)`, `scale w = τ`; its
physical point and matrix (`LNormalizedOracle.physicalPoint`, `physicalMetric`, phase `0`) are
$\tau z$ and $\tau M(\zeta,\eta)$. -/
theorem normalized_coordinates_def (μ : ℝ) (w : LNormalizedReturn.State) :
    LNormalizedReturn.shape w = !![1, w 2; w 2, w 3] ∧ LNormalizedReturn.point w = ![w 0, w 1] ∧
      LNormalizedReturn.scale w = w 4 ∧
      LNormalizedOracle.physicalPoint μ w 0 = LNormalizedReturn.scale w • LNormalizedReturn.point w ∧
      LNormalizedOracle.physicalMetric μ w 0 = LNormalizedReturn.scale w • LNormalizedReturn.shape w :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Item `A/lower_curvature/prose/008` (`paper/appendices/lower_curvature.tex:65`): "The boundary
seed is $P_*=(z_0,0,1,0)$ in coordinates $(z,\zeta,\eta,\tau)$." -/
theorem boundary_seed_def :
    LNormalizedReturn.seed = ![SeedOrbit.point seedC seedD seedRatio 0 0,
      SeedOrbit.point seedC seedD seedRatio 0 1, 0, 1, 0] ∧
      LNormalizedReturn.point LNormalizedReturn.seed = SeedOrbit.point seedC seedD seedRatio 0 ∧
      LNormalizedReturn.shape LNormalizedReturn.seed = 1 ∧ LNormalizedReturn.scale LNormalizedReturn.seed = 0 :=
  ⟨rfl, LNormalizedReturn.seed_point, LNormalizedReturn.seed_shape, LNormalizedReturn.seed_scale⟩

/-- Item `A/lower_curvature/disp/005`, equation `art:lower_return_substep`
(`paper/appendices/lower_curvature.tex:68-74`), with lines 66-67 and 75: "Keep the input $\tau$
fixed during three substeps. Starting with $(Z,M)=(z,M(\zeta,\eta))$, for $j=0,1,2$ perform
\[ \gamma_j=g_j+\mu\tau Z,\quad S=-\alpha_jM\gamma_j,\quad Z^+=Z+S,\quad
   Y=g_{j+1}-g_j+\mu\tau S, \]
\[ M^+=\left(I-\frac{SY^T}{Y^TS}\right)M\left(I-\frac{YS^T}{Y^TS}\right)+\frac{SS^T}{Y^TS}, \]
with cyclic gradient indices and $\alpha=(1,1/4,1/16)$." The library substep is this map, the
indices are `nextPhase = ![1,2,0]`, the lengths `SeedOrbit.length = ![1,1/4,1/16]`, and
`LNormalizedReturn.internal μ w k` is the state after `k` substeps at the fixed input scale. -/
theorem return_substep_def (μ τ : ℝ) (j : Fin 3) (Z : Vec 2) (M : Mat 2) (γ S Y : Vec 2)
    (hγ : γ = SeedOrbit.gradient seedC seedD j + (μ * τ) • Z)
    (hS : S = -(SeedOrbit.length j) • (M *ᵥ γ))
    (hY : Y = SeedOrbit.gradient seedC seedD (nextPhase j) - SeedOrbit.gradient seedC seedD j +
      (μ * τ) • S) :
    LNormalizedReturn.substep μ τ j (Z, M) =
        (Z + S, (1 - (dot Y S)⁻¹ • outer S Y) * M * (1 - (dot Y S)⁻¹ • outer Y S) +
          (dot Y S)⁻¹ • outer S S) ∧
      nextPhase = ![1, 2, 0] ∧ SeedOrbit.length = ![1, 1/4, 1/16] ∧
      ∀ w : LNormalizedReturn.State,
        LNormalizedReturn.internal μ w 0 = (LNormalizedReturn.point w, LNormalizedReturn.shape w) ∧
        ∀ k, LNormalizedReturn.internal μ w (k + 1) =
          LNormalizedReturn.substep μ (LNormalizedReturn.scale w) (phase k)
            (LNormalizedReturn.internal μ w k) := by
  subst hγ hS hY
  exact ⟨rfl, rfl, rfl, fun w => ⟨rfl, fun k => rfl⟩⟩

/-- Item `A/lower_curvature/disp/006`, equation `art:lower_return`
(`paper/appendices/lower_curvature.tex:77-80`), with line 76: "For the resulting $(Z_3,M_3)$, let
$\hat\rho=(M_3)_{11}$ and define
\[ \mathcal T_\mu(z,\zeta,\eta,\tau)=\left(Z_3/\hat\rho,(M_3)_{12}/\hat\rho,(M_3)_{22}/\hat\rho,
   \tau\hat\rho\right)." \] -/
theorem return_map_def (μ : ℝ) (w : LNormalizedReturn.State) :
    LNormalizedReturn.returnFactor μ w = (LNormalizedReturn.internal μ w 3).2 0 0 ∧
      LNormalizedReturn.returnMap μ w =
        ![(LNormalizedReturn.internal μ w 3).1 0 / LNormalizedReturn.returnFactor μ w,
          (LNormalizedReturn.internal μ w 3).1 1 / LNormalizedReturn.returnFactor μ w,
          (LNormalizedReturn.internal μ w 3).2 0 1 / LNormalizedReturn.returnFactor μ w,
          (LNormalizedReturn.internal μ w 3).2 1 1 / LNormalizedReturn.returnFactor μ w,
          LNormalizedReturn.scale w * LNormalizedReturn.returnFactor μ w] :=
  ⟨rfl, rfl⟩

/-- Item `A/lower_curvature/prose/009` (`paper/appendices/lower_curvature.tex:81-84`): "The seed
closure gives $\mathcal T_\mu(P_*)=P_*$ and $\hat\rho(P_*)=\rho$. All denominators are nonzero
there. Hence the map is real analytic on an open neighborhood of $P_*$, using negative $\tau$ only
to define this analytic extension." The denominators are the three curvatures $Y^TS$ and
$\hat\rho$; the open neighborhood contains states with $\tau<0$. -/
theorem seed_return (μ : ℝ) :
    LNormalizedReturn.returnMap μ LNormalizedReturn.seed = LNormalizedReturn.seed ∧
      LNormalizedReturn.returnFactor μ LNormalizedReturn.seed = seedRatio ∧
      (∀ j, 0 < LNormalizedReturn.denominator μ LNormalizedReturn.seed j) ∧
      0 < LNormalizedReturn.returnFactor μ LNormalizedReturn.seed ∧
      ∃ U : Set LNormalizedReturn.State, IsOpen U ∧ LNormalizedReturn.seed ∈ U ∧
        AnalyticOnNhd ℝ (LNormalizedReturn.returnMap μ) U ∧
        ∃ w ∈ U, LNormalizedReturn.scale w < 0 := by
  obtain ⟨U, hUo, hsU, -, han⟩ := LNormalizedReturn.regular_analytic_neighborhood μ
  refine ⟨LNormalizedReturn.seed_fixed μ, LNormalizedReturn.seed_returnFactor μ,
    LNormalizedReturn.seed_denominator_positive μ, (LNormalizedReturn.seed_regular μ).2.1,
    U, hUo, hsU, han, ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo _ hsU
  let e4 : LNormalizedReturn.State := Pi.single (4 : Fin 5) (1 : ℝ)
  let w : LNormalizedReturn.State := LNormalizedReturn.seed - (ε / 2) • e4
  have he4 : ‖e4‖ = 1 := by simp [e4, Pi.norm_single]
  refine ⟨w, hball ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have : w - LNormalizedReturn.seed = -((ε / 2) • e4) := by
      simp only [w]; abel
    rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), he4]
    linarith
  · have : LNormalizedReturn.scale w = 0 - ε / 2 := by
      change LNormalizedReturn.seed 4 - (ε / 2) * e4 4 = 0 - ε / 2
      simp [e4]
      rfl
    rw [this]
    linarith

/-! ### Lemma `art:lower_hyperbolic` -/

/-- The stable subspace of a linear endomorphism of the state space: the sum of its generalized
eigenspaces for the real eigenvalues of modulus less than one. -/
def stableSubspace (L : Module.End ℝ LNormalizedReturn.State) : Submodule ℝ LNormalizedReturn.State :=
  ⨆ (t : ℝ) (_ : |t| < 1), L.maxGenEigenspace t

/-- Item `A/lower_curvature/lemma/art:lower_hyperbolic`, Lemma `art:lower_hyperbolic`
(`paper/appendices/lower_curvature.tex:86-97`), including its display
`A/lower_curvature/disp/007` (lines 92-95).

"On a sufficiently small neighborhood of $P_*$, positive-$\tau$ states follow exactly the three
query lists of Table~\ref{art:trial_table} under the actual algorithm for every admissible pair
$(c_1,c_2)$, and \eqref{art:lower_return} is their return map. Its derivative at $P_*$ has
eigenvalues
\[ \rho^{-1},\quad\rho^{-1},\quad\lambda_s,\quad\lambda_u,\quad\rho,\qquad
   0.038<\lambda_s<0.039,\quad1.564<\lambda_u<1.565. \]
The stable eigenspace contains a vector whose $\tau$ coordinate is one."

Reading. From a state `w` with $\tau>0$ the actual algorithm starts at $x_0=\tau z$,
$H_0=\tau M(\zeta,\eta)$ (`x 0`, `H 0`); at each of the three steps the matrix is positive
definite, the point and every query are differentiable, the point and every query have the
table's unique active branch (of $Q_\mu$), the search's attempted lengths are the table's list
`trialHistory j` with accepted length $\alpha_j$, and the next point and matrix are the
full-BFGS step and update with actual gradients. The return map: $x_3=\tau'z'$ and
$H_3=\tau'M(\zeta',\eta')$ for $(z',\zeta',\eta',\tau')=\mathcal T_\mu(w)$. The eigenvalues
(with algebraic multiplicity) are stated as the factorization of the characteristic polynomial
of $D\mathcal T_\mu(P_*)$. The stable eigenspace is `stableSubspace`. -/
theorem lower_hyperbolic (μ : ℝ) (_hμ : 0 < μ) :
    (∃ N ∈ 𝓝 LNormalizedReturn.seed, ∀ w ∈ N, 0 < LNormalizedReturn.scale w →
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
        ∃ (x : Fin 4 → Vec 2) (H : Fin 4 → Mat 2),
          x 0 = LNormalizedReturn.scale w • LNormalizedReturn.point w ∧
          H 0 = LNormalizedReturn.scale w • LNormalizedReturn.shape w ∧
          (∀ j : Fin 3, (H j.castSucc).PosDef ∧
            DifferentiableAt ℝ (LQuadraticSeed.objective μ) (x j.castSucc) ∧
            (∀ k, k ≠ j → LQuadraticSeed.branch μ k (x j.castSucc) <
              LQuadraticSeed.branch μ j (x j.castSucc)) ∧
            (∀ q : Fin 9, trialPhase q = j → ∀ k, k ≠ trialActive q →
              LQuadraticSeed.branch μ k (x j.castSucc + trialLength q • bfgsStep (H j.castSucc)
                (coordinateGradient (LQuadraticSeed.objective μ) (x j.castSucc)) 1) <
              LQuadraticSeed.branch μ (trialActive q) (x j.castSucc + trialLength q • bfgsStep (H j.castSucc)
                (coordinateGradient (LQuadraticSeed.objective μ) (x j.castSucc)) 1)) ∧
            (∀ N, 5 ≤ N → NonStrictLineSearch.fromMetric (LQuadraticSeed.objective μ) (x j.castSucc)
              (H j.castSucc) c₁ c₂ N = (some (SeedOrbit.length j), trialHistory j)) ∧
            (∀ a ∈ trialHistory j, DifferentiableAt ℝ (LQuadraticSeed.objective μ)
              (x j.castSucc + a • bfgsStep (H j.castSucc)
                (coordinateGradient (LQuadraticSeed.objective μ) (x j.castSucc)) 1)) ∧
            x j.succ = x j.castSucc + bfgsStep (H j.castSucc)
              (coordinateGradient (LQuadraticSeed.objective μ) (x j.castSucc)) (SeedOrbit.length j) ∧
            H j.succ = inverseBFGS (H j.castSucc) (x j.succ - x j.castSucc)
              (coordinateGradient (LQuadraticSeed.objective μ) (x j.succ) -
                coordinateGradient (LQuadraticSeed.objective μ) (x j.castSucc))) ∧
          x 3 = LNormalizedReturn.scale (LNormalizedReturn.returnMap μ w) •
            LNormalizedReturn.point (LNormalizedReturn.returnMap μ w) ∧
          H 3 = LNormalizedReturn.scale (LNormalizedReturn.returnMap μ w) •
            LNormalizedReturn.shape (LNormalizedReturn.returnMap μ w)) ∧
      (∃ ls lu : ℝ, ((0.038 : ℝ) < ls ∧ ls < 0.039) ∧ ((1.564 : ℝ) < lu ∧ lu < 1.565) ∧
        (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed).toLinearMap.charpoly =
          (Polynomial.X - Polynomial.C seedRatio⁻¹) ^ 2 * (Polynomial.X - Polynomial.C ls) *
            (Polynomial.X - Polynomial.C lu) * (Polynomial.X - Polynomial.C seedRatio)) ∧
      ∃ v ∈ stableSubspace (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed).toLinearMap,
        v 4 = 1 := by
  refine ⟨⟨_, LNormalizedOracle.uniform_conditions_eventually μ, ?_⟩, ?_, ?_⟩
  · intro w hw hτ c₁ c₂ hc₁ hc₁' hc hc₂
    have hC : LNormalizedOracle.Conditions μ c₁ c₂ w :=
      hw.conditions hc₁.le hc₁' (hc₁.trans hc).le hc₂.le
    have hr : LNormalizedReturn.returnFactor μ w ≠ 0 := hC.regular.2.1.ne'
    have hbranch (z : Vec 2) (i k : Fin 3) (h : dot (SeedOrbit.gradient seedC seedD k) z <
        dot (SeedOrbit.gradient seedC seedD i) z) :
        LQuadraticSeed.branch μ k z < LQuadraticSeed.branch μ i z :=
      add_lt_add_left h _
    refine ⟨fun k => LNormalizedReturn.scale w • (LNormalizedReturn.internal μ w k).1,
      fun k => LNormalizedReturn.scale w • (LNormalizedReturn.internal μ w k).2, rfl, rfl,
      fun j => ⟨hC.physicalMetric_posDef hτ j, (hC.phase_hasGradient hτ j).differentiableAt,
        fun k hk => hbranch _ j k (((hC.base_active j).scale hτ) k hk), ?_,
        fun N hN => fromMetric_fuel_mono (hC.nonstrict_fromMetric_search hτ j) N hN, ?_,
        hC.actual_point_update hτ j,
        (hC.actual_matrix_update hτ j).symm⟩,
      (LNormalizedReturn.normalization_preserves_point μ w hr).symm,
      (LNormalizedReturn.normalization_preserves_metric μ w hr).symm⟩
    · intro q hq k hk
      have hg := DeterministicLineSearch.actual_coordinateGradient (hC.phase_hasGradient hτ j)
      change LQuadraticSeed.branch μ k (LNormalizedOracle.physicalPoint μ w j + trialLength q •
        bfgsStep (LNormalizedOracle.physicalMetric μ w j) (coordinateGradient (LQuadraticSeed.objective μ)
          (LNormalizedOracle.physicalPoint μ w j)) 1) < LQuadraticSeed.branch μ (trialActive q)
        (LNormalizedOracle.physicalPoint μ w j + trialLength q •
        bfgsStep (LNormalizedOracle.physicalMetric μ w j) (coordinateGradient (LQuadraticSeed.objective μ)
          (LNormalizedOracle.physicalPoint μ w j)) 1)
      rw [hg, LNormalizedOracle.physical_trial]
      have ha := (hC.trial_active q).scale hτ
      rw [hq] at ha
      exact hbranch _ _ k (ha k hk)
    · intro a ha
      obtain ⟨q, hq, rfl⟩ := trial_history_witness j ha
      have h := hC.all_trials_differentiable hτ q
      rw [hq] at h
      exact h
  · obtain ⟨ls, lu, hs, hu, -, -, -, hchar⟩ := LReturnSpectrum.actual_spectral_contract μ
    refine ⟨ls, lu, ⟨by norm_num at hs ⊢; linarith [hs.1], by norm_num at hs ⊢; linarith [hs.2]⟩,
      ⟨by norm_num at hu ⊢; linarith [hu.1], by norm_num at hu ⊢; linarith [hu.2]⟩, hchar⟩
  · obtain ⟨v, hv4, hDv⟩ := LReturnSpectrum.actual_scale_eigenvector μ
    refine ⟨v, ?_, hv4⟩
    set L := (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed).toLinearMap
    have hρ : |seedRatio| < 1 := by
      rw [abs_of_pos source_ratio_pos_lt_one.1]
      exact source_ratio_pos_lt_one.2
    have hvmax : v ∈ Module.End.maxGenEigenspace L seedRatio := by
      apply Module.End.genEigenspace_le_maximal L seedRatio 1
      apply Module.End.eigenspace_le_genEigenspace one_pos
      rw [Module.End.mem_eigenspace_iff]
      exact hDv
    exact (le_iSup₂ (f := fun (t : ℝ) (_ : |t| < 1) => Module.End.maxGenEigenspace L t) seedRatio hρ) hvmax

/-- The normalized shape map at $\tau=0$: `LShapeDerivative.shapeMap c d` sends $(\zeta,\eta)$ to
$((M_3)_{12}/(M_3)_{11},(M_3)_{22}/(M_3)_{11})$, $M_3$ after the three substeps at $\tau=0$
from $M(\zeta,\eta)$; these are the matrix coordinates of $\mathcal T_\mu$ at every state with
$\tau=0$, whatever $z$ (`paper/appendices/lower_curvature.tex:110`: "At $\tau=0$ the matrix
return is independent of $z$"). -/
theorem shape_map_def (μ : ℝ) (w : LNormalizedReturn.State) (hw : LNormalizedReturn.scale w = 0) :
    LShapeDerivative.shapeMap seedC seedD ![w 2, w 3] =
      ![LNormalizedReturn.returnMap μ w 2, LNormalizedReturn.returnMap μ w 3] ∧
      ∀ x : Vec 2, LShapeDerivative.shapeMap seedC seedD x =
        ![(LShapeDerivative.matrixIter seedC seedD x 3) 0 1 / (LShapeDerivative.matrixIter seedC seedD x 3) 0 0,
          (LShapeDerivative.matrixIter seedC seedD x 3) 1 1 / (LShapeDerivative.matrixIter seedC seedD x 3) 0 0] := by
  refine ⟨?_, fun x => rfl⟩
  have hb : w = LNormalizedReturn.shiftPoint
      (LNormalizedReturn.point w - LNormalizedReturn.point LNormalizedReturn.seed)
      (LShapeDerivative.boundary ![w 2, w 3]) := by
    ext i
    fin_cases i <;> simp [LNormalizedReturn.shiftPoint, LShapeDerivative.boundary,
      LNormalizedReturn.point, LNormalizedReturn.seed]
    all_goals first | rfl | exact hw
  rw [LShapeDerivative.shapeMap_eq_returnMap μ]
  conv_rhs => rw [hb, LNormalizedReturn.returnMap_boundary_translate μ
    (LShapeDerivative.boundary_scale _)]
  ext i
  fin_cases i <;> rfl

/-- The Jacobian matrix of the normalized shape map at $(\zeta,\eta)=(0,1)$ is the library's
`LShapeDerivative.jacobian seedC seedD`. -/
theorem shape_jacobian_eq {J : Mat 2}
    (hJ : ∀ i j, J i j = fderiv ℝ (LShapeDerivative.shapeMap seedC seedD) ![0, 1] (Pi.single j 1) i) :
    J = LShapeDerivative.jacobian seedC seedD := by
  have hf := LShapeMapDifferentiability.shapeMap_hasFDerivAt.fderiv
  ext i j
  rw [hJ, show (![0, 1] : Vec 2) = LShapeDerivative.center from rfl, hf,
    LShapeMapDifferentiability.jacobianMap_apply]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Item `A/lower_curvature/disp/008`, equation `art:shape_certificate`
(`paper/appendices/lower_curvature.tex:114-120`), in the proof of Lemma `art:lower_hyperbolic`:
"Let $J$ be the derivative at $(\zeta,\eta)=(0,1)$ of its normalized shape map
$(\zeta,\eta)\mapsto((M_3)_{12},(M_3)_{22})/\hat\rho$. The following
rational enclosures specify the spectral certificate:
\[ 10^{10}J\in\begin{pmatrix}[11123986249,11123986253]&[6459701025,6459701029]\\
   [7515015701,7515015708]&[4905136882,4905136890]\end{pmatrix}." \]
`J i j` is $\partial S_i/\partial x_j$ for the shape map $S$ of `shape_map_def`. -/
theorem shape_certificate (J : Mat 2)
    (hJ : ∀ i j, J i j = fderiv ℝ (LShapeDerivative.shapeMap seedC seedD) ![0, 1] (Pi.single j 1) i) :
    IntervalBounds.Bounds 11123986249 (10 ^ 10 * J 0 0) 11123986253 ∧
      IntervalBounds.Bounds 6459701025 (10 ^ 10 * J 0 1) 6459701029 ∧
      IntervalBounds.Bounds 7515015701 (10 ^ 10 * J 1 0) 7515015708 ∧
      IntervalBounds.Bounds 4905136882 (10 ^ 10 * J 1 1) 4905136890 := by
  rw [shape_jacobian_eq hJ]
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, ⟨h7, h8⟩⟩ := LShapeSpectrum.source_jacobian_bounds
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num at * <;> linarith

/-- Item `A/lower_curvature/disp/009` (`paper/appendices/lower_curvature.tex:124-127`), with lines
121-128, in the proof of Lemma `art:lower_hyperbolic`: "They are obtained by differentiating the
rational substeps \eqref{art:lower_return_substep} at $\tau=0$, then applying the interval rules
of Appendix~\ref{art:seed_certificate} to
\[ c_\circ\in[318481427627118,318481427627119]/10^{15},\quad
   d_\circ\in[-1025232119675749,-1025232119675748]/10^{15}. \]
Both intervals contain the defining root box." The forward-mode derivative of the substeps at
$\tau=0$, `LShapeDerivative.jacobian c d`, lies in the enclosure of display 008 for every
$(c,d)$ in these intervals (the library's interval certificate), and the root box lies in
them. -/
theorem shape_box :
    (∀ x : Vec 2, ‖x - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30 →
      IntervalBounds.Bounds (318481427627118 / 10 ^ 15) (x 0) (318481427627119 / 10 ^ 15) ∧
        IntervalBounds.Bounds (-1025232119675749 / 10 ^ 15) (x 1) (-1025232119675748 / 10 ^ 15)) ∧
      ∀ c d : ℝ, IntervalBounds.Bounds (318481427627118 / 10 ^ 15) c (318481427627119 / 10 ^ 15) →
        IntervalBounds.Bounds (-1025232119675749 / 10 ^ 15) d (-1025232119675748 / 10 ^ 15) →
        IntervalBounds.Bounds 11123986249 (10 ^ 10 * LShapeDerivative.jacobian c d 0 0) 11123986253 ∧
        IntervalBounds.Bounds 6459701025 (10 ^ 10 * LShapeDerivative.jacobian c d 0 1) 6459701029 ∧
        IntervalBounds.Bounds 7515015701 (10 ^ 10 * LShapeDerivative.jacobian c d 1 0) 7515015708 ∧
        IntervalBounds.Bounds 4905136882 (10 ^ 10 * LShapeDerivative.jacobian c d 1 1) 4905136890 := by
  refine ⟨fun x hx => LShapeSpectrum.box_of_original_ball (by simpa [AlgebraicSeed.radius] using hx),
    fun c d hc hd => ?_⟩
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, ⟨h7, h8⟩⟩ := LShapeIntervalCertificate.jacobian_bounds hc hd
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num at * <;> linarith

/-- Item `A/lower_curvature/disp/010` (`paper/appendices/lower_curvature.tex:134-137`), in the
proof of Lemma `art:lower_hyperbolic`: "Substitution of \eqref{art:shape_certificate} in
$p(\lambda)=\lambda^2-\operatorname{tr}(J)\lambda+\det J$ gives
\[ p(0.038)>0,\qquad p(0.039)<0,\qquad p(1.564)<0,\qquad p(1.565)>0." \]
For every matrix $J$ in the enclosure of display 008. -/
theorem characteristic_signs (J : Mat 2)
    (h00 : IntervalBounds.Bounds 11123986249 (10 ^ 10 * J 0 0) 11123986253)
    (h01 : IntervalBounds.Bounds 6459701025 (10 ^ 10 * J 0 1) 6459701029)
    (h10 : IntervalBounds.Bounds 7515015701 (10 ^ 10 * J 1 0) 7515015708)
    (h11 : IntervalBounds.Bounds 4905136882 (10 ^ 10 * J 1 1) 4905136890)
    (p : ℝ → ℝ) (hp : ∀ t, p t = t ^ 2 - J.trace * t + J.det) :
    0 < p 0.038 ∧ p 0.039 < 0 ∧ p 1.564 < 0 ∧ 0 < p 1.565 := by
  have hc (t : ℝ) : p t = LShapeSpectralAlgebra.characteristic J t := by
    rw [hp, LShapeSpectralAlgebra.characteristic, Matrix.trace_fin_two, Matrix.det_fin_two]
  obtain ⟨a1, a2⟩ := h00
  obtain ⟨b1, b2⟩ := h01
  obtain ⟨c1, c2⟩ := h10
  obtain ⟨d1, d2⟩ := h11
  have := LShapeSpectralAlgebra.signs_of_entry_bounds (J := J)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    ⟨by linarith, by linarith⟩
  rw [hc, hc, hc, hc]
  norm_num at this ⊢
  exact this

/-- `pointLift` sends the coordinate vectors of $z$ to those of the state. -/
theorem pointLift_single (k : Fin 2) :
    LNormalizedReturn.pointLift (Pi.single k 1 : Vec 2) =
      (Pi.single (![0, 1] k : Fin 5) 1 : LNormalizedReturn.State) := by
  ext i
  fin_cases k <;> fin_cases i <;> simp [LNormalizedReturn.pointLift, Pi.single_apply, Matrix.cons_val]

/-- Item `A/lower_curvature/disp/011` (`paper/appendices/lower_curvature.tex:144-149`), with lines
141-143 and 150-151, in the proof of Lemma `art:lower_hyperbolic`: "Thus its full derivative has
the block form
\[ D\mathcal T_\mu(P_*)=\begin{pmatrix}\rho^{-1}I_2&*&*\\0&J&*\\0&0&\rho\end{pmatrix}." \]
The matrix of $D\mathcal T_\mu(P_*)$ in the coordinates $(z_1,z_2,\zeta,\eta,\tau)$, with $J$ the
Jacobian matrix of the normalized shape map; the entries marked $*$ are unspecified. -/
theorem return_block_form (μ : ℝ) (J : Mat 2)
    (hJ : ∀ i j, J i j = fderiv ℝ (LShapeDerivative.shapeMap seedC seedD) ![0, 1] (Pi.single j 1) i) :
    ∃ s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ : ℝ,
      LinearMap.toMatrix' (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed).toLinearMap =
        !![seedRatio⁻¹, 0, s₁, s₂, s₃;
           0, seedRatio⁻¹, s₄, s₅, s₆;
           0, 0, J 0 0, J 0 1, s₇;
           0, 0, J 1 0, J 1 1, s₈;
           0, 0, 0, 0, seedRatio] := by
  rw [shape_jacobian_eq hJ]
  set L := fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed
  have hc0 : L (Pi.single 0 1) = seedRatio⁻¹ • (Pi.single 0 1 : LNormalizedReturn.State) := by
    have h := LNormalizedReturn.return_derivative_point_columns μ (Pi.single 0 1)
    rw [pointLift_single] at h
    exact h
  have hc1 : L (Pi.single 1 1) = seedRatio⁻¹ • (Pi.single 1 1 : LNormalizedReturn.State) := by
    have h := LNormalizedReturn.return_derivative_point_columns μ (Pi.single 1 1)
    rw [pointLift_single] at h
    exact h
  have hm00 : L (Pi.single 2 1) 2 = LShapeDerivative.jacobian seedC seedD 0 0 :=
    LShapeSpectrum.actual_middle_block μ 0 0
  have hm01 : L (Pi.single 3 1) 2 = LShapeDerivative.jacobian seedC seedD 0 1 :=
    LShapeSpectrum.actual_middle_block μ 0 1
  have hm10 : L (Pi.single 2 1) 3 = LShapeDerivative.jacobian seedC seedD 1 0 :=
    LShapeSpectrum.actual_middle_block μ 1 0
  have hm11 : L (Pi.single 3 1) 3 = LShapeDerivative.jacobian seedC seedD 1 1 :=
    LShapeSpectrum.actual_middle_block μ 1 1
  have hrow (v : LNormalizedReturn.State) : L v 4 = seedRatio * v 4 :=
    LNormalizedReturn.return_derivative_last_row μ v
  refine ⟨L (Pi.single 2 1) 0, L (Pi.single 3 1) 0, L (Pi.single 4 1) 0,
    L (Pi.single 2 1) 1, L (Pi.single 3 1) 1, L (Pi.single 4 1) 1,
    L (Pi.single 4 1) 2, L (Pi.single 4 1) 3, ?_⟩
  ext i j
  have hsingle : (fun j' => if j' = j then (1 : ℝ) else 0) = (Pi.single j 1 : LNormalizedReturn.State) := by
    funext j'
    simp [Pi.single_apply]
  rw [LinearMap.toMatrix'_apply, hsingle]
  simp only [ContinuousLinearMap.coe_coe]
  fin_cases i <;> fin_cases j <;> simp [hc0, hc1, hm00, hm01, hm10, hm11, hrow]

/-! ### The stable manifold of the boundary seed -/

section Splitting

variable {S U X : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Iterates of a linear map in split coordinates $T\circ E=E\circ(A\times L)$. -/
theorem splitting_pow {T : X →L[ℝ] X} {E : (S × U) ≃L[ℝ] X} {A : S →L[ℝ] S} {L : U →L[ℝ] U}
    (hconj : T.comp E.toContinuousLinearMap = E.toContinuousLinearMap.comp (A.prodMap L))
    (n : ℕ) (w : S × U) : (T ^ n) (E w) = E ((A ^ n) w.1, (L ^ n) w.2) := by
  have h1 : ∀ w : S × U, T (E w) = E (A w.1, L w.2) := fun w =>
    congrArg (fun f => f w) hconj
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, h1]
    simp [pow_succ']

/-- For a splitting $T\circ E=E\circ(A\times L)$ with $\|A\|<1$ and $\|L^{-1}\|<1$, the vectors
whose iterates under $T$ tend to zero are exactly those of $E(S\times0)$. -/
theorem splitting_tendsto_iff {T : X →L[ℝ] X} {E : (S × U) ≃L[ℝ] X} {A : S →L[ℝ] S} {L : U ≃L[ℝ] U}
    (hA : ‖A‖ < 1) (hL : ‖L.symm.toContinuousLinearMap‖ < 1)
    (hconj : T.comp E.toContinuousLinearMap = E.toContinuousLinearMap.comp (A.prodMap L.toContinuousLinearMap))
    (v : X) : Tendsto (fun n : ℕ => (T ^ n) v) atTop (𝓝 0) ↔ ∃ a : S, E (a, 0) = v := by
  constructor
  · intro hv
    set w := E.symm v with hw
    have hv' : v = E w := by simp [hw]
    have h2 : Tendsto (fun n : ℕ => (L.toContinuousLinearMap ^ n) w.2) atTop (𝓝 0) := by
      have hc : Tendsto (fun n : ℕ => E.symm ((T ^ n) v)) atTop (𝓝 (E.symm 0)) :=
        (E.symm.continuous.tendsto 0).comp hv
      rw [map_zero] at hc
      have hs := (continuous_snd.tendsto _).comp hc
      refine (hs.congr fun n => ?_)
      simp [Function.comp, hv', splitting_pow hconj]
    have h1 : ∀ c : U, ‖c‖ ≤ ‖L c‖ := by
      intro c
      calc ‖c‖ = ‖L.symm.toContinuousLinearMap (L c)‖ := by simp
        _ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖L c‖ := L.symm.toContinuousLinearMap.le_opNorm _
        _ ≤ 1 * ‖L c‖ := mul_le_mul_of_nonneg_right hL.le (norm_nonneg _)
        _ = ‖L c‖ := one_mul _
    have hgrow : ∀ (n : ℕ) (b : U), ‖b‖ ≤ ‖(L.toContinuousLinearMap ^ n) b‖ := by
      intro n
      induction n with
      | zero => intro b; simp
      | succ n ih =>
        intro b
        rw [pow_succ', ContinuousLinearMap.mul_apply]
        exact (ih b).trans (h1 _)
    have hb : w.2 = 0 := by
      have hn := (continuous_norm.tendsto _).comp h2
      rw [norm_zero] at hn
      exact norm_le_zero_iff.mp (ge_of_tendsto hn (Eventually.of_forall fun n => hgrow n w.2))
    exact ⟨w.1, by rw [hv', ← hb]⟩
  · rintro ⟨a, rfl⟩
    have hb : ∀ n : ℕ, ‖(A ^ n) a‖ ≤ ‖A‖ ^ n * ‖a‖ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', ContinuousLinearMap.mul_apply, pow_succ, mul_comm (‖A‖ ^ n) ‖A‖, mul_assoc]
        exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg A))
    have hA' : Tendsto (fun n : ℕ => (A ^ n) a) atTop (𝓝 0) := by
      apply squeeze_zero_norm hb
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg A) hA).mul_const ‖a‖
    have hE : Tendsto (fun n : ℕ => E ((A ^ n) a, 0)) atTop (𝓝 (E (0, 0))) :=
      (E.continuous.tendsto _).comp (hA'.prodMk_nhds tendsto_const_nhds)
    rw [show ((0 : S), (0 : U)) = 0 from rfl, map_zero] at hE
    refine hE.congr fun n => ?_
    rw [splitting_pow hconj]
    simp

end Splitting

/-- In the exact diagonal coordinates of `LReturnSpectrum.actual_spectral_contract`
($D\mathcal T_\mu(P_*)E=E\operatorname{diag}(\lambda_s,\rho;\rho^{-1},\rho^{-1},\lambda_u)$), the
stable subspace of Lemma `art:lower_hyperbolic` is $E(\mathbb R^2\times0)$. -/
theorem stableSubspace_iff_diagonal (μ : ℝ) {ls lu : ℝ} (hs : 0 < ls ∧ ls < 1) (hu : 1 < lu)
    {E : LBlockSplitting.Coordinates ≃L[ℝ] LNormalizedReturn.State}
    (hE : ∀ w, (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed) (E w) =
      E (LBlockSplitting.diagonalMap ![ls, seedRatio] w.1,
        LBlockSplitting.diagonalMap ![seedRatio⁻¹, seedRatio⁻¹, lu] w.2))
    (v : LNormalizedReturn.State) :
    v ∈ stableSubspace (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed).toLinearMap ↔
      ∃ a : Vec 2, E (a, 0) = v := by
  set T := fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed with hT
  have hρ := source_ratio_pos_lt_one
  let R : Submodule ℝ LNormalizedReturn.State :=
    LinearMap.range ((E : LBlockSplitting.Coordinates →L[ℝ] LNormalizedReturn.State).toLinearMap.comp
      (LinearMap.inl ℝ (Vec 2) (Vec 3)))
  have hR : ∀ v, v ∈ R ↔ ∃ a : Vec 2, E (a, 0) = v := fun v => by
    simp [R]
  constructor
  · intro hv
    refine (hR v).mp ((iSup₂_le (fun t ht => ?_) : stableSubspace T.toLinearMap ≤ R) hv)
    intro x hx
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
    set w := E.symm x with hw
    have hx' : x = E w := by simp [hw]
    have hstep : ∀ (j : ℕ) (u : LBlockSplitting.Coordinates),
        ((T.toLinearMap - t • (1 : Module.End ℝ LNormalizedReturn.State)) ^ j) (E u) =
          E (fun i => (![ls, seedRatio] i - t) ^ j * u.1 i,
            fun i => (![seedRatio⁻¹, seedRatio⁻¹, lu] i - t) ^ j * u.2 i) := by
      intro j
      induction j with
      | zero => intro u; simp
      | succ j ih =>
        intro u
        rw [pow_succ', Module.End.mul_apply, ih]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          ContinuousLinearMap.coe_coe, hE]
        rw [← map_smul, ← map_sub]
        congr 1
        ext i <;> simp [LBlockSplitting.diagonalMap_apply, pow_succ'] <;> ring
    rw [hx', hstep] at hk
    have hk2 := congrArg Prod.snd ((map_eq_zero_iff E E.injective).mp hk)
    have hw2 : w.2 = 0 := by
      ext i
      have hi := congrFun hk2 i
      simp only [Prod.snd_zero, Pi.zero_apply] at hi
      have htl : t < 1 := (abs_lt.mp ht).2
      have hinv : 1 < seedRatio⁻¹ := (one_lt_inv₀ hρ.1).mpr hρ.2
      have hpos : 0 < ![seedRatio⁻¹, seedRatio⁻¹, lu] i - t := by
        fin_cases i <;> simp <;> linarith
      have hne : (![seedRatio⁻¹, seedRatio⁻¹, lu] i - t) ^ k ≠ 0 := pow_ne_zero _ hpos.ne'
      simpa [hne] using hi
    exact (hR x).mpr ⟨w.1, by rw [hx', ← hw2]⟩
  · rintro ⟨a, rfl⟩
    have heig : ∀ (j : Fin 2) (d : ℝ), ![ls, seedRatio] j = d → |d| < 1 →
        E (Pi.single j 1, 0) ∈ stableSubspace T.toLinearMap := by
      intro j d hd hd1
      have hmem : E (Pi.single j 1, 0) ∈ Module.End.maxGenEigenspace T.toLinearMap d := by
        apply Module.End.genEigenspace_le_maximal _ d 1
        apply Module.End.eigenspace_le_genEigenspace one_pos
        rw [Module.End.mem_eigenspace_iff]
        change T (E (Pi.single j 1, 0)) = d • E (Pi.single j 1, 0)
        rw [hE, ← map_smul]
        congr 1
        ext i <;> simp [LBlockSplitting.diagonalMap_apply, Pi.single_apply, ← hd]
        split_ifs with h <;> simp [h]
      exact (le_iSup₂ (f := fun (t : ℝ) (_ : |t| < 1) => Module.End.maxGenEigenspace T.toLinearMap t)
        d hd1) hmem
    have h0 := heig 0 ls rfl (by rw [abs_of_pos hs.1]; exact hs.2)
    have h1 := heig 1 seedRatio rfl (by rw [abs_of_pos hρ.1]; exact hρ.2)
    have hsplit : E (a, 0) = a 0 • E (Pi.single 0 1, 0) + a 1 • E (Pi.single 1 1, 0) := by
      rw [← map_smul, ← map_smul, ← map_add]
      congr 1
      ext i <;> fin_cases i <;> simp
    rw [hsplit]
    exact (stableSubspace T.toLinearMap).add_mem ((stableSubspace T.toLinearMap).smul_mem _ h0)
      ((stableSubspace T.toLinearMap).smul_mem _ h1)

/-- Item `A/lower_curvature/prose/036` (`paper/appendices/lower_curvature.tex:54-58`): "The right
object for persistence is the three-step return map after dividing out the shrinking scale. The
homogeneous cycle becomes a fixed point on the boundary where that scale is zero. We will verify
that it is hyperbolic and that its stable manifold enters the positive-scale region."

Reading. The return map is $\mathcal T_\mu$ of `art:lower_return`; the homogeneous cycle is
$P_*$, a fixed point with $\tau=0$. Hyperbolic: no eigenvalue of $D\mathcal T_\mu(P_*)$, real or
complex, has modulus one. Its stable manifold enters $\tau>0$: inside every neighbourhood $W$
of $P_*$ there is a smooth injective two-parameter chart $\Phi$ with $\Phi(0)=P_*$, whose derivative
at $0$ is injective with range the stable subspace (`stableSubspace`, the sum of the generalized
eigenspaces of the eigenvalues of modulus less than one), every point $\Phi(a)$ of which has its
forward $\mathcal T_\mu$-orbit in $W$, converging to $P_*$; and some point $\Phi(a)$ has
$\tau>0$. -/
theorem stable_manifold_positive_scale (μ : ℝ) (_hμ : 0 < μ) :
    LNormalizedReturn.returnMap μ LNormalizedReturn.seed = LNormalizedReturn.seed ∧
      LNormalizedReturn.scale LNormalizedReturn.seed = 0 ∧
      (∀ z : ℂ, ‖z‖ = 1 → Polynomial.eval₂ (algebraMap ℝ ℂ) z
        (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed).toLinearMap.charpoly ≠ 0) ∧
      ∀ W ∈ 𝓝 LNormalizedReturn.seed, ∃ (V : Set (Vec 2)) (Φ : Vec 2 → LNormalizedReturn.State),
        IsOpen V ∧ (0 : Vec 2) ∈ V ∧ Φ 0 = LNormalizedReturn.seed ∧ ContDiffOn ℝ ∞ Φ V ∧
        Function.Injective Φ ∧ Function.Injective (fderiv ℝ Φ 0) ∧
        LinearMap.range (fderiv ℝ Φ 0 : Vec 2 →ₗ[ℝ] LNormalizedReturn.State) =
          stableSubspace (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed).toLinearMap ∧
        (∀ a ∈ V, ∃ w : ℕ → LNormalizedReturn.State, w 0 = Φ a ∧ (∀ n, w n ∈ W) ∧
          Tendsto w atTop (𝓝 LNormalizedReturn.seed) ∧
          ∀ n, w (n + 1) = LNormalizedReturn.returnMap μ (w n)) ∧
        ∃ a ∈ V, 0 < LNormalizedReturn.scale (Φ a) := by
  refine ⟨LNormalizedReturn.seed_fixed μ, LNormalizedReturn.seed_scale,
    fun z hz => LReturnSpectrum.actual_no_unit_complex_root μ hz, fun W hW => ?_⟩
  obtain ⟨E, -, A, L, hA, hL, hconj, h, V, hV, hV0, h0, -, -, hchart, hchartd, hτ, hsol⟩ :=
    LReturnStableGraph.source_smooth_stable_graph μ W hW
  obtain ⟨ls, lu, hs, hu, E', -, hE', -⟩ := LReturnSpectrum.actual_spectral_contract μ
  set Φ := AnalyticStableGraph.chart LNormalizedReturn.seed E h with hΦ
  have hfd : fderiv ℝ Φ 0 = E.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 3)) :=
    hchartd.fderiv
  set T := fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed with hT
  have hρ := source_ratio_pos_lt_one
  have hls : 0 < ls ∧ ls < 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hlu : 1 < lu := by linarith [hu.1]
  have hdne : ∀ i, (![seedRatio⁻¹, seedRatio⁻¹, lu] : Vec 3) i ≠ 0 := by
    have hρi : seedRatio⁻¹ ≠ 0 := inv_ne_zero hρ.1.ne'
    have hlu0 : lu ≠ 0 := by linarith
    intro i; fin_cases i <;> simp [hρi, hlu0]
  have hconj' : T.comp E'.toContinuousLinearMap = E'.toContinuousLinearMap.comp
      ((LBlockSplitting.diagonalMap ![ls, seedRatio]).prodMap
        (LBlockSplitting.diagonalEquiv ![seedRatio⁻¹, seedRatio⁻¹, lu] hdne).toContinuousLinearMap) :=
    ContinuousLinearMap.ext fun w => hE' w
  have hstab : ∀ v, v ∈ stableSubspace T.toLinearMap ↔ ∃ a : Vec 2, E (a, 0) = v := by
    intro v
    rw [stableSubspace_iff_diagonal μ hls hlu hE' v,
      ← splitting_tendsto_iff (LBlockSplitting.stable_diagonal_contraction hls.1 hls.2 hρ.1 hρ.2)
        (LBlockSplitting.unstable_diagonal_inverse_contraction hρ.1 hρ.2 hlu hdne) hconj' v,
      splitting_tendsto_iff hA hL hconj v]
  refine ⟨V, Φ, hV, hV0, ?_, hchart, AnalyticStableGraph.chart_injective _ _ _, ?_, ?_, hsol, ?_⟩
  · simp [hΦ, AnalyticStableGraph.chart, h0]
  · rw [hfd]
    intro a b hab
    have := E.injective hab
    simpa using congrArg Prod.fst this
  · ext v
    rw [hstab v, LinearMap.mem_range, hfd]
    rfl
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 0 hV0
    refine ⟨![0, ε / 2], hball ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      refine (pi_norm_lt_iff hε).mpr fun i => ?_
      fin_cases i <;> simp [abs_of_pos hε] <;> linarith
    · rw [hτ]
      simp
      linarith

/-! ### The accumulation embedding with four strongly convex branches -/

/-- Item `A/lower_curvature/disp/012` (`paper/appendices/lower_curvature.tex:210-213`): "Fix
\[ \mu=1/4096,\quad c_*=(2,-32)^T,\quad q_i=g_i-\mu c_*,\quad b_i=q_i^Tc_*,\quad r=1/128,\quad
   a_\ell=r^\ell." \] -/
theorem embedding_constants_def :
    LEmbedding.mu = 1 / 4096 ∧ LEmbedding.center = ![2, -32] ∧
      (∀ i, LEmbedding.slope i = SeedOrbit.gradient seedC seedD i - LEmbedding.mu • LEmbedding.center) ∧
      (∀ i, LEmbedding.parameter i = dot (LEmbedding.slope i) LEmbedding.center) ∧
      LScalarGeometric.theta = 1 / 128 ∧ LScalarRamp.theta = 1 / 128 ∧
      ∀ ℓ, LScalarGeometric.scale ℓ = LScalarGeometric.theta ^ ℓ :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ => rfl⟩

/-- Item `A/lower_curvature/prose/012` (`paper/appendices/lower_curvature.tex:214-215`): "Here
$b_0=b_1=1791/1024$ and $1.7<b_i<34$. For each of the two distinct values of $b_i$". -/
theorem parameter_values :
    LEmbedding.parameter 0 = 1791 / 1024 ∧ LEmbedding.parameter 1 = 1791 / 1024 ∧
      (∀ i, (1.7 : ℝ) < LEmbedding.parameter i ∧ LEmbedding.parameter i < 34) ∧
      LEmbedding.parameter 2 ≠ LEmbedding.parameter 0 := by
  refine ⟨LEmbedding.parameter_first, LEmbedding.parameter_second, fun i => ?_, ?_⟩
  · have h := LEmbedding.parameter_bounds i
    norm_num
    exact h
  · rw [LEmbedding.parameter_first]
    have h := LEmbedding.parameter_third_gt
    intro he
    rw [he] at h
    norm_num at h

/-- Item `A/lower_curvature/disp/013` (`paper/appendices/lower_curvature.tex:216-218`):
\[ t_b=\frac{1-(1+r)/b}{1-r},\qquad\varepsilon=1/1024. \] -/
theorem ramp_constants_def (b : ℝ) :
    LScalarRamp.center b = (1 - (1 + LScalarRamp.theta) / b) / (1 - LScalarRamp.theta) ∧
      LScalarRamp.epsilon = 1 / 1024 :=
  ⟨rfl, rfl⟩

/-- The two values $b=b_i$ (`b = LEmbedding.parameter i`) lie in $[1.7,34]$, the range of the
general forms below. -/
theorem parameter_range {i : Fin 3} {b : ℝ} (hb : b = LEmbedding.parameter i) : 17/10 ≤ b ∧ b ≤ 34 := by
  subst hb
  exact ⟨(LEmbedding.parameter_bounds i).1.le, (LEmbedding.parameter_bounds i).2.le⟩

/-- The cubic ramp $P_b$ of `paper/sections/failure.tex:284-291` with center `t` and width `ε`:
$0$ for $\xi\le t-\varepsilon$, $3v^2-2v^3$ for $|\xi-t|<\varepsilon$, $1$ for
$\xi\ge t+\varepsilon$, where $v=(\xi-t+\varepsilon)/(2\varepsilon)$. -/
def cubicRamp (t ε ξ : ℝ) : ℝ :=
  if ξ ≤ t - ε then 0 else if t + ε ≤ ξ then 1 else
    3 * ((ξ - t + ε) / (2 * ε)) ^ 2 - 2 * ((ξ - t + ε) / (2 * ε)) ^ 3

/-- Its primitive $J_b(\xi)=\int_0^\xi P_b(t)\,dt$. -/
def cubicPrimitive (t ε ξ : ℝ) : ℝ := ∫ s in (0 : ℝ)..ξ, cubicRamp t ε s

/-- The library ramp is the cubic ramp with center $t_b$ and width $\varepsilon$. -/
theorem ramp_eq_cubicRamp (b ξ : ℝ) :
    LScalarRamp.ramp b ξ = cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon ξ := by
  unfold cubicRamp
  split_ifs with h1 h2
  · exact LScalarRamp.ramp_eq_zero h1
  · exact LScalarRamp.ramp_eq_one h2
  · rw [LScalarRamp.ramp_eq_cubic (not_le.mp h1) (not_le.mp h2)]
    rfl

/-- For every $1.7\le b\le34$ (a range containing both values $b_i$; the item is `ramp_def_bi`):
the library's `LScalarRamp.ramp b` and `LScalarRamp.primitive b` are $P_b$ and $J_b$ with center
$t_b$ and width $\varepsilon=1/1024$. -/
theorem ramp_def {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    LScalarRamp.ramp b = cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon ∧
      LScalarRamp.primitive b = cubicPrimitive (LScalarRamp.center b) LScalarRamp.epsilon := by
  have h1 : LScalarRamp.ramp b = cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon :=
    funext (ramp_eq_cubicRamp b)
  refine ⟨h1, funext fun ξ => ?_⟩
  rw [LScalarRamp.primitive_eq_integral hl hr, cubicPrimitive, h1]

/-- Item `A/lower_curvature/prose/013` (`paper/appendices/lower_curvature.tex:219-220`): "Use the
same cubic ramp $P_b$ and primitive $J_b$ defined before \eqref{art:upper_scalar}, with this
center and width." For each of the values $b=b_i$, the library's `LScalarRamp.ramp b` and
`LScalarRamp.primitive b` are $P_b$ and $J_b$ with center $t_b$ and width $\varepsilon=1/1024$. -/
theorem ramp_def_bi (i : Fin 3) {b : ℝ} (hb : b = LEmbedding.parameter i) :
    LScalarRamp.ramp b = cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon ∧
      LScalarRamp.primitive b = cubicPrimitive (LScalarRamp.center b) LScalarRamp.epsilon :=
  ramp_def (parameter_range hb).1 (parameter_range hb).2

/-- For every $1.7\le b\le34$ (the item is `lower_scalar_def_bi`): the library's `LScalar.phi b`
satisfies the equations of `art:lower_scalar` and of the lines after it; `lower_scalar_unique`
shows that they determine it. -/
theorem lower_scalar_def {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (r : ℝ) (hrdef : r = 1 / 128)
    (a : ℕ → ℝ) (ha : ∀ ℓ, a ℓ = r ^ ℓ) (t ε : ℝ) (ht : t = (1 - (1 + r) / b) / (1 - r))
    (hε : ε = 1 / 1024) :
    (∀ (ℓ : ℕ) (x ξ : ℝ), b * a (ℓ + 1) ≤ x → x ≤ b * a ℓ → ξ = (x / (b * a ℓ) - r) / (1 - r) →
      LScalar.phi b x = (r * a ℓ) ^ 2 + b * a ℓ ^ 2 * (1 - r) * (r * ξ + (1 - r) * cubicPrimitive t ε ξ)) ∧
      LScalar.phi b 0 = 0 ∧ (∀ x, x < 0 → LScalar.phi b x = x ^ 2 / 2) ∧
      ∀ x, b ≤ x → LScalar.phi b x = 1 + x - b := by
  have hθ : r = LScalarGeometric.theta := by rw [hrdef]; rfl
  have hprim := (ramp_def hl hr).2
  have hcen : t = LScalarRamp.center b := by rw [ht, hrdef]; rfl
  have heps : ε = LScalarRamp.epsilon := by rw [hε]; rfl
  refine ⟨fun ℓ x ξ hlo hhi hξ => ?_, LScalar.phi_zero hl hr,
    fun x hx => LScalar.phi_eq_negative hl hr hx.le, fun x hx => LScalar.phi_eq_outer hl hr hx⟩
  have ha' : a ℓ = LScalarGeometric.scale ℓ := by rw [ha, hθ]; rfl
  have hlo' : b * LScalarGeometric.theta * LScalarGeometric.scale ℓ ≤ x := by
    rw [ha, hθ, pow_succ] at hlo
    change b * LScalarGeometric.theta * LScalarGeometric.theta ^ ℓ ≤ x
    linarith [show b * (LScalarGeometric.theta ^ ℓ * LScalarGeometric.theta) =
      b * LScalarGeometric.theta * LScalarGeometric.theta ^ ℓ by ring]
  have hhi' : x ≤ b * LScalarGeometric.scale ℓ := by rw [← ha']; exact hhi
  rw [LScalar.phi_interval hl hr ℓ hlo' hhi', hξ, ha', hθ, hcen, heps, ← hprim]
  rfl

/-- Item `A/lower_curvature/disp/014`, equation `art:lower_scalar`
(`paper/appendices/lower_curvature.tex:222-226`), with prose item
`A/lower_curvature/prose/014` (lines 227-228): "For $ba_{\ell+1}\le x\le ba_\ell$ put
\[ \psi_b(x)=(ra_\ell)^2+ba_\ell^2(1-r)\{r\xi+(1-r)J_b(\xi)\},\qquad
   \xi=\frac{x/(ba_\ell)-r}{1-r}. \]
Set $\psi_b(0)=0$, $\psi_b(x)=x^2/2$ for $x<0$, and $\psi_b(x)=1+x-b$ for $x\ge b$." For each
of the values $b=b_i$, the library's `LScalar.phi b` satisfies these equations;
`lower_scalar_unique` shows that they determine it. -/
theorem lower_scalar_def_bi (i : Fin 3) {b : ℝ} (hb : b = LEmbedding.parameter i) (r : ℝ)
    (hrdef : r = 1 / 128) (a : ℕ → ℝ) (ha : ∀ ℓ, a ℓ = r ^ ℓ) (t ε : ℝ)
    (ht : t = (1 - (1 + r) / b) / (1 - r)) (hε : ε = 1 / 1024) :
    (∀ (ℓ : ℕ) (x ξ : ℝ), b * a (ℓ + 1) ≤ x → x ≤ b * a ℓ → ξ = (x / (b * a ℓ) - r) / (1 - r) →
      LScalar.phi b x = (r * a ℓ) ^ 2 + b * a ℓ ^ 2 * (1 - r) * (r * ξ + (1 - r) * cubicPrimitive t ε ξ)) ∧
      LScalar.phi b 0 = 0 ∧ (∀ x, x < 0 → LScalar.phi b x = x ^ 2 / 2) ∧
      ∀ x, b ≤ x → LScalar.phi b x = 1 + x - b :=
  lower_scalar_def (parameter_range hb).1 (parameter_range hb).2 r hrdef a ha t ε ht hε

/-- The equations of `lower_scalar_def` determine $\psi_b$: every function satisfying them is
`LScalar.phi b`. -/
theorem lower_scalar_unique {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (f : ℝ → ℝ)
    (hint : ∀ (ℓ : ℕ) (x : ℝ), b * LScalarGeometric.scale (ℓ + 1) ≤ x → x ≤ b * LScalarGeometric.scale ℓ →
      f x = (LScalarGeometric.theta * LScalarGeometric.scale ℓ) ^ 2 +
        b * LScalarGeometric.scale ℓ ^ 2 * (1 - LScalarGeometric.theta) *
          (LScalarGeometric.theta * LScalarGeometric.coordinate b (LScalarGeometric.scale ℓ) x +
            (1 - LScalarGeometric.theta) *
              LScalarRamp.primitive b (LScalarGeometric.coordinate b (LScalarGeometric.scale ℓ) x)))
    (h0 : f 0 = 0) (hneg : ∀ x, x < 0 → f x = x ^ 2 / 2) (hout : ∀ x, b ≤ x → f x = 1 + x - b) :
    f = LScalar.phi b := by
  funext x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [hneg x hx, LScalar.phi_eq_negative hl hr hx.le]
  · rw [h0, LScalar.phi_zero hl hr]
  · by_cases hxb : b ≤ x
    · rw [hout x hxb, LScalar.phi_eq_outer hl hr hxb]
    · obtain ⟨ℓ, h1, h2⟩ := LScalarGeometric.positive_interval_cover (by linarith) hx (not_le.mp hxb).le
      have h1' : b * LScalarGeometric.scale (ℓ + 1) ≤ x := by
        rw [LScalarGeometric.scale_succ]
        linarith
      rw [hint ℓ x h1' h2, LScalar.phi_interval hl hr ℓ h1.le h2]

/-- For every $1.7\le b\le34$ (the item is `lower_scalar_derivatives_bi`): on the closed interval
$ba_{\ell+1}\le x\le ba_\ell$, $\psi_b'=a_\ell\{r+(1-r)P_b(\xi)\}$, $\psi_b''=P_b'(\xi)/b$, and
$0\le P_b'\le768$. -/
theorem lower_scalar_derivatives {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (ℓ : ℕ) (x ξ : ℝ)
    (hlo : b * LScalarGeometric.scale (ℓ + 1) ≤ x) (hhi : x ≤ b * LScalarGeometric.scale ℓ)
    (hξ : ξ = (x / (b * LScalarGeometric.scale ℓ) - LScalarGeometric.theta) / (1 - LScalarGeometric.theta)) :
    HasDerivAt (LScalar.phi b) (LScalarGeometric.scale ℓ * (LScalarGeometric.theta +
        (1 - LScalarGeometric.theta) * cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon ξ)) x ∧
      HasDerivAt (deriv (LScalar.phi b))
        (deriv (cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon) ξ / b) x ∧
      ∀ η, 0 ≤ deriv (cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon) η ∧
        deriv (cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon) η ≤ 768 := by
  have hb : 0 < b := by linarith
  have hramp := (ramp_def hl hr).1
  have hlo' : b * LScalarGeometric.theta * LScalarGeometric.scale ℓ ≤ x := by
    rw [LScalarGeometric.scale_succ] at hlo
    linarith
  have hx : 0 < x := lt_of_lt_of_le (by
    have := LScalarGeometric.scale_pos ℓ
    have := LScalarGeometric.theta_pos
    positivity) hlo'
  have hcoord : LScalarGeometric.coordinate b (LScalarGeometric.scale ℓ) x = ξ := by
    rw [hξ]; rfl
  have hderiv (η : ℝ) : deriv (cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon) η =
      LScalarRamp.rampDerivative b η := by
    rw [← hramp]
    exact (LScalarRamp.ramp_hasDerivAt b η).deriv
  refine ⟨?_, ?_, fun η => by rw [hderiv]; exact LScalarRamp.rampDerivative_bounds b η⟩
  · have h := LScalar.phi_hasDerivAt hl hr x
    rw [LScalar.phiFirst_eq_positive hx.le, LScalar.positiveSlope_interval hl hr ℓ hlo' hhi, hcoord,
      hramp] at h
    simpa only [pow_one] using h
  · have h := LScalar.phi_second_hasDerivAt_pos hl hr hx
    rw [LScalar.positiveCurvature_interval hl hr ℓ hlo' hhi, LScalar.curvatureComponent, hcoord,
      ← hderiv] at h
    convert h using 1
    ring

/-- Item `A/lower_curvature/disp/015` (`paper/appendices/lower_curvature.tex:231-234`): "On each
positive interval,
\[ \psi_b'=a_\ell\{r+(1-r)P_b(\xi)\},\qquad \psi_b''=P_b'(\xi)/b,\qquad0\le P_b'\le768." \]
For each of the values $b=b_i$, on the closed interval $ba_{\ell+1}\le x\le ba_\ell$, with $\xi$
as in `art:lower_scalar` and $P_b'$ the derivative of $P_b$. -/
theorem lower_scalar_derivatives_bi (i : Fin 3) {b : ℝ} (hb : b = LEmbedding.parameter i) (ℓ : ℕ)
    (x ξ : ℝ) (hlo : b * LScalarGeometric.scale (ℓ + 1) ≤ x) (hhi : x ≤ b * LScalarGeometric.scale ℓ)
    (hξ : ξ = (x / (b * LScalarGeometric.scale ℓ) - LScalarGeometric.theta) / (1 - LScalarGeometric.theta)) :
    HasDerivAt (LScalar.phi b) (LScalarGeometric.scale ℓ * (LScalarGeometric.theta +
        (1 - LScalarGeometric.theta) * cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon ξ)) x ∧
      HasDerivAt (deriv (LScalar.phi b))
        (deriv (cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon) ξ / b) x ∧
      ∀ η, 0 ≤ deriv (cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon) η ∧
        deriv (cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon) η ≤ 768 :=
  lower_scalar_derivatives (parameter_range hb).1 (parameter_range hb).2 ℓ x ξ hlo hhi hξ

/-- For every $1.7\le b\le34$ (the item is `lower_scalar_nodes_bi`): the matching identity, and the
node values $a_\ell^2$ and slopes $a_\ell$ at $x=ba_\ell$. -/
theorem lower_scalar_nodes {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    LScalarGeometric.theta + (1 - LScalarGeometric.theta) * (1 - LScalarRamp.center b) =
        (1 + LScalarGeometric.theta) / b ∧
      ∀ ℓ, LScalar.phi b (b * LScalarGeometric.scale ℓ) = LScalarGeometric.scale ℓ ^ 2 ∧
        HasDerivAt (LScalar.phi b) (LScalarGeometric.scale ℓ) (b * LScalarGeometric.scale ℓ) :=
  ⟨LScalarRamp.matching_identity (by linarith),
    fun ℓ => ⟨LScalar.phi_node hl hr ℓ, LScalar.phi_node_hasDerivAt hl hr ℓ⟩⟩

/-- Item `A/lower_curvature/prose/015` (`paper/appendices/lower_curvature.tex:235-236`): "The
identity $r+(1-r)(1-t_b)=(1+r)/b$ matches node values and derivatives. Their values are
$a_\ell^2$ and $a_\ell$, respectively." For each of the values $b=b_i$. -/
theorem lower_scalar_nodes_bi (i : Fin 3) {b : ℝ} (hb : b = LEmbedding.parameter i) :
    LScalarGeometric.theta + (1 - LScalarGeometric.theta) * (1 - LScalarRamp.center b) =
        (1 + LScalarGeometric.theta) / b ∧
      ∀ ℓ, LScalar.phi b (b * LScalarGeometric.scale ℓ) = LScalarGeometric.scale ℓ ^ 2 ∧
        HasDerivAt (LScalar.phi b) (LScalarGeometric.scale ℓ) (b * LScalarGeometric.scale ℓ) :=
  lower_scalar_nodes (parameter_range hb).1 (parameter_range hb).2

/-- For every $1.7\le b\le34$ (the item is `lower_scalar_monotone_flat_bi`): $\psi_b'$ is monotone
on $x>0$ and constant near every node. -/
theorem lower_scalar_monotone_flat {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    MonotoneOn (deriv (LScalar.phi b)) (Set.Ioi 0) ∧
      ∀ ℓ, ∀ᶠ x in 𝓝 (b * LScalarGeometric.scale ℓ), deriv (LScalar.phi b) x = LScalarGeometric.scale ℓ := by
  refine ⟨fun x hx y hy hxy => ?_, fun ℓ => ?_⟩
  · rw [LScalar.deriv_phi hl hr, LScalar.phiFirst_eq_positive (le_of_lt hx),
      LScalar.phiFirst_eq_positive (le_of_lt hy)]
    exact LScalar.positiveSlope_monotone (by linarith) hxy
  · have hs := LScalarGeometric.scale_pos ℓ
    have hopen : IsOpen {y : ℝ | |y - b * LScalarGeometric.scale ℓ| < LScalarGeometric.scale ℓ / 2} :=
      isOpen_lt ((continuous_id.sub continuous_const).abs) continuous_const
    filter_upwards [hopen.mem_nhds (by simp; positivity)] with y hy
    have h := LScalar.phi_plateau_hasDerivAt hl hr ℓ (h := y - b * LScalarGeometric.scale ℓ) hy
    rw [add_sub_cancel] at h
    exact h.deriv

/-- Item `A/lower_curvature/prose/016` (`paper/appendices/lower_curvature.tex:237`): "The positive
derivative is monotone and constant near every node." For each of the values $b=b_i$. -/
theorem lower_scalar_monotone_flat_bi (i : Fin 3) {b : ℝ} (hb : b = LEmbedding.parameter i) :
    MonotoneOn (deriv (LScalar.phi b)) (Set.Ioi 0) ∧
      ∀ ℓ, ∀ᶠ x in 𝓝 (b * LScalarGeometric.scale ℓ), deriv (LScalar.phi b) x = LScalarGeometric.scale ℓ :=
  lower_scalar_monotone_flat (parameter_range hb).1 (parameter_range hb).2

/-- For every $1.7\le b\le34$ (the item is `lower_scalar_regularity_bi`): the slopes of $\psi_b'$
lie in $[0,\max(1,768/b)]$, and $\psi_b$ is $C^{1,1}$, convex, coercive, nonnegative, with unique
zero at the origin. -/
theorem lower_scalar_regularity {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    (∀ x s : ℝ, HasDerivAt (deriv (LScalar.phi b)) s x → 0 ≤ s ∧ s ≤ max 1 (768 / b)) ∧
      ContDiff ℝ 1 (LScalar.phi b) ∧ (∃ K, LipschitzWith K (deriv (LScalar.phi b))) ∧
      ConvexOn ℝ univ (LScalar.phi b) ∧ Tendsto (LScalar.phi b) (cocompact ℝ) atTop ∧
      (∀ x, 0 ≤ LScalar.phi b x) ∧ ∀ x, LScalar.phi b x = 0 ↔ x = 0 := by
  obtain ⟨hconv, hnn, hcoer, ⟨_, huniq⟩, hC1, hlip, -, -, -, hsec⟩ := lScalarRegularity b hl hr
  refine ⟨fun x s h => hsec x s h, hC1, hlip, hconv, hcoer, hnn, fun x => ⟨fun h => ?_, ?_⟩⟩
  · exact huniq x (h.trans (LScalar.phi_zero hl hr).symm)
  · rintro rfl
    exact LScalar.phi_zero hl hr

/-- Item `A/lower_curvature/prose/017` (`paper/appendices/lower_curvature.tex:238-240`): "Its
derivative slopes are uniformly bounded, so summing over intervals and taking a limit at zero
proves that $\psi_b$ is globally $C^{1,1}$, convex and coercive, nonnegative with unique zero at
the origin." For each of the values $b=b_i$. -/
theorem lower_scalar_regularity_bi (i : Fin 3) {b : ℝ} (hb : b = LEmbedding.parameter i) :
    (∀ x s : ℝ, HasDerivAt (deriv (LScalar.phi b)) s x → 0 ≤ s ∧ s ≤ max 1 (768 / b)) ∧
      ContDiff ℝ 1 (LScalar.phi b) ∧ (∃ K, LipschitzWith K (deriv (LScalar.phi b))) ∧
      ConvexOn ℝ univ (LScalar.phi b) ∧ Tendsto (LScalar.phi b) (cocompact ℝ) atTop ∧
      (∀ x, 0 ≤ LScalar.phi b x) ∧ ∀ x, LScalar.phi b x = 0 ↔ x = 0 :=
  lower_scalar_regularity (parameter_range hb).1 (parameter_range hb).2

/-- $P_b(\xi)=1$ exactly when $\xi\ge t+\varepsilon$. -/
theorem cubicRamp_eq_one_iff {t ε ξ : ℝ} (hε : 0 < ε) : cubicRamp t ε ξ = 1 ↔ t + ε ≤ ξ := by
  unfold cubicRamp
  constructor
  · intro h
    by_contra hξ
    push_neg at hξ
    split_ifs at h with h1 h2
    · norm_num at h
    · linarith
    · set v := (ξ - t + ε) / (2 * ε)
      have hv0 : 0 < v := div_pos (by linarith [not_le.mp h1]) (by linarith)
      have hv1 : v < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      nlinarith [mul_pos (sub_pos.mpr hv1) (sub_pos.mpr hv1), mul_pos hv0 hv0]
  · intro h
    rw [if_neg (by linarith), if_pos h]

/-- $P_b(\xi)=0$ exactly when $\xi\le t-\varepsilon$. -/
theorem cubicRamp_eq_zero_iff {t ε ξ : ℝ} (hε : 0 < ε) : cubicRamp t ε ξ = 0 ↔ ξ ≤ t - ε := by
  unfold cubicRamp
  constructor
  · intro h
    by_contra hξ
    push_neg at hξ
    rw [if_neg (not_le.mpr hξ)] at h
    split_ifs at h with h2
    · norm_num at h
    · set v := (ξ - t + ε) / (2 * ε)
      have hv0 : 0 < v := div_pos (by linarith) (by linarith)
      have hv1 : v < 1 := (div_lt_one (by linarith)).mpr (by linarith [not_le.mp h2])
      nlinarith [mul_pos hv0 hv0]
  · intro h
    rw [if_pos h]

/-- For every $1.7\le b\le34$ (the item is `lower_plateau_lengths_bi`): with
$L_1=b(1-r)(1-t_b-\varepsilon)$ and $L_2=b(1-r)(t_b-\varepsilon)/r$, on the interval
$[ba_{\ell+1},ba_\ell]$ below the node $ba_\ell$ the derivative equals $a_\ell$ exactly from
$ba_\ell-a_\ell L_1$ on; on the same interval, above the node $ba_{\ell+1}$, it equals
$a_{\ell+1}$ exactly up to $ba_{\ell+1}+a_{\ell+1}L_2$; and $L_1,L_2>1/2$. -/
theorem lower_plateau_lengths {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (L₁ L₂ : ℝ)
    (hL₁ : L₁ = b * (1 - LScalarGeometric.theta) * (1 - LScalarRamp.center b - LScalarRamp.epsilon))
    (hL₂ : L₂ = b * (1 - LScalarGeometric.theta) * (LScalarRamp.center b - LScalarRamp.epsilon) /
      LScalarGeometric.theta) :
    (∀ (ℓ : ℕ) (x : ℝ), b * LScalarGeometric.scale (ℓ + 1) ≤ x → x ≤ b * LScalarGeometric.scale ℓ →
      (deriv (LScalar.phi b) x = LScalarGeometric.scale ℓ ↔
        b * LScalarGeometric.scale ℓ - LScalarGeometric.scale ℓ * L₁ ≤ x)) ∧
      (∀ (ℓ : ℕ) (x : ℝ), b * LScalarGeometric.scale (ℓ + 1) ≤ x → x ≤ b * LScalarGeometric.scale ℓ →
        (deriv (LScalar.phi b) x = LScalarGeometric.scale (ℓ + 1) ↔
          x ≤ b * LScalarGeometric.scale (ℓ + 1) + LScalarGeometric.scale (ℓ + 1) * L₂)) ∧
      1 / 2 < L₁ ∧ 1 / 2 < L₂ := by
  have hb : 0 < b := by linarith
  have hθ := LScalarGeometric.theta_pos
  have hθ1 := LScalarGeometric.theta_lt_one
  have hε : (0 : ℝ) < LScalarRamp.epsilon := by norm_num [LScalarRamp.epsilon]
  have hplat := LScalarRamp.plateau_lengths hl hr
  refine ⟨fun ℓ x hlo hhi => ?_, fun ℓ x hlo hhi => ?_, by rw [hL₁]; exact hplat.1,
    by rw [hL₂]; exact hplat.2⟩
  all_goals
    have hs := LScalarGeometric.scale_pos ℓ
    have hd := (lower_scalar_derivatives hl hr ℓ x _ hlo hhi rfl).1.deriv
    set ξ := (x / (b * LScalarGeometric.scale ℓ) - LScalarGeometric.theta) / (1 - LScalarGeometric.theta)
      with hξdef
    have h1θ : (0 : ℝ) < 1 - LScalarGeometric.theta := sub_pos.mpr hθ1
    have hba : 0 < b * LScalarGeometric.scale ℓ := mul_pos hb hs
    have hx : x = b * LScalarGeometric.scale ℓ * (LScalarGeometric.theta + (1 - LScalarGeometric.theta) * ξ) := by
      have e1 : (1 - LScalarGeometric.theta) * ξ = x / (b * LScalarGeometric.scale ℓ) - LScalarGeometric.theta := by
        rw [hξdef]
        field_simp
        ring
      rw [e1, add_sub_cancel]
      field_simp
    have hpos : 0 < b * LScalarGeometric.scale ℓ * (1 - LScalarGeometric.theta) := mul_pos hba h1θ
    rw [hd]
  · rw [show LScalarGeometric.scale ℓ * (LScalarGeometric.theta + (1 - LScalarGeometric.theta) *
        cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon ξ) = LScalarGeometric.scale ℓ ↔
        cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon ξ = 1 from by
      constructor
      · intro h
        have h' := mul_left_cancel₀ hs.ne' (h.trans (mul_one _).symm)
        have : (1 - LScalarGeometric.theta) * (cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon ξ - 1) = 0 := by
          linarith
        rcases mul_eq_zero.mp this with h0 | h0 <;> linarith
      · intro h
        rw [h]
        ring, cubicRamp_eq_one_iff hε]
    have hthr : b * LScalarGeometric.scale ℓ - LScalarGeometric.scale ℓ * L₁ =
        b * LScalarGeometric.scale ℓ * (LScalarGeometric.theta + (1 - LScalarGeometric.theta) *
          (LScalarRamp.center b + LScalarRamp.epsilon)) := by
      rw [hL₁]; ring
    rw [hthr]
    conv_rhs => rw [hx]
    constructor
    · intro h
      nlinarith [mul_le_mul_of_nonneg_left h hpos.le]
    · intro h
      by_contra hc
      push_neg at hc
      nlinarith [mul_lt_mul_of_pos_left hc hpos]
  · rw [LScalarGeometric.scale_succ]
    rw [show LScalarGeometric.scale ℓ * (LScalarGeometric.theta + (1 - LScalarGeometric.theta) *
        cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon ξ) = LScalarGeometric.theta * LScalarGeometric.scale ℓ ↔
        cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon ξ = 0 from by
      constructor
      · intro h
        have : LScalarGeometric.scale ℓ * ((1 - LScalarGeometric.theta) *
            cubicRamp (LScalarRamp.center b) LScalarRamp.epsilon ξ) = 0 := by linarith
        rcases mul_eq_zero.mp this with h0 | h0
        · linarith
        · rcases mul_eq_zero.mp h0 with h1 | h1
          · linarith
          · exact h1
      · intro h
        rw [h]
        ring, cubicRamp_eq_zero_iff hε]
    have hthr : b * (LScalarGeometric.theta * LScalarGeometric.scale ℓ) +
        LScalarGeometric.theta * LScalarGeometric.scale ℓ * L₂ =
        b * LScalarGeometric.scale ℓ * (LScalarGeometric.theta + (1 - LScalarGeometric.theta) *
          (LScalarRamp.center b - LScalarRamp.epsilon)) := by
      rw [hL₂]; field_simp; ring
    rw [hthr]
    conv_rhs => rw [hx]
    constructor
    · intro h
      nlinarith [mul_le_mul_of_nonneg_left h hpos.le]
    · intro h
      by_contra hc
      push_neg at hc
      nlinarith [mul_lt_mul_of_pos_left hc hpos]

/-- Item `A/lower_curvature/disp/016` (`paper/appendices/lower_curvature.tex:242-245`), with lines
241 and 246-247: "The constant-derivative lengths below and above $ba_\ell$, divided by
$a_\ell$, are
\[ b(1-r)(1-t_b-\varepsilon),\qquad b(1-r)(t_b-\varepsilon)/r, \]
both greater than $1/2$ for these values of $b$; the affine outer extension covers the upper side
when $\ell=0$." For each of the values $b=b_i$: on the
interval $[ba_{\ell+1},ba_\ell]$ below the node $ba_\ell$ the derivative equals $a_\ell$ exactly
from $ba_\ell-a_\ell L_1$ on; on the same interval, above the node $ba_{\ell+1}$, it equals
$a_{\ell+1}$ exactly up to $ba_{\ell+1}+a_{\ell+1}L_2$. -/
theorem lower_plateau_lengths_bi (i : Fin 3) {b : ℝ} (hb : b = LEmbedding.parameter i) (L₁ L₂ : ℝ)
    (hL₁ : L₁ = b * (1 - LScalarGeometric.theta) * (1 - LScalarRamp.center b - LScalarRamp.epsilon))
    (hL₂ : L₂ = b * (1 - LScalarGeometric.theta) * (LScalarRamp.center b - LScalarRamp.epsilon) /
      LScalarGeometric.theta) :
    (∀ (ℓ : ℕ) (x : ℝ), b * LScalarGeometric.scale (ℓ + 1) ≤ x → x ≤ b * LScalarGeometric.scale ℓ →
      (deriv (LScalar.phi b) x = LScalarGeometric.scale ℓ ↔
        b * LScalarGeometric.scale ℓ - LScalarGeometric.scale ℓ * L₁ ≤ x)) ∧
      (∀ (ℓ : ℕ) (x : ℝ), b * LScalarGeometric.scale (ℓ + 1) ≤ x → x ≤ b * LScalarGeometric.scale ℓ →
        (deriv (LScalar.phi b) x = LScalarGeometric.scale (ℓ + 1) ↔
          x ≤ b * LScalarGeometric.scale (ℓ + 1) + LScalarGeometric.scale (ℓ + 1) * L₂)) ∧
      1 / 2 < L₁ ∧ 1 / 2 < L₂ :=
  lower_plateau_lengths (parameter_range hb).1 (parameter_range hb).2 L₁ L₂ hL₁ hL₂

/-- For every $1.7\le b\le34$ (the item is `lower_plateau_bi`):
$\psi_b(ba_\ell+h)=a_\ell^2+a_\ell h$ for $|h|\le a_\ell/2$. -/
theorem lower_plateau {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (ℓ : ℕ) (h : ℝ)
    (hh : |h| ≤ LScalarGeometric.scale ℓ / 2) :
    LScalar.phi b (b * LScalarGeometric.scale ℓ + h) = LScalarGeometric.scale ℓ ^ 2 + LScalarGeometric.scale ℓ * h :=
  LScalar.phi_plateau hl hr ℓ hh

/-- Item `A/lower_curvature/disp/017`, equation `art:lower_plateau`
(`paper/appendices/lower_curvature.tex:248-250`): "Consequently
\[ \psi_b(ba_\ell+h)=a_\ell^2+a_\ell h\qquad(|h|\le a_\ell/2)." \]
For each of the values $b=b_i$ and every $\ell$. -/
theorem lower_plateau_bi (i : Fin 3) {b : ℝ} (hb : b = LEmbedding.parameter i) (ℓ : ℕ) (h : ℝ)
    (hh : |h| ≤ LScalarGeometric.scale ℓ / 2) :
    LScalar.phi b (b * LScalarGeometric.scale ℓ + h) = LScalarGeometric.scale ℓ ^ 2 + LScalarGeometric.scale ℓ * h :=
  lower_plateau (parameter_range hb).1 (parameter_range hb).2 ℓ h hh

/-- For every $1.7\le b\le34$ (the item is `lower_scalar_not_twice_bi`): the difference quotients
of $\psi_b'$ at zero along $ba_\ell$ and $(b+1/4)a_\ell$ are $1/b$ and $1/(b+1/4)$, and $\psi_b'$
is not differentiable at zero. -/
theorem lower_scalar_not_twice {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    deriv (LScalar.phi b) 0 = 0 ∧
      (∀ ℓ, (deriv (LScalar.phi b) (b * LScalarGeometric.scale ℓ) - deriv (LScalar.phi b) 0) /
          (b * LScalarGeometric.scale ℓ - 0) = 1 / b ∧
        (deriv (LScalar.phi b) ((b + 1/4) * LScalarGeometric.scale ℓ) - deriv (LScalar.phi b) 0) /
          ((b + 1/4) * LScalarGeometric.scale ℓ - 0) = 1 / (b + 1/4)) ∧
      ¬ DifferentiableAt ℝ (deriv (LScalar.phi b)) 0 := by
  have hz : deriv (LScalar.phi b) 0 = 0 := by rw [LScalar.deriv_phi hl hr, LScalar.phiFirst_zero hl hr]
  refine ⟨hz, fun ℓ => ?_, LScalar.phi_not_twice_differentiable_zero hl hr⟩
  rw [hz, sub_zero, sub_zero, sub_zero, sub_zero]
  exact ⟨LScalar.derivative_ratio_on_nodes hl hr ℓ, LScalar.derivative_ratio_on_shifted_nodes hl hr ℓ⟩

/-- Item `A/lower_curvature/prose/018` (`paper/appendices/lower_curvature.tex:251-253`): "At zero,
the difference quotients of $\psi_b'$ along $ba_\ell$ and $(b+1/4)a_\ell$ equal $1/b$ and
$1/(b+1/4)$, respectively. Thus its second derivative at zero does not exist." For each of the
values $b=b_i$. -/
theorem lower_scalar_not_twice_bi (i : Fin 3) {b : ℝ} (hb : b = LEmbedding.parameter i) :
    deriv (LScalar.phi b) 0 = 0 ∧
      (∀ ℓ, (deriv (LScalar.phi b) (b * LScalarGeometric.scale ℓ) - deriv (LScalar.phi b) 0) /
          (b * LScalarGeometric.scale ℓ - 0) = 1 / b ∧
        (deriv (LScalar.phi b) ((b + 1/4) * LScalarGeometric.scale ℓ) - deriv (LScalar.phi b) 0) /
          ((b + 1/4) * LScalarGeometric.scale ℓ - 0) = 1 / (b + 1/4)) ∧
      ¬ DifferentiableAt ℝ (deriv (LScalar.phi b)) 0 :=
  lower_scalar_not_twice (parameter_range hb).1 (parameter_range hb).2

/-- Item `A/lower_curvature/disp/018`, equation `art:lower_objective`
(`paper/appendices/lower_curvature.tex:256-261`): "Define
\[ f_i(x)=\tfrac\mu2\|x\|^2+\psi_{b_i}(q_i^Tx)\ (i=0,1,2),\qquad f_3(x)=\tfrac\mu2\|x\|^2+x_2,
   \qquad F=\max_if_i." \] -/
theorem lower_objective_def (x : Vec 2) :
    (∀ i : Fin 3, LEmbedding.branch i.castSucc x =
      LEmbedding.mu / 2 * sqNorm x + LScalar.phi (LEmbedding.parameter i) (dot (LEmbedding.slope i) x)) ∧
      LEmbedding.branch 3 x = LEmbedding.mu / 2 * sqNorm x + x 1 ∧
      LEmbedding.objective x = Finset.univ.sup' Finset.univ_nonempty (fun i => LEmbedding.branch i x) := by
  refine ⟨fun i => ?_, rfl, LEmbedding.objective_eq_max x⟩
  rw [LEmbedding.branch, LEmbedding.residualBranch_old]
  rfl

/-- The gradient of a branch is the library's `LEmbedding.branchGradient`. -/
theorem branch_gradient_eq (i : Fin 4) (x : Vec 2) :
    coordinateGradient (LEmbedding.branch i) x = LEmbedding.branchGradient i x :=
  DeterministicLineSearch.actual_coordinateGradient (LEmbedding.branch_hasGradient i x)

/-- Item `A/lower_curvature/prose/019` (`paper/appendices/lower_curvature.tex:262`): "Each branch
is globally $\mu$-strongly convex and $C^{1,1}$." -/
theorem branches_regular (i : Fin 4) :
    FixedNormal.EuclideanStrongConvexOn univ LEmbedding.mu (LEmbedding.branch i) ∧
      ContDiff ℝ 1 (LEmbedding.branch i) ∧
      ∃ L : ℝ, ∀ x y, ‖euclideanVector (coordinateGradient (LEmbedding.branch i) x -
        coordinateGradient (LEmbedding.branch i) y)‖ ≤ L * ‖euclideanVector (x - y)‖ := by
  refine ⟨LEmbedding.branch_strongConvex i, LEmbedding.branch_contDiff i, 512, fun x y => ?_⟩
  rw [branch_gradient_eq, branch_gradient_eq]
  exact euclid_le_of_sqNorm_le (by norm_num) (LEmbedding.branch_gradient_bound i x y)

/-- Item `A/lower_curvature/prose/020` (`paper/appendices/lower_curvature.tex:263-266`): "For
$i<3$, choose a vector $v_i$ with $q_i^Tv_i=1$. Restricting $f_i$ to $tv_i$ and subtracting its
smooth quadratic term recovers $\psi_{b_i}(t)$, so these three branches are not twice
differentiable at zero. An invertible linear change preserves this obstruction." -/
theorem ridge_restriction :
    (∀ i : Fin 3, ∃ v : Vec 2, dot (LEmbedding.slope i) v = 1) ∧
      (∀ (i : Fin 3) (v : Vec 2), dot (LEmbedding.slope i) v = 1 → ∀ t : ℝ,
        LEmbedding.branch i.castSucc (t • v) - LEmbedding.mu / 2 * sqNorm (t • v) =
          LScalar.phi (LEmbedding.parameter i) t) ∧
      (∀ i : Fin 3, ¬ DifferentiableAt ℝ (fderiv ℝ (LEmbedding.branch i.castSucc)) (0 : Vec 2)) ∧
      ∀ (i : Fin 3) (A : Mat 2), A.det ≠ 0 →
        ¬ DifferentiableAt ℝ (fderiv ℝ (fun z => LEmbedding.branch i.castSucc (A *ᵥ z))) (0 : Vec 2) := by
  refine ⟨fun i => ?_, fun i v hv t => ?_, ArticleBranchRegularity.branch_not_twice_differentiable_zero,
    fun i A hA hd => ?_⟩
  · have hb : LEmbedding.parameter i ≠ 0 := by
      have := (LEmbedding.parameter_bounds i).1; intro h; rw [h] at this; norm_num at this
    refine ⟨(LEmbedding.parameter i)⁻¹ • LEmbedding.center, ?_⟩
    rw [dot_smul_right]
    change (LEmbedding.parameter i)⁻¹ * LEmbedding.parameter i = 1
    exact inv_mul_cancel₀ hb
  · rw [(lower_objective_def (t • v)).1 i, dot_smul_right, hv, mul_one]
    ring
  · have h := (AffineWhitening.second_differentiableAt_iff A hA (LEmbedding.branch i.castSucc) 0).mp hd
    rw [Matrix.mulVec_zero] at h
    exact ArticleBranchRegularity.branch_not_twice_differentiable_zero i h

/-- Item `A/lower_curvature/prose/010` (`paper/appendices/lower_curvature.tex:11-14`): "The price of
retaining a positive lower curvature bound is the loss of second differentiability of three of the
four branches at the minimizer." (Corrected on 15 October 2026, M8 and M30; it said "of the
branches" and "at the accumulation point".) The first three branches $f_0,f_1,f_2$ of `art:lower_objective` are not
twice differentiable at zero, the point where the bad starts accumulate, and neither are the
whitened branches $f_i(Az)$ of Theorem `art:local-failure-lower` (`LUniform.smoothBranch`); the
fourth branch $f_3(x)=\mu\|x\|^2/2+x_2$ is a quadratic, twice differentiable at every point, also
after the whitening. -/
theorem branch_second_differentiability :
    (∀ i : Fin 3, ¬ DifferentiableAt ℝ (fderiv ℝ (LEmbedding.branch i.castSucc)) (0 : Vec 2)) ∧
      (∀ i : Fin 3, ¬ DifferentiableAt ℝ (fderiv ℝ (LUniform.smoothBranch i.castSucc)) (0 : Vec 2)) ∧
      (∀ x : Vec 2, DifferentiableAt ℝ (fderiv ℝ (LEmbedding.branch 3)) x) ∧
      ∀ z : Vec 2, DifferentiableAt ℝ (fderiv ℝ (LUniform.smoothBranch 3)) z :=
  ⟨ArticleBranchRegularity.branch_not_twice_differentiable_zero,
    LUniform.branch_not_twice_differentiable_zero,
    fun x => (LEmbedding.branch_last_second_hasFDerivAt x).differentiableAt,
    fun z => (AffineWhitening.second_differentiableAt_iff LUniform.coordinateMatrix
      LUniform.coordinateMatrix_invertible (LEmbedding.branch 3) z).mpr
      (LEmbedding.branch_last_second_hasFDerivAt _).differentiableAt⟩

/-- Item `A/lower_curvature/prose/021` (`paper/appendices/lower_curvature.tex:267-270`): "For the
first three branches, the gradient-Lipschitz constants are at most
$L_i=\mu+\max\{1,768/b_i\}\|q_i\|^2$. Direct substitution of the rational root bounds gives
$L_0<439$, $L_1<446$ and $L_2<27$; hence $512$ is a common constant, also covering the fourth
branch." Euclidean Lipschitz bounds for the actual gradients. -/
theorem branch_gradient_constants :
    (∀ (i : Fin 3) (x y : Vec 2),
      ‖euclideanVector (coordinateGradient (LEmbedding.branch i.castSucc) x -
        coordinateGradient (LEmbedding.branch i.castSucc) y)‖ ≤
      (LEmbedding.mu + max 1 (768 / LEmbedding.parameter i) * sqNorm (LEmbedding.slope i)) *
        ‖euclideanVector (x - y)‖) ∧
      LEmbedding.mu + max 1 (768 / LEmbedding.parameter 0) * sqNorm (LEmbedding.slope 0) < 439 ∧
      LEmbedding.mu + max 1 (768 / LEmbedding.parameter 1) * sqNorm (LEmbedding.slope 1) < 446 ∧
      LEmbedding.mu + max 1 (768 / LEmbedding.parameter 2) * sqNorm (LEmbedding.slope 2) < 27 ∧
      ∀ (i : Fin 4) (x y : Vec 2),
        ‖euclideanVector (coordinateGradient (LEmbedding.branch i) x -
          coordinateGradient (LEmbedding.branch i) y)‖ ≤ 512 * ‖euclideanVector (x - y)‖ := by
  have hmax (i : Fin 3) : max 1 (768 / LEmbedding.parameter i) = 768 / LEmbedding.parameter i := by
    have h := LEmbedding.parameter_bounds i
    apply max_eq_right
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hL (i : Fin 3) : LEmbedding.mu + max 1 (768 / LEmbedding.parameter i) * sqNorm (LEmbedding.slope i) =
      LEmbedding.gradientBound i := by
    rw [hmax]; rfl
  refine ⟨fun i x y => ?_, ?_, ?_, ?_, fun i x y => ?_⟩
  · rw [branch_gradient_eq, branch_gradient_eq, hL]
    exact euclid_le_of_sqNorm_le (LEmbedding.gradientBound_pos i).le (LEmbedding.branch_old_gradient_bound i x y)
  · rw [hL]; simpa using LEmbedding.gradientBound_source 0
  · rw [hL]; simpa using LEmbedding.gradientBound_source 1
  · rw [hL]; simpa using LEmbedding.gradientBound_source 2
  · rw [branch_gradient_eq, branch_gradient_eq]
    exact euclid_le_of_sqNorm_le (by norm_num) (LEmbedding.branch_gradient_bound i x y)

/-- Item `A/lower_curvature/prose/022` (`paper/appendices/lower_curvature.tex:271-274`): "Since
$F(x)\ge\mu\|x\|^2/2$ and $F(0)=0$, the sublevels are compact and the
minimizer is unique. The first three gradients at zero vanish, whereas the fourth is $(0,1)^T$,
so the minimizer is nonsmooth." -/
theorem lower_objective_minimizer :
    (∀ x, LEmbedding.mu / 2 * sqNorm x ≤ LEmbedding.objective x) ∧ LEmbedding.objective 0 = 0 ∧
      (∀ a, IsCompact {x | LEmbedding.objective x ≤ a}) ∧
      (∀ x, LEmbedding.objective 0 ≤ LEmbedding.objective x) ∧
      (∀ x, LEmbedding.objective x = LEmbedding.objective 0 → x = 0) ∧
      (∀ i : Fin 3, coordinateGradient (LEmbedding.branch i.castSucc) 0 = 0) ∧
      coordinateGradient (LEmbedding.branch 3) 0 = ![0, 1] ∧
      ¬ DifferentiableAt ℝ LEmbedding.objective (0 : Vec 2) := by
  refine ⟨LEmbedding.objective_lower, LEmbedding.objective_zero, LEmbedding.objective_sublevels_compact,
    fun x => by rw [LEmbedding.objective_zero]; exact LEmbedding.objective_nonnegative x,
    fun x hx => LEmbedding.objective_unique_zero (hx.trans LEmbedding.objective_zero),
    fun i => by rw [branch_gradient_eq]; exact LEmbedding.branchGradient_zero i, ?_,
    LEmbedding.objective_not_differentiable_zero⟩
  rw [branch_gradient_eq]
  ext i
  fin_cases i <;> simp [LEmbedding.branchGradient, LEmbedding.residualGradient]

/-- Item `A/lower_curvature/prose/023` (`paper/appendices/lower_curvature.tex:276-279`): "At a
differentiable point of a finite maximum of $L$-smooth functions, all active gradients agree.
Inactive branches stay inactive locally; taking the maximum of the active upper Taylor bounds
therefore gives the local upper Taylor bound with constant $L$." For a maximum $F$ of branches
$f_i$ with $L$-Lipschitz (Euclidean) gradients $g_i$, differentiable at $x$ with gradient $a$. -/
theorem finite_max_local_taylor {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (g : Fin m → Vec n → Vec n) (L : ℝ) (hL : 0 ≤ L)
    (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (hF : ∀ z, F z = Finset.univ.sup' hne (fun i => f i z))
    (hg : ∀ i z, HasFDerivAt (f i) (gradientFunctional (g i z)) z)
    (hlip : ∀ i z w, sqNorm (g i z - g i w) ≤ L ^ 2 * sqNorm (z - w))
    (x a : Vec n) (hx : HasFDerivAt F (gradientFunctional a) x) :
    (∀ i, f i x = F x → g i x = a) ∧ (∀ i, f i x < F x → ∀ᶠ z in 𝓝 x, f i z < F z) ∧
      ∀ᶠ z in 𝓝 x, F z ≤ F x + dot a (z - x) + L / 2 * sqNorm (z - x) := by
  have hrep : ConvexSubdifferential.LocalFiniteMax F f x := by
    refine Eventually.of_forall fun z => ⟨?_, ?_⟩
    · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun i => f i z)
      exact ⟨i, by rw [hF z, hi]⟩
    · rintro _ ⟨i, rfl⟩
      rw [hF z]
      exact Finset.le_sup' (fun i => f i z) (Finset.mem_univ i)
  refine ⟨fun i hi => ?_, fun i hi => ?_,
    FiniteMaxHessian.finiteMax_local_upper_taylor hL hrep hx hg hlip⟩
  · have h := FiniteMaxHessian.active_derivative_eq hrep hx (hg i x)
      (ConvexSubdifferential.mem_activeIndices.mpr hi)
    exact AffineProjection.gradientFunctional_injective h
  · have hc : ContinuousAt (fun z => F z - f i z) x := hx.continuousAt.sub (hg i x).continuousAt
    filter_upwards [hc.eventually (eventually_gt_nhds (sub_pos.mpr hi))] with z hz
    linarith

/-- Item `A/lower_curvature/disp/019` (`paper/appendices/lower_curvature.tex:281-284`): "Applying
this with $L=512$ and combining it with strong convexity proves
\[ \mu I\preceq\nabla^2F(x)\preceq512I\quad\text{whenever }F\text{ is twice differentiable}." \]
-/
theorem lower_objective_hessian (x : Vec 2)
    (hfirst : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ LEmbedding.objective z)
    (hsecond : DifferentiableAt ℝ (fderiv ℝ LEmbedding.objective) x) :
    (RadialHessian.matrix LEmbedding.objective x).IsSymm ∧ ∀ v,
      LEmbedding.mu * sqNorm v ≤ dot v ((RadialHessian.matrix LEmbedding.objective x).mulVec v) ∧
      dot v ((RadialHessian.matrix LEmbedding.objective x).mulVec v) ≤ 512 * sqNorm v :=
  LEmbedding.actual_hessian_bounds hfirst hsecond

/-! ### Copying one entire orbit and fixing the initial matrix -/

/-- Item `A/lower_curvature/prose/025` (`paper/appendices/lower_curvature.tex:288`): "Let
$\bar x_\ell=a_\ell c_*$ and $C_*=1+\mu\|c_*\|^2/2$." -/
theorem copy_constants_def (ℓ : ℕ) :
    LEmbedding.copyCenter ℓ = LScalarGeometric.scale ℓ • LEmbedding.center ∧
      LEmbedding.offset = 1 + LEmbedding.mu / 2 * sqNorm LEmbedding.center :=
  ⟨rfl, rfl⟩

/-- Item `A/lower_curvature/disp/020`, equation `art:lower_local_model`
(`paper/appendices/lower_curvature.tex:291-293`): "For $y$ in a fixed sufficiently small
neighborhood of zero, \eqref{art:lower_plateau} yields
\[ F(\bar x_\ell+a_\ell y)=a_\ell^2\{C_*+Q_\mu(y)\}\qquad(\ell\ge1)." \]
Here $Q_\mu$ is taken with the fixed $\mu=1/4096$; the neighborhood is
`LEmbedding.localDomain` $=\{y:\|y\|_\infty<1,\ |q_i^Ty|<1/2\}$. -/
theorem lower_local_model :
    ∃ N ∈ 𝓝 (0 : Vec 2), ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ y ∈ N,
      LEmbedding.objective (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • y) =
        LScalarGeometric.scale ℓ ^ 2 * (LEmbedding.offset + LQuadraticSeed.objective LEmbedding.mu y) :=
  ⟨LEmbedding.localDomain, LEmbedding.localDomain_nhds, fun ℓ _ _ hy => LEmbedding.local_model ℓ hy⟩

/-- Item `A/lower_curvature/prose/026` (`paper/appendices/lower_curvature.tex:294-297`):
"Indeed, $|q_i^Ty|\le1/2$ puts each old branch in its affine scalar region, and expansion of the
common quadratic uses $q_i+\mu c_*=g_i$. The fourth branch is inactive there: its residual
$a_\ell(-32+y_2)$ is negative, while each old scalar residual is at least $a_\ell^2/2$." -/
theorem local_model_reasons (ℓ : ℕ) (y : Vec 2) (hy : y ∈ LEmbedding.localDomain) :
    (∀ i : Fin 3, |dot (LEmbedding.slope i) y| ≤ 1/2 →
      LScalar.phi (LEmbedding.parameter i)
          (dot (LEmbedding.slope i) (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • y)) =
        LScalarGeometric.scale ℓ ^ 2 +
          LScalarGeometric.scale ℓ * (LScalarGeometric.scale ℓ * dot (LEmbedding.slope i) y)) ∧
      (∀ i : Fin 3, LEmbedding.slope i + LEmbedding.mu • LEmbedding.center = SeedOrbit.gradient seedC seedD i) ∧
      (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • y) 1 = LScalarGeometric.scale ℓ * (-32 + y 1) ∧
      (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • y) 1 < 0 ∧
      ∀ i : Fin 3, LScalarGeometric.scale ℓ ^ 2 / 2 ≤ LScalar.phi (LEmbedding.parameter i)
        (dot (LEmbedding.slope i) (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • y)) := by
  have hs := LScalarGeometric.scale_pos ℓ
  have harg (i : Fin 3) := LEmbedding.copy_argument ℓ i y
  change ∀ i, dot (LEmbedding.slope i) (LEmbedding.copyPoint ℓ y) = _ at harg
  refine ⟨fun i hi => ?_, fun i => sub_add_cancel _ _, ?_, ?_, fun i => ?_⟩
  · change LScalar.phi _ (dot (LEmbedding.slope i) (LEmbedding.copyPoint ℓ y)) = _
    rw [harg i]
    have hh : |LScalarGeometric.scale ℓ * dot (LEmbedding.slope i) y| ≤ LScalarGeometric.scale ℓ / 2 := by
      rw [abs_mul, abs_of_pos hs]
      nlinarith
    exact LScalar.phi_plateau (LEmbedding.parameter_bounds i).1.le (LEmbedding.parameter_bounds i).2.le ℓ hh
  · change LScalarGeometric.scale ℓ * (-32) + LScalarGeometric.scale ℓ * y 1 = _
    ring
  · exact LEmbedding.last_residual_copy_negative ℓ hy
  · have h := LEmbedding.scalar_copy ℓ i (hy.2 i).le
    rw [LEmbedding.residualBranch_old] at h
    change LScalarGeometric.scale ℓ ^ 2 / 2 ≤ LScalar.phi _ (dot (LEmbedding.slope i) (LEmbedding.copyPoint ℓ y))
    rw [h]
    have := (abs_lt.mp (hy.2 i)).1
    nlinarith [sq_nonneg (LScalarGeometric.scale ℓ)]

/-- The admissible pair `c₁ = 10⁻⁴`, `c₂ = 1/2`, used to name pair-independent objects. -/
theorem fixedPair : LUniform.Admissible (1/10000) (1/2) := LUniform.sourcePair

/-- Item `A/lower_curvature/disp/021` (`paper/appendices/lower_curvature.tex:304-306`), with prose
item `A/lower_curvature/prose/027` (lines 299-303): "Choose, by
Proposition~\ref{art:quadratic_failure}, one bad orbit $(x_k^{\rm seed},H_k^{\rm seed})$ whose
initial point and queries all lie in this neighborhood; it is the same for every admissible pair
$(c_1,c_2)$. For every $\ell\ge1$, start at $\bar x_\ell+a_\ell x_0^{\rm seed}$ with the same
matrix $H_0^{\rm seed}$. Induction on the actual query tree gives
\[ x_k^{(\ell)}=\bar x_\ell+a_\ell x_k^{\rm seed},\qquad H_k^{(\ell)}=H_k^{\rm seed}." \]
(Text as corrected on 15 October 2026, M33 and M41: before, "all of whose queries" and "For every
$\ell$".) This theorem states the copies for every $\ell$, $\ell=0$ included; `copy_runs_from_one`
restricts it to $\ell\ge1$ as printed. The chosen orbit is `LUniform.source` (iterates `source.x`, matrices `source.H`), an actual
run of $Q_\mu$ ($\mu=1/4096$) for every admissible pair; the copies are actual runs of $F$ of
the implementation for every admissible pair and every $\ell$. -/
theorem copy_runs :
    (LUniform.source.H 0).PosDef ∧
      (∀ k, LUniform.source.x k ∈ LEmbedding.localDomain ∧ ∀ a ∈ trialHistory (phase k),
        LUniform.source.x k + a • bfgsStep (LUniform.source.H k)
          (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1 ∈
          LEmbedding.localDomain) ∧
      (∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
        ∃ R : AdmissibleBFGSRun 2 (LQuadraticSeed.objective LEmbedding.mu),
          R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ R.x = LUniform.source.x ∧ R.H = LUniform.source.H ∧
          ∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric (LQuadraticSeed.objective LEmbedding.mu) (R.x k)
            (R.H k) c₁ c₂ N = (some (R.α k), trialHistory (phase k))) ∧
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 → ∀ ℓ : ℕ,
        ∃ R : AdmissibleBFGSRun 2 LEmbedding.objective, R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
          (∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric LEmbedding.objective (R.x k) (R.H k) c₁ c₂ N =
            (some (R.α k), trialHistory (phase k))) ∧
          R.x 0 = LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x 0 ∧
          R.H 0 = LUniform.source.H 0 ∧
          ∀ k, R.x k = LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x k ∧
            R.H k = LUniform.source.H k := by
  obtain ⟨-, hx, hq⟩ := LUniform.source_spec
  refine ⟨LUniform.source.initial_posDef, fun k => ⟨hx k, fun a ha => ?_⟩, ?_, ?_⟩
  · obtain ⟨q, hqk, rfl⟩ := trial_history_witness (phase k) ha
    exact hq k q hqk
  · intro c₁ c₂ hc₁ hc₁' hc hc₂
    have h : LUniform.Admissible c₁ c₂ := ⟨hc₁, hc₁', hc, hc₂⟩
    exact ⟨LUniform.sourceRun h, rfl, rfl, rfl, rfl,
      fun k N hN => fromMetric_fuel_mono (LUniform.nonstrict_run_search h k) N hN⟩
  · intro c₁ c₂ hc₁ hc₁' hc hc₂ ℓ
    have h : LUniform.Admissible c₁ c₂ := ⟨hc₁, hc₁', hc, hc₂⟩
    exact ⟨LUniform.family LActualCopies.smoothData h ℓ, rfl, rfl,
      fun k N hN => fromMetric_fuel_mono
        (LUniform.copy_nonstrict_actual_search LActualCopies.smoothData h ℓ k) N hN, rfl, rfl,
      fun k => ⟨rfl, rfl⟩⟩

/-- Item `A/lower_curvature/disp/021` (`paper/appendices/lower_curvature.tex:304-306`), with prose
item `A/lower_curvature/prose/027` (lines 299-303), as corrected on 15 October 2026 (M33 and
M41, reader points R-F-1 and R-F-8): "Choose, by Proposition~\ref{art:quadratic_failure}, one
bad orbit $(x_k^{\rm seed},H_k^{\rm seed})$ whose initial point and queries all lie in this
neighborhood; it is the same for every admissible pair $(c_1,c_2)$. For every $\ell\ge1$, start
at $\bar x_\ell+a_\ell x_0^{\rm seed}$ with the same matrix $H_0^{\rm seed}$. Induction on the
actual query tree gives
\[ x_k^{(\ell)}=\bar x_\ell+a_\ell x_k^{\rm seed},\qquad H_k^{(\ell)}=H_k^{\rm seed}." \]
`copy_runs` restricted to `ℓ ≥ 1`, the range of `art:lower_local_model`; its second conjunct
places every iterate of the chosen orbit, the initial point included, and every query in the
local domain. -/
theorem copy_runs_from_one :
    (LUniform.source.H 0).PosDef ∧
      (∀ k, LUniform.source.x k ∈ LEmbedding.localDomain ∧ ∀ a ∈ trialHistory (phase k),
        LUniform.source.x k + a • bfgsStep (LUniform.source.H k)
          (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1 ∈
          LEmbedding.localDomain) ∧
      (∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
        ∃ R : AdmissibleBFGSRun 2 (LQuadraticSeed.objective LEmbedding.mu),
          R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ R.x = LUniform.source.x ∧ R.H = LUniform.source.H ∧
          ∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric (LQuadraticSeed.objective LEmbedding.mu) (R.x k)
            (R.H k) c₁ c₂ N = (some (R.α k), trialHistory (phase k))) ∧
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 → ∀ ℓ : ℕ, 1 ≤ ℓ →
        ∃ R : AdmissibleBFGSRun 2 LEmbedding.objective, R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
          (∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric LEmbedding.objective (R.x k) (R.H k) c₁ c₂ N =
            (some (R.α k), trialHistory (phase k))) ∧
          R.x 0 = LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x 0 ∧
          R.H 0 = LUniform.source.H 0 ∧
          ∀ k, R.x k = LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x k ∧
            R.H k = LUniform.source.H k := by
  obtain ⟨h1, h2, h3, h4⟩ := copy_runs
  exact ⟨h1, h2, h3, fun c₁ c₂ hc₁ hc₁' hc hc₂ ℓ _ => h4 c₁ c₂ hc₁ hc₁' hc hc₂ ℓ⟩

/-- Item `A/lower_curvature/prose/028` (`paper/appendices/lower_curvature.tex:307-312`): "This is
\eqref{art:matched-local-model} with spatial factor $a_\ell$ and objective factor $a_\ell^2$. The
covariance calculation \eqref{art:matched-scaling} preserves the matrix, while function
differences and directional products acquire the same positive factor. Thus each rejection,
acceptance and updated matrix is preserved. Equation~\eqref{art:lower_local_model} applies at
the initial point and to every query because the whole chosen seed orbit lies in its domain."
(Corrected on 15 October 2026, M33: before "applies to every query".) For the copy $\ell$ at step
$k$ and every attempted length $a$: the gradient and the direction scale by $a_\ell$ (so
$\lambda^2/\sigma=a_\ell^2/a_\ell^2=1$ keeps the matrix), the query is the scaled seed query, which
lies in the domain of the local model, and function differences and directional products are the
seed ones times $a_\ell^2$. This holds for every $k$, $k=0$ included, where the copy's point is its
initial point $\bar x_\ell+a_\ell x_0^{\rm seed}$; that $x_0^{\rm seed}$ itself lies in the domain of
the local model is the second conjunct of `copy_runs_from_one`. -/
theorem copy_transfer (ℓ k : ℕ) (a : ℝ) (ha : a ∈ trialHistory (phase k)) :
    LScalarGeometric.scale ℓ ^ 2 / LScalarGeometric.scale ℓ ^ 2 = 1 ∧
      coordinateGradient LEmbedding.objective (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x k) =
        LScalarGeometric.scale ℓ • coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k) ∧
      bfgsStep (LUniform.source.H k) (coordinateGradient LEmbedding.objective
          (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x k)) 1 =
        LScalarGeometric.scale ℓ • bfgsStep (LUniform.source.H k)
          (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1 ∧
      (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x k) +
          a • bfgsStep (LUniform.source.H k) (coordinateGradient LEmbedding.objective
            (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x k)) 1 =
        LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • (LUniform.source.x k +
          a • bfgsStep (LUniform.source.H k)
            (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1) ∧
      LUniform.source.x k + a • bfgsStep (LUniform.source.H k)
          (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1 ∈
        LEmbedding.localDomain ∧
      LEmbedding.objective (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • (LUniform.source.x k +
          a • bfgsStep (LUniform.source.H k)
            (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1)) -
        LEmbedding.objective (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x k) =
        LScalarGeometric.scale ℓ ^ 2 * (LQuadraticSeed.objective LEmbedding.mu (LUniform.source.x k +
          a • bfgsStep (LUniform.source.H k)
            (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1) -
          LQuadraticSeed.objective LEmbedding.mu (LUniform.source.x k)) ∧
      dot (coordinateGradient LEmbedding.objective (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ •
          (LUniform.source.x k + a • bfgsStep (LUniform.source.H k)
            (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1)))
          (LScalarGeometric.scale ℓ • bfgsStep (LUniform.source.H k)
            (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1) =
        LScalarGeometric.scale ℓ ^ 2 * dot (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu)
            (LUniform.source.x k + a • bfgsStep (LUniform.source.H k)
              (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1))
          (bfgsStep (LUniform.source.H k)
            (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1) := by
  set D := LActualCopies.smoothData
  set h := fixedPair
  set R := LUniform.sourceRun h
  have hs := LScalarGeometric.scale_pos ℓ
  have hgR : coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k) = R.g k := rfl
  obtain ⟨q, hqk, rfl⟩ := trial_history_witness (phase k) ha
  obtain ⟨hU, hd⟩ := LUniform.run_query_conditions h k q hqk
  have hgc : coordinateGradient LEmbedding.objective
      (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x k) =
      LScalarGeometric.scale ℓ • R.g k := by
    have hh := (LUniform.family D h ℓ).hasGradient k
    exact DeterministicLineSearch.actual_coordinateGradient hh
  have hstep : bfgsStep (LUniform.source.H k) (LScalarGeometric.scale ℓ • R.g k) 1 =
      LScalarGeometric.scale ℓ • bfgsStep (LUniform.source.H k) (R.g k) 1 := by
    simp only [bfgsStep, Matrix.mulVec_smul, smul_smul, mul_comm]
  have hqv : LEmbedding.objective (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ •
      (LUniform.source.x k + trialLength q • bfgsStep (LUniform.source.H k) (R.g k) 1)) =
      LScalarGeometric.scale ℓ ^ 2 * (LEmbedding.offset + LQuadraticSeed.objective LEmbedding.mu
        (LUniform.source.x k + trialLength q • bfgsStep (LUniform.source.H k) (R.g k) 1)) := by
    have h0 := D.query_value R (LUniform.point_in h) ℓ k (trialLength q) hU
    rw [D.query_identity] at h0
    exact h0
  have hrv : LEmbedding.objective (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x k) =
      LScalarGeometric.scale ℓ ^ 2 * (LEmbedding.offset + LQuadraticSeed.objective LEmbedding.mu
        (LUniform.source.x k)) := by
    have h0 := D.run_value R (LUniform.point_in h) ℓ k
    rw [D.run_x] at h0
    exact h0
  have hqg : HasFDerivAt LEmbedding.objective (gradientFunctional (LScalarGeometric.scale ℓ •
      coordinateGradient (LQuadraticSeed.objective LEmbedding.mu)
        (LUniform.source.x k + trialLength q • bfgsStep (LUniform.source.H k) (R.g k) 1)))
      (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ •
        (LUniform.source.x k + trialLength q • bfgsStep (LUniform.source.H k) (R.g k) 1)) := by
    have h0 := D.query_hasGradient R (LUniform.point_in h) ℓ k (trialLength q) hU hd
    rw [D.query_identity] at h0
    exact h0
  rw [hgc, hstep, hgR]
  refine ⟨div_self (by positivity), rfl, rfl, ?_, hU, ?_, ?_⟩
  · rw [smul_comm (trialLength q) (LScalarGeometric.scale ℓ), smul_add, add_assoc]
  · rw [hqv, hrv]
    ring
  · rw [DeterministicLineSearch.actual_coordinateGradient hqg, dot_smul_right]
    change LScalarGeometric.scale ℓ * dotProduct (LScalarGeometric.scale ℓ • _) _ = _
    rw [smul_dotProduct, smul_eq_mul]
    change _ = LScalarGeometric.scale ℓ ^ 2 * dotProduct _ _
    ring

/-- The gradient of an old branch at a copy center is $a_\ell g_i$. -/
theorem center_branch_gradient (ℓ : ℕ) (i : Fin 3) :
    coordinateGradient (LEmbedding.branch i.castSucc) (LEmbedding.copyCenter ℓ) =
      LScalarGeometric.scale ℓ • SeedOrbit.gradient seedC seedD i := by
  have hb := LEmbedding.parameter_bounds i
  rw [branch_gradient_eq]
  have hr (x : Vec 2) : LEmbedding.residualGradient i.castSucc x = LEmbedding.ridgeGradient i x := by
    fin_cases i <;> rfl
  have harg : dot (LEmbedding.slope i) (LEmbedding.copyCenter ℓ) =
      LEmbedding.parameter i * LScalarGeometric.scale ℓ := by
    change dot (LEmbedding.slope i) (LScalarGeometric.scale ℓ • LEmbedding.center) = _
    rw [dot_smul_right]
    change LScalarGeometric.scale ℓ * LEmbedding.parameter i = _
    ring
  have hslope : LScalar.phiFirst (LEmbedding.parameter i) (LEmbedding.parameter i * LScalarGeometric.scale ℓ) =
      LScalarGeometric.scale ℓ := by
    rw [LScalar.phiFirst_eq_positive (mul_nonneg (by linarith) (LScalarGeometric.scale_pos ℓ).le),
      LScalar.positiveSlope_node hb.1.le hb.2.le ℓ, pow_one]
  rw [LEmbedding.branchGradient, hr, LEmbedding.ridgeGradient, harg, hslope, LEmbedding.slope]
  change LEmbedding.mu • (LScalarGeometric.scale ℓ • LEmbedding.center) +
    LScalarGeometric.scale ℓ • (SeedOrbit.gradient seedC seedD i - LEmbedding.mu • LEmbedding.center) = _
  rw [smul_sub, smul_comm LEmbedding.mu (LScalarGeometric.scale ℓ)]
  abel

/-- Seed queries lie in the unit sup-ball, hence in the Euclidean ball of radius `2`. -/
theorem euclid_le_two_of_mem_localDomain {y : Vec 2} (hy : y ∈ LEmbedding.localDomain) :
    ‖euclideanVector y‖ ≤ 2 := by
  have h0 : |y 0| < 1 := (norm_le_pi_norm y 0).trans_lt hy.1
  have h1 : |y 1| < 1 := (norm_le_pi_norm y 1).trans_lt hy.1
  have hsq : ‖euclideanVector y‖ ^ 2 ≤ 2 ^ 2 := by
    rw [euclid_norm_sq]
    simp only [sqNorm, Fin.sum_univ_two]
    nlinarith [abs_lt.mp h0, abs_lt.mp h1]
  exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp hsq

/-- Item `A/lower_curvature/prose/029` (`paper/appendices/lower_curvature.tex:313-317`): "Thus
$x_k^{(\ell)}\to\bar x_\ell$ and $F(x_k^{(\ell)})\downarrow a_\ell^2C_*>0$. The three active
gradients at $\bar x_\ell$ are $a_\ell g_i$, whose convex hull excludes zero. All query norms
are at most $a_\ell(\|c_*\|+\sup_{\rm seed\ queries}\|x^{\rm seed}\|)\to0$." The copies
$x_k^{(\ell)}=\bar x_\ell+a_\ell x_k^{\rm seed}$ of `copy_runs`; the seed query norms (Euclidean)
form the bounded set `S`, and the copy queries are those of the copy runs. -/
theorem copy_limits (ℓ : ℕ) :
    Tendsto (fun k => LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x k) atTop
        (𝓝 (LEmbedding.copyCenter ℓ)) ∧
      StrictAnti (fun k => LEmbedding.objective
        (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x k)) ∧
      Tendsto (fun k => LEmbedding.objective
        (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x k)) atTop
        (𝓝 (LScalarGeometric.scale ℓ ^ 2 * LEmbedding.offset)) ∧
      LEmbedding.objective (LEmbedding.copyCenter ℓ) = LScalarGeometric.scale ℓ ^ 2 * LEmbedding.offset ∧
      0 < LScalarGeometric.scale ℓ ^ 2 * LEmbedding.offset ∧
      (∀ i : Fin 3, LEmbedding.branch i.castSucc (LEmbedding.copyCenter ℓ) =
          LEmbedding.objective (LEmbedding.copyCenter ℓ) ∧
        coordinateGradient (LEmbedding.branch i.castSucc) (LEmbedding.copyCenter ℓ) =
          LScalarGeometric.scale ℓ • SeedOrbit.gradient seedC seedD i) ∧
      LEmbedding.branch 3 (LEmbedding.copyCenter ℓ) < LEmbedding.objective (LEmbedding.copyCenter ℓ) ∧
      (0 : Vec 2) ∉ convexHull ℝ {LScalarGeometric.scale ℓ • g0, LScalarGeometric.scale ℓ • g1,
        LScalarGeometric.scale ℓ • g2 seedC seedD} ∧
      BddAbove {r : ℝ | ∃ k, ∃ a ∈ trialHistory (phase k), r = ‖euclideanVector (LUniform.source.x k +
        a • bfgsStep (LUniform.source.H k)
          (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1)‖} ∧
      (∀ k, ∀ a ∈ trialHistory (phase k),
        ‖euclideanVector ((LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x k) +
          a • bfgsStep (LUniform.source.H k) (coordinateGradient LEmbedding.objective
            (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • LUniform.source.x k)) 1)‖ ≤
        LScalarGeometric.scale ℓ * (‖euclideanVector LEmbedding.center‖ +
          sSup {r : ℝ | ∃ k, ∃ a ∈ trialHistory (phase k), r = ‖euclideanVector (LUniform.source.x k +
            a • bfgsStep (LUniform.source.H k)
              (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1)‖})) ∧
      Tendsto (fun m => LScalarGeometric.scale m * (‖euclideanVector LEmbedding.center‖ +
          sSup {r : ℝ | ∃ k, ∃ a ∈ trialHistory (phase k), r = ‖euclideanVector (LUniform.source.x k +
            a • bfgsStep (LUniform.source.H k)
              (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1)‖}))
        atTop (𝓝 0) := by
  set D := LActualCopies.smoothData
  set h := fixedPair
  set S : Set ℝ := {r : ℝ | ∃ k, ∃ a ∈ trialHistory (phase k), r = ‖euclideanVector (LUniform.source.x k +
    a • bfgsStep (LUniform.source.H k)
      (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1)‖} with hS
  have hs := LScalarGeometric.scale_pos ℓ
  have hcenter := LEmbedding.center_value ℓ
  have hSb : BddAbove S := by
    refine ⟨2, ?_⟩
    rintro r ⟨k, a, ha, rfl⟩
    exact euclid_le_two_of_mem_localDomain ((copy_runs.2.1 k).2 a ha)
  refine ⟨LUniform.copy_point_limit D h ℓ, strictAnti_nat_of_succ_lt
    (LUniform.family D h ℓ).objective_strict_decrease, LUniform.copy_value_limit D h ℓ, hcenter,
    mul_pos (sq_pos_of_pos hs) LEmbedding.offset_pos, fun i => ⟨?_, center_branch_gradient ℓ i⟩, ?_, ?_,
    hSb, fun k a ha => ?_, ?_⟩
  · have hb := LEmbedding.branch_copy ℓ i LEmbedding.zero_mem_localDomain
    simp only [LEmbedding.copyPoint, smul_zero, add_zero, LQuadraticSeed.branch_zero] at hb
    rw [hb, hcenter]
  · rw [hcenter]
    change LQuadraticSeed.quadratic LEmbedding.mu (LEmbedding.copyCenter ℓ) +
      (LScalarGeometric.scale ℓ • LEmbedding.center) 1 < _
    have hq : LQuadraticSeed.quadratic LEmbedding.mu (LEmbedding.copyCenter ℓ) =
        LScalarGeometric.scale ℓ ^ 2 * (LEmbedding.mu / 2 * sqNorm LEmbedding.center) := by
      change LEmbedding.mu / 2 * sqNorm (LScalarGeometric.scale ℓ • LEmbedding.center) = _
      rw [RadialPower.sqNorm_smul]
      ring
    rw [hq, LEmbedding.offset]
    simp [LEmbedding.center]
    nlinarith
  · rw [show ({LScalarGeometric.scale ℓ • g0, LScalarGeometric.scale ℓ • g1,
        LScalarGeometric.scale ℓ • g2 seedC seedD} : Set (Vec 2)) =
        LScalarGeometric.scale ℓ • ({g0, g1, g2 seedC seedD} : Set (Vec 2)) by
      rw [Set.smul_set_insert, Set.smul_set_insert, Set.smul_set_singleton],
      convexHull_smul, Set.zero_mem_smul_set_iff hs.ne', ← slopes_eq]
    exact LQuadraticSeed.zero_not_mem_convexHull
  · obtain ⟨q, hqk, rfl⟩ := trial_history_witness (phase k) ha
    have ht := copy_transfer ℓ k (trialLength q) ha
    rw [ht.2.2.2.1, show euclideanVector (LEmbedding.copyCenter ℓ + LScalarGeometric.scale ℓ • (LUniform.source.x k +
      trialLength q • bfgsStep (LUniform.source.H k)
        (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1)) =
      LScalarGeometric.scale ℓ • euclideanVector LEmbedding.center + LScalarGeometric.scale ℓ •
        euclideanVector (LUniform.source.x k + trialLength q • bfgsStep (LUniform.source.H k)
          (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1) from rfl]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_add]
    have hmem : ‖euclideanVector (LUniform.source.x k + trialLength q • bfgsStep (LUniform.source.H k)
        (coordinateGradient (LQuadraticSeed.objective LEmbedding.mu) (LUniform.source.x k)) 1)‖ ∈ S :=
      ⟨k, trialLength q, ha, rfl⟩
    have := le_csSup hSb hmem
    nlinarith
  · simpa only [zero_mul] using LScalar.scale_tendsto_zero.mul_const
      (‖euclideanVector LEmbedding.center‖ + sSup S)

/-- Item `A/lower_curvature/prose/030` (`paper/appendices/lower_curvature.tex:319-323`): "The seed
supplied by the stable manifold has a positive-definite initial matrix $H_0^{\rm seed}$, common to
every copy. Identity initialization is obtained by changing coordinates once for the whole
objective and the whole sequence of starts, rather than selecting a different objective for each
start. Set $A=(H_0^{\rm seed})^{1/2}$ and $\widetilde F(z)=F(Az)$." `LUniform.initialMetric` is
$H_0^{\rm seed}$ (the initial matrix of every copy, `copy_runs`), `LUniform.coordinateMatrix` is
its positive semidefinite square root $A$, and `LUniform.smoothObjective` is $\widetilde F$. -/
theorem whitening_setup :
    LUniform.initialMetric = LUniform.source.H 0 ∧ LUniform.initialMetric.PosDef ∧
      LUniform.coordinateMatrix.PosSemidef ∧
      LUniform.coordinateMatrix * LUniform.coordinateMatrix = LUniform.initialMetric ∧
      LUniform.coordinateMatrix.det ≠ 0 ∧
      ∀ z, LUniform.smoothObjective z = LEmbedding.objective (LUniform.coordinateMatrix *ᵥ z) :=
  ⟨rfl, LUniform.initialMetric_posDef, LUniform.initialMetric_posDef.posSemidef.posSemidef_sqrt,
    LUniform.coordinateMatrix_square, LUniform.coordinateMatrix_invertible, fun _ => rfl⟩

/-- Item `A/lower_curvature/disp/022` (`paper/appendices/lower_curvature.tex:325-328`), with prose
item `A/lower_curvature/prose/031` (lines 329-330): "The coordinate identities
\[ \widetilde g=A^Tg,\qquad \widetilde H=A^{-1}HA^{-T},\qquad \widetilde s=A^{-1}s \]
preserve both scalar line-search tests and \eqref{art:failure_update}". For an invertible $A$ and
$\widetilde F(z)=F(Az)$: gradients transform by $A^T$ at $A^{-1}x$, steps by $A^{-1}$, the
(non-strict) Armijo and Wolfe tests are equivalent, the inverse update commutes with the change of
coordinates, and the implementation's whole search is unchanged. -/
theorem whitening_identities (A : Mat 2) (hA : A.det ≠ 0) (F : Vec 2 → ℝ) :
    (∀ x g : Vec 2, HasFDerivAt F (gradientFunctional g) x →
      HasFDerivAt (fun z => F (A *ᵥ z)) (gradientFunctional (Aᵀ *ᵥ g)) (A⁻¹ *ᵥ x)) ∧
      (∀ (H : Mat 2) (g : Vec 2) (α : ℝ),
        bfgsStep (A⁻¹ * H * (A⁻¹)ᵀ) (Aᵀ *ᵥ g) α = A⁻¹ *ᵥ bfgsStep H g α) ∧
      (∀ (x p g : Vec 2) (c a : ℝ),
        NonStrictLineSearch.Armijo (fun z => F (A *ᵥ z)) (A⁻¹ *ᵥ x) (A⁻¹ *ᵥ p) (Aᵀ *ᵥ g) c a ↔
          NonStrictLineSearch.Armijo F x p g c a) ∧
      (∀ (x p g : Vec 2) (c a : ℝ),
        NonStrictLineSearch.Wolfe (fun z => F (A *ᵥ z)) (A⁻¹ *ᵥ x) (A⁻¹ *ᵥ p) (Aᵀ *ᵥ g) c a ↔
          NonStrictLineSearch.Wolfe F x p g c a) ∧
      (∀ (H : Mat 2) (s y : Vec 2),
        A⁻¹ * inverseBFGS H s y * (A⁻¹)ᵀ = inverseBFGS (A⁻¹ * H * (A⁻¹)ᵀ) (A⁻¹ *ᵥ s) (Aᵀ *ᵥ y)) ∧
      ∀ (x : Vec 2) (H : Mat 2) (c₁ c₂ : ℝ) (fuel : ℕ),
        NonStrictLineSearch.fromMetric (fun z => F (A *ᵥ z)) (A⁻¹ *ᵥ x) (A⁻¹ * H * (A⁻¹)ᵀ) c₁ c₂ fuel =
          NonStrictLineSearch.fromMetric F x H c₁ c₂ fuel :=
  ⟨fun x g hg => AffineWhitening.hasGradient_equiv A hA F x g hg,
    fun H g α => AffineWhitening.step_equiv A hA H g α,
    fun x p g c a => AffineWhitening.nonstrict_armijo_equiv A hA F x p g c a,
    fun x p g c a => AffineWhitening.nonstrict_wolfe_equiv A hA F x p g c a,
    fun H s y => AffineWhitening.update_equiv A hA H s y,
    fun x H c₁ c₂ fuel => AffineWhitening.nonstrict_fromMetric_equiv A hA F x H c₁ c₂ fuel⟩

/-- Item `A/lower_curvature/prose/032` (`paper/appendices/lower_curvature.tex:331`): "They give
$\widetilde H_0=I$ for this one fixed transformation." -/
theorem whitening_initial :
    LUniform.coordinateMatrix⁻¹ * LUniform.initialMetric * (LUniform.coordinateMatrix⁻¹)ᵀ = 1 :=
  AffineWhitening.squareRoot_initial_metric _ _

/-- Item `A/lower_curvature/prose/033` (`paper/appendices/lower_curvature.tex:332-334`):
"Strong-convexity and smoothness constants become $\underline\mu=\mu\lambda_{\min}(H_0^{\rm seed})$
and $\overline L=512\lambda_{\max}(H_0^{\rm seed})$." The whitened objective and its branches are
$\underline\mu$-strongly convex, the branch gradients are $\overline L$-Lipschitz, and
$\underline\mu I\preceq\nabla^2\widetilde F\preceq\overline LI$ at twice-differentiable points. -/
theorem whitening_constants :
    LUniform.lowerConstant = LEmbedding.mu *
        AffineWhitening.minEigenvalue LUniform.initialMetric LUniform.initialMetric_posDef.1 ∧
      LUniform.upperConstant = 512 * AffineWhitening.maxEigenvalue LUniform.initialMetric LUniform.initialMetric_posDef.1 ∧
      FixedNormal.EuclideanStrongConvexOn univ LUniform.lowerConstant LUniform.smoothObjective ∧
      (∀ i, FixedNormal.EuclideanStrongConvexOn univ LUniform.lowerConstant (LUniform.smoothBranch i)) ∧
      (∀ i x y, ‖euclideanVector (coordinateGradient (LUniform.smoothBranch i) x -
        coordinateGradient (LUniform.smoothBranch i) y)‖ ≤ LUniform.upperConstant * ‖euclideanVector (x - y)‖) ∧
      ∀ x : Vec 2, (∀ᶠ z in 𝓝 x, DifferentiableAt ℝ LUniform.smoothObjective z) →
        DifferentiableAt ℝ (fderiv ℝ LUniform.smoothObjective) x →
        (RadialHessian.matrix LUniform.smoothObjective x).IsSymm ∧ ∀ v,
          LUniform.lowerConstant * sqNorm v ≤ dot v ((RadialHessian.matrix LUniform.smoothObjective x).mulVec v) ∧
          dot v ((RadialHessian.matrix LUniform.smoothObjective x).mulVec v) ≤ LUniform.upperConstant * sqNorm v := by
  refine ⟨rfl, rfl, LUniform.smooth_strongConvex, fun i => (LUniform.smooth_branch_regular i).2.1,
    fun i x y => ?_, fun x hf hs => LUniform.smooth_actual_hessian hf hs⟩
  rw [DeterministicLineSearch.actual_coordinateGradient ((LUniform.smooth_branch_regular i).2.2.1 x),
    DeterministicLineSearch.actual_coordinateGradient ((LUniform.smooth_branch_regular i).2.2.1 y)]
  exact euclid_le_of_sqNorm_le LUniform.upperConstant_pos.le ((LUniform.smooth_branch_regular i).2.2.2 x y)

/-! ### Non-vacuity -/

/-- The standing assumptions of this file can hold at once: $\mu=1/4096>0$; the two values
$b_i$ lie in $[1.7,34]$, the range of the general forms of the statements about $\psi_b$; the
Jacobian matrix of the shape map exists as a matrix; every neighbourhood of the boundary seed
$P_*$ contains a state with $\tau>0$ (so the hypotheses of part (i) of `lower_hyperbolic` hold on
any neighbourhood); an admissible pair exists. -/
example : (0 : ℝ) < LEmbedding.mu ∧
    ((17 : ℝ)/10 ≤ LEmbedding.parameter 0 ∧ LEmbedding.parameter 0 ≤ 34) ∧
    ((17 : ℝ)/10 ≤ LEmbedding.parameter 2 ∧ LEmbedding.parameter 2 ≤ 34) ∧
    (∃ J : Mat 2, ∀ i j, J i j =
      fderiv ℝ (LShapeDerivative.shapeMap seedC seedD) ![0, 1] (Pi.single j 1) i) ∧
    (∀ N ∈ 𝓝 LNormalizedReturn.seed, ∃ w ∈ N, 0 < LNormalizedReturn.scale w) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ 1/3 ∧ c₁ < c₂ ∧ c₂ < 1 := by
  refine ⟨LEmbedding.mu_pos, ⟨(LEmbedding.parameter_bounds 0).1.le, (LEmbedding.parameter_bounds 0).2.le⟩,
    ⟨(LEmbedding.parameter_bounds 2).1.le, (LEmbedding.parameter_bounds 2).2.le⟩,
    ⟨fun i j => fderiv ℝ (LShapeDerivative.shapeMap seedC seedD) ![0, 1] (Pi.single j 1) i,
      fun _ _ => rfl⟩, fun N hN => ?_,
    1/10000, 1/2, by norm_num, by norm_num, by norm_num, by norm_num⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hN
  let e4 : LNormalizedReturn.State := Pi.single (4 : Fin 5) (1 : ℝ)
  have he4 : ‖e4‖ = 1 := by simp [e4, Pi.norm_single]
  refine ⟨LNormalizedReturn.seed + (ε / 2) • e4, hball ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (half_pos hε), he4]
    linarith
  · have : LNormalizedReturn.scale (LNormalizedReturn.seed + (ε / 2) • e4) = 0 + ε / 2 := by
      change LNormalizedReturn.seed 4 + (ε / 2) * e4 4 = 0 + ε / 2
      simp [e4]
      rfl
    rw [this]
    linarith

end BfgsCoverage.Article.LowerCurvature
