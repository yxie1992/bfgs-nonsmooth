import BfgsArticle.Coverage.Article.LowerCurvature
import BfgsArticle.Coverage.Article.Failure
import BfgsArticle.Coverage.Article.SeedCertificate
import BfgsVerification.LShapePrecision
import BfgsVerification.LReturnLocalInverse
import BfgsVerification.LStepEmbeddingTargets
import BfgsVerification.LScalarStepTargets
import BfgsVerification.LIdentityGeometry

/-!
# Lean coverage: `companion/chapters/13_L.tex`

Chapter 13 of the companion ("Failure with positive lower curvature", label `comp:L`). Register:
`editorial/lean_coverage/register/C_13_L.json`. The chapter is close to the article's Appendix
`art:lower_curvature` and Theorem `art:local-failure-lower`; this module imports the article
coverage modules `LowerCurvature`, `Failure` and `SeedCertificate` and reuses their theorems, and
the register points identical items to the article items (`SAME_AS`).

## Reading of the chapter

* The line search is the specified unit-first bracketing search `NonStrictLineSearch.fromMetric`
  (Armijo first, weak Wolfe second, brackets `0` and `+∞`, bisection after bracketing, doubling
  otherwise), stated for every trial budget `N ≥ 5`; the strict tests give the same decisions on
  every run of the chapter (`strict_margins_same_decisions`). Runs are `AdmissibleBFGSRun`s (actual
  gradients, the unmodified inverse update `inverseBFGS`). The pair is any
  $0<c_1\le1/3$, $c_1<c_2<1$ (`LUniform.Admissible`, `admissible_iff`); the orbits, objectives and
  initial points are chosen before the pair (13 October transformation of the chapter).
* Notation: $\varphi_b$ of the companion is the article's $\psi_b$, `LScalar.phi b`; $(b,e)$ are
  the article's $(\zeta,\eta)$; $r=(M_3)_{11}$ in Section 13.3 is the article's $\hat\rho$,
  `LNormalizedReturn.returnFactor μ`, while $r=1/128$ in Section 13.5 is `LScalarGeometric.theta`;
  $\vartheta_b$ is the article's $t_b$, `LScalarRamp.center b`; $n$, $p_n$ are the article's
  $\ell$, $\bar x_\ell$ (`LEmbedding.copyCenter`); $(c,d)$ is $(c_\circ,d_\circ)$ =
  (`seedC`, `seedD`); $\bar x_k,\bar H_k$ is the chosen orbit `LUniform.source`, $\bar H_0$ =
  `LUniform.initialMetric`, $A$ = `LUniform.coordinateMatrix`.
* Theorem `L:thm:local` is stated for two objectives: the whitened four-branch function
  `LUniform.smoothObjective` and the whitened step embedding `stepObjective` (defined here, with
  the same fixed matrix `LUniform.coordinateMatrix`, so that both families serve every pair).
* The $\mu$ in the last column of display `L:eq:jacobian` is proved, not only notation: the
  blocks $C,a,b$ are the same for every $\mu>0$ (`jacobian_block_form`, through
  `returnMap_scale`).

## Discrepancies (see the register)

* Line 3 (`C/13_L/prose/002`, the M8 pattern): "The local finite-branch functions have Lipschitz
  gradients but lose second differentiability at the accumulation point": only three of the four
  branches lose it (`branch_regularity`).
* Theorem `L:thm:local` (line 59): the final clause "the latter version has a countable polyhedral
  nonsmooth part, not a finite smooth-branch representation", read literally, is false: the step
  version is also a maximum of ten convex, globally $C^{1,1}$, uniformly strongly convex branches
  (sketch in the register, not formalized); `local_failure` states everything else and the
  descriptive reading (the nonsmooth part is a countable polyhedral function).
* Line 413 (`C/13_L/prose/082`): "This chapter uses the fixed line-search pair displayed in this
  chapter; D's wider parameter family is not imported" is a leftover of the fixed-pair edition:
  the chapter now states its theorems for the same family as Chapter D.

## Items

| Item | Lines | Lean |
|---|---|---|
| `disp/001`, prose `004`-`007` | 29-40 | `admissible_iff`, `strict_margins_same_decisions` |
| `theorem/L:thm:global` (`disp/003`) | 42-48 | `global_failure` |
| `theorem/L:thm:local` (`disp/004`) | 51-60 | `local_failure` (with `stepObjective`, `runs_of_uniform`) |
| prose `011`, `012` (OPEN) | 61 | `not_four_C2_branches`, `FourC2BranchLocalFailure` |
| `disp/007`, `disp/009`, `disp/010`, `disp/011`, prose `017`-`025` | 75-122 | `root_equations`, `seed_ratio_def`, `seed_matrix_closure`, `accepted_gradients_active`, `query_lists`, `accepted_ratios`, `downhill_pairings`, `minimizer_and_origin` |
| `lemma/L:lem:agreement`, `disp/018`, prose `033` | 162-171 | `agreement`, `query_value_scaled`, `positive_scale_part` |
| `disp/020`-`disp/024`, prose `034`-`043` | 189-234 | `boundary_shape_return`, `jacobian_display`, `characteristic_def`, `shape_eigenvalues`, `characteristic_signs_box`, `jacobian_block_form`, `block_reasons`, `return_eigenvalues`, `hyperbolic_spectrum`, `scale_eigenvector`, `orbit_physical_states` |
| `lemma/L:lem:scalar`, `disp/029`, prose `048`, `053`-`057` | 267-322 | `scalar_lemma`, `monotone_ramp`, `ramp_integral_bounds`, `branch_hessian_bounds`, `objective_strongly_convex`, `directional_derivative` |
| `disp/038`, `disp/044`, prose `061`, `066` | 345-380 | `branch_copy_formula`, `fourth_branch_negative`, `center_active_nonstationary`, `whitened_constants` |
| `disp/045`, prose `071`-`077` | 396-403 | `step_scalar_def`, `step_scalar_props`, `step_copies`, `step_objective_structure`, `step_zero_argument_inactive`, `step_local_polyhedral`, `step_hessian_identity`, `whitened_step_hessian` |
| prose `083` | 413 | `branch_regularity` |

The other items (definitions, displays and prose identical to article items, proofs, remarks)
are `DEFINITION`, `SAME_AS`, `PART_OF`, `PROOF` or `NON_CLAIM` in the register. Two `example`s at
the end show that the standing assumptions can hold at once and that the clauses "at every
twice-differentiable point" are not vacuous.
-/

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix BfgsVerification SeedOrbit SeedCycle

namespace BfgsCoverage.Companion.Ch13L

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Helpers -/

/-- The attempted lengths of phase `j` are the trial lengths of the rows of that phase. -/
theorem mem_trialHistory_iff (j : Fin 3) (a : ℝ) :
    a ∈ trialHistory j ↔ ∃ q : Fin 9, trialPhase q = j ∧ trialLength q = a := by
  constructor
  · exact trial_history_witness j
  · rintro ⟨q, rfl, rfl⟩
    fin_cases q <;> simp [trialHistory, trialPhase, trialLength]

/-- The accepted lengths of the phases of the seed cycle: `1, 1/4, 1/16`. -/
theorem length_phase (m : ℕ) :
    SeedOrbit.length (phase (3 * m)) = 1 ∧ SeedOrbit.length (phase (3 * m + 1)) = 1/4 ∧
      SeedOrbit.length (phase (3 * m + 2)) = 1/16 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [phase, SeedOrbit.length, Nat.mul_mod_right]
  · have : (3 * m + 1) % 3 = 1 := by omega
    simp [phase, SeedOrbit.length, this]
  · have : (3 * m + 2) % 3 = 2 := by omega
    simp [phase, SeedOrbit.length, this]

/-! ### Statements and retained implementation (lines 27-61) -/

/-- Item `C/13_L/disp/001` (`companion/chapters/13_L.tex:30-32`): "Fix
\[ 0<c_1\le\tfrac13,\qquad c_1<c_2<1. \]"
The library's `LUniform.Admissible c₁ c₂` is this range. -/
theorem admissible_iff (c₁ c₂ : ℝ) :
    LUniform.Admissible c₁ c₂ ↔ 0 < c₁ ∧ c₁ ≤ 1/3 ∧ c₁ < c₂ ∧ c₂ < 1 :=
  ⟨fun h => ⟨h.pos, h.le_third, h.lt, h.lt_one⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

/-- $Q_\mu$ written with the three slopes is the library's `LQuadraticSeed.objective μ`. -/
theorem quadratic_objective_eq (μ : ℝ) (Q : Vec 2 → ℝ)
    (hQ : ∀ x, Q x = μ / 2 * sqNorm x + max (max (dot (SeedOrbit.gradient seedC seedD 0) x)
      (dot (SeedOrbit.gradient seedC seedD 1) x)) (dot (SeedOrbit.gradient seedC seedD 2) x)) :
    Q = LQuadraticSeed.objective μ := by
  funext x
  rw [hQ, (BfgsCoverage.Article.LowerCurvature.quadratic_def μ x).1,
    (BfgsCoverage.Article.LowerCurvature.quadratic_def μ x).2]
  rfl

/-- Item `C/13_L/theorem/L:thm:global`, Theorem `L:thm:global` (`companion/chapters/13_L.tex:42-48`),
"Global failure with constant positive branch Hessians", including its display `C/13_L/disp/003`
(lines 44-46).

"There are three fixed slopes $g_0,g_1,g_2\in\R^2$ such that, for every $\mu>0$,
\[ Q_\mu(x)=\tfrac\mu2\norm{x}^2+\max_{i=0,1,2}g_i\T x \]
is $\mu$-strongly convex, coercive, and has a unique nonsmooth minimizer $x_*\ne0$, yet admits
initial states $(x_0,H_0)$ that produce, for every such pair $(c_1,c_2)$, the same deterministic
full-BFGS iterates converging to the nonstationary origin. Initial states and every future trial
may be chosen arbitrarily close to the origin in the sense made precise in
Section~\ref{L:sec:blowup}. Every branch has Hessian exactly $\mu I$ globally. The accepted
lengths repeat $1,1/4,1/16$."

Reading. "Such pair" is $0<c_1\le1/3$, $c_1<c_2<1$ (display `C/13_L/disp/001`); the
implementation is `NonStrictLineSearch.fromMetric` for every trial budget `N ≥ 5`, runs are
`AdmissibleBFGSRun` (actual gradients, the unmodified update); the initial state and the
iterates `x`, `H` are chosen before the pair. "Strongly convex" is Euclidean
(`FixedNormal.EuclideanStrongConvexOn`). The branches are $\mu\|x\|^2/2+g_i^Tx$; "Hessian
exactly $\mu I$ globally": each branch is $C^2$ with Hessian matrix $\mu I$ at every point.
"Arbitrarily close in the sense of Section `L:sec:blowup`": for every neighbourhood `W` of the
limiting seed state $P_*$ in the normalized coordinates $x=\tau z$, $H=\tau M(b,e)$ (display
`C/13_L/disp/014`; `LNormalizedReturn.point`, `shape`, `scale`) and every neighbourhood `V` of
the origin, the initial state is $(x_0,H_0)=(\tau z,\tau M(b,e))$ with $(z,b,e,\tau)\in W$,
$\tau>0$, and every iterate and every trial point lies in `V` (with `W`, `V` the whole spaces
this is the plain existence claim). The trial points of step `k` are
$x_k+a\,p_k$, $p_k=-H_k\nabla Q_\mu(x_k)$, for the attempted lengths $a$, which are
`trialHistory (phase k)` for every pair; they are differentiable points of $Q_\mu$ (the chapter's
standing convention of differentiable oracle queries, line 29).

Also Item `C/13_L/prose/006` (`companion/chapters/13_L.tex:33`): "The orbits, objectives and
initial points below are chosen before this pair." Here the initial state and the iterates `x`,
matrices `H` are chosen before the pair (likewise in `local_failure` and `agreement`).

Also Item `C/13_L/prose/082` (`companion/chapters/13_L.tex:413`), a discrepancy ("This chapter uses
the fixed line-search pair displayed in this chapter; D's wider parameter family is not
imported."): this theorem and `local_failure` hold for every pair $0<c_1\le1/3$, $c_1<c_2<1$,
the parameter family of Chapter D. -/
theorem global_failure :
    ∃ g : Fin 3 → Vec 2, ∀ μ : ℝ, 0 < μ → ∀ Q : Vec 2 → ℝ,
      (∀ x, Q x = μ / 2 * sqNorm x + max (max (dot (g 0) x) (dot (g 1) x)) (dot (g 2) x)) →
      -- `μ`-strongly convex and coercive
      FixedNormal.EuclideanStrongConvexOn univ μ Q ∧ Tendsto Q (cocompact (Vec 2)) atTop ∧
      -- a unique nonsmooth minimizer `x_* ≠ 0`
      (∃ xs : Vec 2, xs ≠ 0 ∧ (∀ x, Q xs ≤ Q x) ∧ (∀ x, Q x = Q xs → x = xs) ∧
        ¬ DifferentiableAt ℝ Q xs) ∧
      -- the origin is nonstationary
      (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential Q 0 ∧
      -- every branch has Hessian exactly `μ I` globally
      (∀ i : Fin 3, ContDiff ℝ 2 (fun x => μ / 2 * sqNorm x + dot (g i) x) ∧
        ∀ x, RadialHessian.matrix (fun y => μ / 2 * sqNorm y + dot (g i) y) x = μ • (1 : Mat 2)) ∧
      -- initial states, arbitrarily close to the origin, and their runs
      ∀ W ∈ 𝓝 LNormalizedReturn.seed, ∀ V ∈ 𝓝 (0 : Vec 2),
        ∃ (w₀ : LNormalizedReturn.State) (x : ℕ → Vec 2) (H : ℕ → Mat 2),
          w₀ ∈ W ∧ 0 < LNormalizedReturn.scale w₀ ∧
          x 0 = LNormalizedReturn.scale w₀ • LNormalizedReturn.point w₀ ∧
          H 0 = LNormalizedReturn.scale w₀ • LNormalizedReturn.shape w₀ ∧ (H 0).PosDef ∧
          -- converging to the (nonstationary) origin
          Tendsto x atTop (𝓝 0) ∧ (∀ k, x k ∈ V) ∧
          -- every trial is differentiable and lies in `V`
          (∀ k, ∀ a ∈ trialHistory (phase k),
            DifferentiableAt ℝ Q (x k + a • bfgsStep (H k) (coordinateGradient Q (x k)) 1) ∧
            x k + a • bfgsStep (H k) (coordinateGradient Q (x k)) 1 ∈ V) ∧
          -- the same deterministic full-BFGS iterates for every pair
          ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
            ∃ R : AdmissibleBFGSRun 2 Q, R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ R.x = x ∧ R.H = H ∧
              (∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric Q (R.x k) (R.H k) c₁ c₂ N =
                (some (R.α k), trialHistory (phase k))) ∧
              -- the accepted lengths repeat `1, 1/4, 1/16`
              ∀ m, R.α (3 * m) = 1 ∧ R.α (3 * m + 1) = 1/4 ∧ R.α (3 * m + 2) = 1/16 := by
  refine ⟨SeedOrbit.gradient seedC seedD, fun μ hμ Q hQ => ?_⟩
  obtain rfl := quadratic_objective_eq μ Q hQ
  refine ⟨LQuadraticSeed.objective_strongConvex μ, LQuadraticSeed.objective_coercive hμ,
    ⟨LQuadraticSeed.minimizer μ, LQuadraticSeed.minimizer_ne_zero hμ,
      LQuadraticSeed.objective_minimum hμ, fun x hx => LQuadraticSeed.objective_unique_minimum hμ hx,
      LQuadraticSeed.minimizer_not_differentiable hμ⟩,
    LQuadraticSeed.origin_nonstationary hμ.le, fun i => ?_, fun W hW V hV => ?_⟩
  · have hb : (fun x => μ / 2 * sqNorm x + dot (SeedOrbit.gradient seedC seedD i) x) =
        LQuadraticSeed.branch μ i := rfl
    rw [hb]
    exact ⟨LQuadraticSeed.branch_contDiff μ i, LQuadraticSeed.branch_hessian μ i⟩
  · obtain ⟨V', hV'o, hV's, hV'⟩ := LFlatten.physical_neighborhood μ V hV
    obtain ⟨w, hw, ht, hp, hc, hn⟩ := LNormalizedOracle.uniform_oracle_orbit μ (V' ∩ W)
      (inter_mem (hV'o.mem_nhds hV's) hW)
    let O : LUniform.Orbit μ := ⟨w, hp, hc, hn⟩
    have h₀ : LUniform.Admissible (1/10000) (1/2) := LUniform.sourcePair
    obtain ⟨hx, hq⟩ := (O.data h₀).whole_run_in_neighborhood (fun m => (hw m).1) hV'
    obtain ⟨hxlim, -, -, -, -, -, hdiff, -, -⟩ :=
      (O.data h₀).failure_contract hμ.le (by norm_num) (by norm_num) (by norm_num) ht
    refine ⟨w 0, O.x, O.H, (hw 0).2, hp 0, rfl, rfl, O.initial_posDef, hxlim, hx, ?_, ?_⟩
    · intro k a ha
      obtain ⟨q, hqk, rfl⟩ := (mem_trialHistory_iff (phase k) a).mp ha
      exact ⟨hdiff k q hqk, hq k q hqk⟩
    · intro c₁ c₂ hc₁ hc₁' hc hc₂
      have h : LUniform.Admissible c₁ c₂ := ⟨hc₁, hc₁', hc, hc₂⟩
      refine ⟨O.run hμ.le h, rfl, rfl, rfl, rfl, fun k N hN => ?_, fun m => ?_⟩
      · exact BfgsCoverage.Article.LowerCurvature.fromMetric_fuel_mono
          ((O.data h).nonstrict_actual_search k) N hN
      · rw [LUniform.Orbit.run_alpha, LUniform.Orbit.run_alpha, LUniform.Orbit.run_alpha]
        exact length_phase m

/-! ### The step objective after the one fixed whitening

The alternative of Theorem `L:thm:local` (Section 13.7): the step embedding
`LStepEmbedding.objective` composed with the same fixed square root $A=\bar H_0^{1/2}$
(`LUniform.coordinateMatrix`) as the four-branch objective `LUniform.smoothObjective`. The
library proves these facts for the square root of its own initial matrix (`LWhitening`, chosen
for one pair); they are repeated here for `LUniform.coordinateMatrix`, whose orbit serves every
admissible pair. -/

/-- $\widetilde F(z)=F(Az)$ for the step embedding $F$. -/
def stepObjective : Vec 2 → ℝ :=
  AffineWhitening.objective LUniform.coordinateMatrix LStepEmbedding.objective

/-- The one fixed matrix $\mu\bar H_0$. -/
def stepHessian : Mat 2 := LEmbedding.mu • LUniform.initialMetric

theorem stepHessian_posDef : stepHessian.PosDef :=
  LNormalizedOracle.positive_smul_posDef LUniform.initialMetric_posDef LEmbedding.mu_pos

theorem stepHessian_isSymm : stepHessian.IsSymm := by
  have h := stepHessian_posDef.1
  unfold Matrix.IsHermitian at h
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

theorem step_strongConvex :
    FixedNormal.EuclideanStrongConvexOn univ LUniform.lowerConstant stepObjective :=
  AffineWhitening.strongConvex_whitening _ LUniform.initialMetric_posDef LEmbedding.mu_pos.le
    LStepEmbedding.objective_strongConvex

theorem step_apply (z : Vec 2) :
    stepObjective z = LStepEmbedding.objective (LUniform.coordinateMatrix *ᵥ z) := rfl

theorem step_zero : stepObjective 0 = 0 := by
  rw [step_apply, Matrix.mulVec_zero, LStepEmbedding.objective_zero]

theorem step_nonnegative (z : Vec 2) : 0 ≤ stepObjective z :=
  LStepEmbedding.objective_nonnegative _

theorem step_unique_zero {z : Vec 2} (hz : stepObjective z = 0) : z = 0 :=
  AffineWhitening.zero_unique_whitening LUniform.coordinateMatrix LUniform.coordinateMatrix_invertible
    (fun _ => LStepEmbedding.objective_unique_zero) hz

theorem step_compact_sublevel (a : ℝ) : IsCompact {z | stepObjective z ≤ a} :=
  AffineWhitening.sublevels_compact_whitening LUniform.coordinateMatrix
    LUniform.coordinateMatrix_invertible LStepEmbedding.objective_sublevels_compact a

theorem step_nonsmooth_origin : ¬ DifferentiableAt ℝ stepObjective (0 : Vec 2) := by
  have he := AffineWhitening.differentiableAt_equiv LUniform.coordinateMatrix
    LUniform.coordinateMatrix_invertible LStepEmbedding.objective 0
  simpa only [AffineWhitening.point, Matrix.mulVec_zero, stepObjective] using
    mt he.mp LStepEmbedding.objective_not_differentiable_zero

/-- At every differentiable point of $\widetilde F$ its derivative is differentiable and its
Hessian is $\mu\bar H_0$ (the proof of `LWhitening.step_actual_hessian`, for
`LUniform.coordinateMatrix`). -/
theorem step_actual_hessian {z : Vec 2} (hd : DifferentiableAt ℝ stepObjective z) :
    DifferentiableAt ℝ (fderiv ℝ stepObjective) z ∧ RadialHessian.matrix stepObjective z = stepHessian := by
  have hF : DifferentiableAt ℝ LStepEmbedding.objective (LUniform.coordinateMatrix.mulVec z) :=
    (AffineWhitening.linearEquiv LUniform.coordinateMatrix
      LUniform.coordinateMatrix_invertible).comp_right_differentiableAt_iff.mp hd
  obtain ⟨hsecond, hM⟩ := LStepEmbedding.objective_actual_hessian hF
  refine ⟨(AffineWhitening.second_hasFDerivAt LUniform.coordinateMatrix
    LUniform.coordinateMatrix_invertible _ z _ hsecond).differentiableAt, ?_⟩
  rw [stepObjective, AffineWhitening.hessian_formula _ LUniform.coordinateMatrix_invertible _ z
    hsecond.differentiableAt, hM, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    LUniform.coordinateMatrix_transpose, LUniform.coordinateMatrix_square]
  rfl

/-- $\underline\mu\|v\|^2\le v^T\mu\bar H_0v\le\overline L\|v\|^2$. -/
theorem stepHessian_bounds (v : Vec 2) :
    LUniform.lowerConstant * sqNorm v ≤ dot v (stepHessian.mulVec v) ∧
      dot v (stepHessian.mulVec v) ≤ LUniform.upperConstant * sqNorm v := by
  have hb := AffineWhitening.actual_extreme_metric_bounds LUniform.initialMetric
    LUniform.initialMetric_posDef.1 v
  have hM := AffineWhitening.maxEigenvalue_pos LUniform.initialMetric LUniform.initialMetric_posDef
  have hn := sqNorm_nonneg v
  change LUniform.lowerConstant * sqNorm v ≤ metricEnergy (LEmbedding.mu • LUniform.initialMetric) v ∧
    metricEnergy (LEmbedding.mu • LUniform.initialMetric) v ≤ LUniform.upperConstant * sqNorm v
  rw [EnergyIdentities.energy_smul_matrix]
  dsimp [LUniform.lowerConstant, LUniform.upperConstant, LEmbedding.mu]
  constructor <;> nlinarith [mul_nonneg hM.le hn]

/-- $\widetilde F(z)=z^T(\mu\bar H_0)z/2+p(Az)$, with $p$ the residual of the step embedding. -/
theorem step_decomposition (z : Vec 2) :
    stepObjective z = metricEnergy stepHessian z / 2 +
      LStepEmbedding.residual (LUniform.coordinateMatrix *ᵥ z) := by
  change LEmbedding.mu / 2 * sqNorm (LUniform.coordinateMatrix.mulVec z) +
    LStepEmbedding.residual (LUniform.coordinateMatrix *ᵥ z) = _
  rw [stepHessian, EnergyIdentities.energy_smul_matrix]
  change LEmbedding.mu / 2 * sqNorm ((AffineWhitening.squareRoot LUniform.initialMetric
    LUniform.initialMetric_posDef).mulVec z) + _ = _
  rw [AffineWhitening.squareRoot_sqNorm]
  ring

/-! ### Runs uniform in the line-search pair -/

/-- The run clauses of Theorem `L:thm:local` from the article package's
`LUniform.UniformFailureTarget` (one family of iterates and matrices, chosen before the pair,
with `H₀ = I`, converging to the centers `LUniform.failureCenter`). -/
theorem runs_of_uniform {F : Vec 2 → ℝ} (hT : LUniform.UniformFailureTarget F 1 LUniform.failureCenter) :
    ∃ (x : ℕ → ℕ → Vec 2) (H : ℕ → ℕ → Mat 2) (p : ℕ → Vec 2),
      Tendsto (fun n => x n 0) atTop (𝓝 0) ∧ (∀ n, H n 0 = 1) ∧
      (∀ n, Tendsto (x n) atTop (𝓝 (p n))) ∧
      (∀ n, (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential F (p n)) ∧ Tendsto p atTop (𝓝 0) ∧
      (∀ n k, ∀ a ∈ trialHistory (phase k),
        DifferentiableAt ℝ F (x n k + a • bfgsStep (H n k) (coordinateGradient F (x n k)) 1)) ∧
      (∀ U ∈ 𝓝 (0 : Vec 2), ∃ N : ℕ, ∀ n ≥ N, ∀ k, ∀ a ∈ trialHistory (phase k),
        x n k + a • bfgsStep (H n k) (coordinateGradient F (x n k)) 1 ∈ U) ∧
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
        ∃ R : ℕ → AdmissibleBFGSRun 2 F, ∀ n,
          (R n).c₁ = c₁ ∧ (R n).c₂ = c₂ ∧ (R n).x = x n ∧ (R n).H = H n ∧
          ∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric F ((R n).x k) ((R n).H k) c₁ c₂ N =
            (some ((R n).α k), trialHistory (phase k)) := by
  obtain ⟨x, H, g, hH0, hx0, hruns⟩ := hT
  obtain ⟨R₀, hR₀, hloc₀⟩ := hruns (1/10000) (1/2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hgrad (n k : ℕ) : coordinateGradient F (x n k) = g n k := by
    obtain ⟨hx, -, hg, -⟩ := hR₀ n
    rw [← hx, ← hg]
    exact DeterministicLineSearch.actual_coordinateGradient ((R₀ n).hasGradient k)
  refine ⟨x, H, LUniform.failureCenter, hx0, hH0, ?_, ?_, LUniform.failure_centers_tendsto, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨hx, -, -, hrun⟩ := hR₀ n
    rw [← hx]
    exact hrun.2.2.1
  · intro n
    obtain ⟨-, -, -, hrun⟩ := hR₀ n
    exact hrun.2.2.2.2.2.2.1
  · intro n k a ha
    obtain ⟨q, hq, rfl⟩ := (mem_trialHistory_iff (phase k) a).mp ha
    obtain ⟨hx, hH, hg, hrun⟩ := hR₀ n
    have h := (hrun.2.2.2.2.2.2.2.2.1 k q hq).1
    rw [hx, hH, hg] at h
    rw [hgrad n k]
    exact h
  · intro U hU
    obtain ⟨N, hN⟩ := hloc₀ U hU
    refine ⟨N, fun n hn k a ha => ?_⟩
    obtain ⟨q, hq, rfl⟩ := (mem_trialHistory_iff (phase k) a).mp ha
    obtain ⟨hx, hH, hg, -⟩ := hR₀ n
    have h := (hN n hn k).2 q hq
    rw [hx, hH, hg] at h
    rw [hgrad n k]
    exact h
  · intro c₁ c₂ hc₁ hc₁' hc hc₂
    obtain ⟨R, hR, -⟩ := hruns c₁ c₂ hc₁ hc₁' hc hc₂
    refine ⟨R, fun n => ?_⟩
    obtain ⟨hx, hH, -, hrun⟩ := hR n
    obtain ⟨h1, h2, -, -, -, -, -, hstep, -, -⟩ := hrun
    exact ⟨h1, h2, hx, hH, fun k N hN =>
      BfgsCoverage.Article.LowerCurvature.fromMetric_fuel_mono (hstep k).2.2.2.1 N hN⟩

/-- Item `C/13_L/theorem/L:thm:local`, Theorem `L:thm:local` (`companion/chapters/13_L.tex:51-60`),
"Local failure under the pointwise Hessian bounds" (a discrepancy for its last clause, see
below), with its display Item `C/13_L/disp/004` (`companion/chapters/13_L.tex:53-56`).

"There is a finite strongly convex objective $F:\R^2\to\R$ with compact sublevels and a unique
nonsmooth minimizer at zero, and constants $0<\underline\mu\le\overline L<\infty$, such that
\[ \underline\mu I\preceq \nabla^2F(x)\preceq\overline L I
   \quad\text{at every twice-differentiable point}, \]
yet the fixed deterministic full-BFGS implementation with $H_0=I$ has bad initial points
$x_0^{(n)}\to0$ whose runs, the same for every such pair $(c_1,c_2)$, converge to nonstationary
points $p_n\to0$. All trial points of the $n$th run remain uniformly near zero as $n\to\infty$.

The function can be chosen as a maximum of four globally $C^{1,1}$, uniformly strongly convex,
globally gradient-Lipschitz branches. Alternatively, it can be chosen so that its Hessian is one
fixed positive-definite matrix wherever it is twice differentiable; the latter version has a
countable polyhedral nonsmooth part, not a finite smooth-branch representation."

Reading. Two objectives `F₁` (the four-branch version, `LUniform.smoothObjective`) and `F₂` (the
alternative, `stepObjective`) both have every property of the first paragraph. Twice
differentiable at `x`: `F` differentiable near `x` and its derivative differentiable at `x`; the
Hessian is `RadialHessian.matrix F x` and the bounds are stated with its quadratic form. The
implementation is `NonStrictLineSearch.fromMetric` for every budget `N ≥ 5`, runs are
`AdmissibleBFGSRun`; the iterates `x n`, the matrices `H n` (with `H n 0 = I`) and the limits
`p n` are chosen before the pair. The trial points of step `k` of run `n` are
$x_k^{(n)}+a\,p_k^{(n)}$, $p_k^{(n)}=-H_k^{(n)}\nabla F(x_k^{(n)})$, for the attempted lengths
`a ∈ trialHistory (phase k)` (the trial lists of every pair); they are differentiable (the
chapter's convention of differentiable oracle queries, line 29) and, uniformly in `k`, lie in any
given neighbourhood of zero once `n` is large. $C^{1,1}$ and gradient-Lipschitz: $C^1$ with a
Euclidean Lipschitz gradient (one constant for the four branches); uniformly strongly convex: one
modulus for the four branches. The alternative: $\nabla^2F_2=B$ for one positive-definite `B`
at every twice-differentiable point, and $F_2(x)-x^TBx/2$ (its nonsmooth part) is the pointwise
maximum, attained, of a countable family of affine functions. The final clause "not a finite
smooth-branch representation" is recorded as a discrepancy in the register: read literally ("the
latter version has no finite smooth-branch representation") it is false, since the step version is
also a maximum of ten convex, globally $C^{1,1}$, uniformly strongly convex branches (sketch in the
register, not formalized). The statement below is the descriptive reading (the nonsmooth part of
the latter version is a countable polyhedral function, in contrast with the four smooth branches of
the first version; Section 13.7: "No claim of four smooth branches is made for this
alternative").

Also the following items, stated by conjuncts of this theorem:
* Item `C/13_L/prose/010` (`companion/chapters/13_L.tex:61`): "The local theorem satisfies the
  user's literal classical-Hessian assumption, and even actual strong convexity." (the
  strong-convexity and Hessian-bound conjuncts, for both objectives);
* Item `C/13_L/prose/046` (`companion/chapters/13_L.tex:254`): "We now construct a single objective
  satisfying the literal Hessian bounds and having no guaranteed local basin." (`F₁`);
* Item `C/13_L/prose/070` (`companion/chapters/13_L.tex:381`): "These constants are fixed for the
  one transformed objective, not changed between starts. [...] This proves the four-$C^{1,1}$-branch
  part of Theorem~\ref{L:thm:local}." (`F₁`, with the constants of `whitened_constants`);
* Item `C/13_L/prose/078` (`companion/chapters/13_L.tex:403`): "This establishes the remaining
  version of Theorem~\ref{L:thm:local}." (`F₂`). -/
theorem local_failure :
    ∃ F₁ F₂ : Vec 2 → ℝ,
      (∀ F ∈ ({F₁, F₂} : Set (Vec 2 → ℝ)),
        -- a finite strongly convex objective with compact sublevels
        (∃ κ : ℝ, 0 < κ ∧ FixedNormal.EuclideanStrongConvexOn univ κ F) ∧
        (∀ a : ℝ, IsCompact {x | F x ≤ a}) ∧
        -- and a unique nonsmooth minimizer at zero
        (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) ∧ ¬ DifferentiableAt ℝ F (0 : Vec 2) ∧
        -- constants `0 < μ̲ ≤ L̄ < ∞` with the Hessian bounds at every twice-differentiable point
        (∃ μl Lu : ℝ, 0 < μl ∧ μl ≤ Lu ∧ ∀ x : Vec 2,
          (∀ᶠ z in 𝓝 x, DifferentiableAt ℝ F z) → DifferentiableAt ℝ (fderiv ℝ F) x →
          (RadialHessian.matrix F x).IsSymm ∧ ∀ v,
            μl * sqNorm v ≤ dot v ((RadialHessian.matrix F x).mulVec v) ∧
            dot v ((RadialHessian.matrix F x).mulVec v) ≤ Lu * sqNorm v) ∧
        -- bad initial points `x₀⁽ⁿ⁾ → 0` with `H₀ = I`, converging to nonstationary `p_n → 0`
        ∃ (x : ℕ → ℕ → Vec 2) (H : ℕ → ℕ → Mat 2) (p : ℕ → Vec 2),
          Tendsto (fun n => x n 0) atTop (𝓝 0) ∧ (∀ n, H n 0 = 1) ∧
          (∀ n, Tendsto (x n) atTop (𝓝 (p n))) ∧
          (∀ n, (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential F (p n)) ∧
          Tendsto p atTop (𝓝 0) ∧
          (∀ n k, ∀ a ∈ trialHistory (phase k),
            DifferentiableAt ℝ F (x n k + a • bfgsStep (H n k) (coordinateGradient F (x n k)) 1)) ∧
          -- all trial points of the `n`th run remain uniformly near zero
          (∀ U ∈ 𝓝 (0 : Vec 2), ∃ N : ℕ, ∀ n ≥ N, ∀ k, ∀ a ∈ trialHistory (phase k),
            x n k + a • bfgsStep (H n k) (coordinateGradient F (x n k)) 1 ∈ U) ∧
          -- the runs of the implementation, the same for every pair
          ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1/3 → c₁ < c₂ → c₂ < 1 →
            ∃ R : ℕ → AdmissibleBFGSRun 2 F, ∀ n,
              (R n).c₁ = c₁ ∧ (R n).c₂ = c₂ ∧ (R n).x = x n ∧ (R n).H = H n ∧
              ∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric F ((R n).x k) ((R n).H k) c₁ c₂ N =
                (some ((R n).α k), trialHistory (phase k))) ∧
      -- `F₁` is a maximum of four globally `C^{1,1}`, uniformly strongly convex, globally
      -- gradient-Lipschitz branches
      (∃ f : Fin 4 → Vec 2 → ℝ,
        (∀ x, F₁ x = Finset.univ.sup' Finset.univ_nonempty (fun i => f i x)) ∧
        (∀ i, ContDiff ℝ 1 (f i)) ∧
        (∃ κ : ℝ, 0 < κ ∧ ∀ i, FixedNormal.EuclideanStrongConvexOn univ κ (f i)) ∧
        ∃ L : ℝ, ∀ i y z, ‖euclideanVector (coordinateGradient (f i) y - coordinateGradient (f i) z)‖ ≤
          L * ‖euclideanVector (y - z)‖) ∧
      -- `F₂` has one fixed positive-definite Hessian and a countable polyhedral nonsmooth part
      ∃ B : Mat 2, B.PosDef ∧
        (∀ x : Vec 2, (∀ᶠ z in 𝓝 x, DifferentiableAt ℝ F₂ z) → DifferentiableAt ℝ (fderiv ℝ F₂) x →
          RadialHessian.matrix F₂ x = B) ∧
        ∃ (ι : Type) (_ : Countable ι) (ℓ : ι → Vec 2 →L[ℝ] ℝ) (c : ι → ℝ), ∀ x,
          IsGreatest (Set.range fun j => ℓ j x + c j) (F₂ x - metricEnergy B x / 2) := by
  obtain ⟨hκ, horder, hgeom, hbranch, hmax, hhess, -, htarget, -⟩ := LUniform.uniformSmoothLocalFailure
  obtain ⟨-, hstrong, hF0, hlower, hzero, hcompact, -, hnonsmooth⟩ := hgeom
  refine ⟨LUniform.smoothObjective, stepObjective, ?_, ?_, stepHessian, stepHessian_posDef,
    fun x hf _ => (step_actual_hessian hf.self_of_nhds).2, ?_⟩
  · rintro F (rfl | rfl)
    · refine ⟨⟨LUniform.lowerConstant, hκ, hstrong⟩, hcompact, fun y => ?_, fun y hy => ?_,
        hnonsmooth, ⟨LUniform.lowerConstant, LUniform.upperConstant, hκ, horder, hhess⟩,
        runs_of_uniform htarget⟩
      · rw [hF0]
        exact (mul_nonneg (div_nonneg hκ.le (by norm_num)) (sqNorm_nonneg y)).trans (hlower y)
      · rw [hF0] at hy
        exact hzero y hy
    · refine ⟨⟨LUniform.lowerConstant, hκ, step_strongConvex⟩, step_compact_sublevel,
        fun y => by rw [step_zero]; exact step_nonnegative y,
        fun y hy => step_unique_zero (hy.trans step_zero), step_nonsmooth_origin,
        ⟨LUniform.lowerConstant, LUniform.upperConstant, hκ, horder, fun x hf _ => ?_⟩,
        runs_of_uniform (LUniform.uniform_identity_failure LActualCopies.stepData
          LStepEmbedding.objective_zero)⟩
      rw [(step_actual_hessian hf.self_of_nhds).2]
      exact ⟨stepHessian_isSymm, stepHessian_bounds⟩
  · refine ⟨LUniform.smoothBranch, hmax, fun i => (hbranch i).1,
      ⟨LUniform.lowerConstant, hκ, fun i => (hbranch i).2.1⟩, LUniform.upperConstant, fun i y z => ?_⟩
    rw [DeterministicLineSearch.actual_coordinateGradient ((hbranch i).2.2.1 y),
      DeterministicLineSearch.actual_coordinateGradient ((hbranch i).2.2.1 z)]
    exact BfgsCoverage.Article.LowerCurvature.euclid_le_of_sqNorm_le LUniform.upperConstant_pos.le
      ((hbranch i).2.2.2 y z)
  · refine ⟨LStepEmbedding.CountableIndex, LStepEmbedding.countable_index,
      fun j => (LStepEmbedding.countableLinear j).comp (AffineProjection.matrixCLM LUniform.coordinateMatrix),
      LStepEmbedding.countableOffset, fun x => ?_⟩
    rw [step_decomposition x, add_sub_cancel_left]
    exact LStepEmbedding.residual_countable_max (LUniform.coordinateMatrix *ᵥ x)

/-- Item `C/13_L/prose/007` (`companion/chapters/13_L.tex:40`): "The seed inequalities have
strict margins, so there are no equality-convention issues."

The margins of the seed (display `art:seed_margins` of the article, `Failure.seed_margins`; $z_j$,
$s_j$, $g_j$ with $g_3=g_0$ are `Failure.seedPoint`, `Failure.seedStep`, `Failure.seedSlope`,
$p_j=-M_jg_j$ is `Failure.seedDir`) are strict, and every rejected trial strictly raises the
value. Consequently, for every pair `LUniform.Admissible c₁ c₂` ($0<c_1\le1/3$, $c_1<c_2<1$,
`admissible_iff`), the specified search with the non-strict tests (`NonStrictLineSearch`:
$\le$, $\ge$) and the search with the strict tests (`DeterministicLineSearch`: $<$, $>$) return
the same accepted length and the same trial list at every iterate of every run of the chapter:
the runs on $Q_\mu$ along any normalized return orbit (`LUniform.Orbit`, the runs of Theorem
`L:thm:global`), the scaled copies (`LUniform.family`) on the smooth and the step embedding, and
their whitened versions (`LUniform.failureFamily`, the runs of Theorem `L:thm:local`). -/
theorem strict_margins_same_decisions :
    (∀ j : Fin 3,
      objective seedC seedD (BfgsCoverage.Article.Failure.seedPoint j.castSucc) +
          1/3 * dot (BfgsCoverage.Article.Failure.seedSlope j.castSucc) (BfgsCoverage.Article.Failure.seedStep j) -
        objective seedC seedD (BfgsCoverage.Article.Failure.seedPoint j.succ) > 0 ∧
      dot (BfgsCoverage.Article.Failure.seedSlope j.succ) (BfgsCoverage.Article.Failure.seedStep j) > 0 ∧
      0 > dot (BfgsCoverage.Article.Failure.seedSlope j.castSucc) (BfgsCoverage.Article.Failure.seedStep j)) ∧
    (∀ q : Fin 9, trialAccept q = false →
      objective seedC seedD (BfgsCoverage.Article.Failure.seedPoint (trialPhase q).castSucc) <
        objective seedC seedD (BfgsCoverage.Article.Failure.seedPoint (trialPhase q).castSucc +
          trialLength q • BfgsCoverage.Article.Failure.seedDir (trialPhase q))) ∧
    ∀ (c₁ c₂ : ℝ) (h : LUniform.Admissible c₁ c₂),
      (∀ μ : ℝ, 0 ≤ μ → ∀ (O : LUniform.Orbit μ) (k : ℕ),
        NonStrictLineSearch.fromMetric (LQuadraticSeed.objective μ) (O.x k) (O.H k) c₁ c₂ 5 =
          DeterministicLineSearch.fromMetric (LQuadraticSeed.objective μ) (O.x k) (O.H k) c₁ c₂ 5) ∧
      (∀ m k, NonStrictLineSearch.fromMetric LEmbedding.objective
          ((LUniform.family LActualCopies.smoothData h m).x k)
          ((LUniform.family LActualCopies.smoothData h m).H k) c₁ c₂ 5 =
        DeterministicLineSearch.fromMetric LEmbedding.objective
          ((LUniform.family LActualCopies.smoothData h m).x k)
          ((LUniform.family LActualCopies.smoothData h m).H k) c₁ c₂ 5) ∧
      (∀ m k, NonStrictLineSearch.fromMetric LStepEmbedding.objective
          ((LUniform.family LActualCopies.stepData h m).x k)
          ((LUniform.family LActualCopies.stepData h m).H k) c₁ c₂ 5 =
        DeterministicLineSearch.fromMetric LStepEmbedding.objective
          ((LUniform.family LActualCopies.stepData h m).x k)
          ((LUniform.family LActualCopies.stepData h m).H k) c₁ c₂ 5) ∧
      (∀ m k, NonStrictLineSearch.fromMetric LUniform.smoothObjective
          ((LUniform.failureFamily LActualCopies.smoothData h m).x k)
          ((LUniform.failureFamily LActualCopies.smoothData h m).H k) c₁ c₂ 5 =
        DeterministicLineSearch.fromMetric LUniform.smoothObjective
          ((LUniform.failureFamily LActualCopies.smoothData h m).x k)
          ((LUniform.failureFamily LActualCopies.smoothData h m).H k) c₁ c₂ 5) ∧
      ∀ m k, NonStrictLineSearch.fromMetric stepObjective
          ((LUniform.failureFamily LActualCopies.stepData h m).x k)
          ((LUniform.failureFamily LActualCopies.stepData h m).H k) c₁ c₂ 5 =
        DeterministicLineSearch.fromMetric stepObjective
          ((LUniform.failureFamily LActualCopies.stepData h m).x k)
          ((LUniform.failureFamily LActualCopies.stepData h m).H k) c₁ c₂ 5 := by
  refine ⟨BfgsCoverage.Article.Failure.seed_margins, BfgsCoverage.Article.Failure.seed_rejections_raise,
    fun c₁ c₂ h => ⟨fun μ _ O k => ?_, fun m k => ?_, fun m k => ?_, fun m k => ?_, fun m k => ?_⟩⟩
  · exact ((O.data h).nonstrict_actual_search k).trans ((O.data h).actual_search k).symm
  · exact (LUniform.copy_nonstrict_actual_search _ h m k).trans (LUniform.copy_actual_search _ h m k).symm
  · exact (LUniform.copy_nonstrict_actual_search _ h m k).trans (LUniform.copy_actual_search _ h m k).symm
  · exact (LUniform.nonstrict_failure_search _ h m k).trans (LUniform.failure_search _ h m k).symm
  · exact (LUniform.nonstrict_failure_search _ h m k).trans (LUniform.failure_search _ h m k).symm

/-- Item `C/13_L/prose/083` (`companion/chapters/13_L.tex:413`): "The first three branches of the
local finite-branch construction fail to be twice differentiable at the accumulation point." The
four branches of the local construction, before (`LEmbedding.branch`) and after
(`LUniform.smoothBranch`) the fixed whitening: all four have globally Lipschitz (Euclidean)
gradients; the first three are not twice differentiable at zero, the point where the bad starts
accumulate; the fourth is twice differentiable everywhere.

It is also the corrected claim of Item `C/13_L/prose/002` (`companion/chapters/13_L.tex:3`), a
discrepancy: "The local finite-branch functions have Lipschitz gradients but lose second
differentiability at the accumulation point" (only three of the four branches lose it). -/
theorem branch_regularity :
    (∀ i : Fin 4, ∃ L : ℝ, ∀ x y, ‖euclideanVector (coordinateGradient (LEmbedding.branch i) x -
        coordinateGradient (LEmbedding.branch i) y)‖ ≤ L * ‖euclideanVector (x - y)‖) ∧
      (∀ i : Fin 4, ∃ L : ℝ, ∀ x y, ‖euclideanVector (coordinateGradient (LUniform.smoothBranch i) x -
        coordinateGradient (LUniform.smoothBranch i) y)‖ ≤ L * ‖euclideanVector (x - y)‖) ∧
      (∀ i : Fin 3, ¬ DifferentiableAt ℝ (fderiv ℝ (LEmbedding.branch i.castSucc)) (0 : Vec 2)) ∧
      (∀ i : Fin 3, ¬ DifferentiableAt ℝ (fderiv ℝ (LUniform.smoothBranch i.castSucc)) (0 : Vec 2)) ∧
      (∀ x : Vec 2, DifferentiableAt ℝ (fderiv ℝ (LEmbedding.branch 3)) x) ∧
      ∀ z : Vec 2, DifferentiableAt ℝ (fderiv ℝ (LUniform.smoothBranch 3)) z := by
  obtain ⟨h1, h2, h3, h4⟩ := BfgsCoverage.Article.LowerCurvature.branch_second_differentiability
  refine ⟨fun i => (BfgsCoverage.Article.LowerCurvature.branches_regular i).2.2,
    fun i => ⟨LUniform.upperConstant,
      (BfgsCoverage.Article.LowerCurvature.whitening_constants).2.2.2.2.1 i⟩, h1, h2, h3, h4⟩

/-- `ContDiff ℝ 2` gives a differentiable derivative map. -/
theorem fderiv_differentiable_of_contDiff_two {f : Vec 2 → ℝ} (hf : ContDiff ℝ 2 f) (x : Vec 2) :
    DifferentiableAt ℝ (fderiv ℝ f) x :=
  ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x

/-- Item `C/13_L/prose/011` (`companion/chapters/13_L.tex:61`): "It is \emph{not} a local
counterexample with four globally $C^2$ branches having uniform lower curvature." The four
branches of the first version of Theorem `L:thm:local` (`LUniform.smoothBranch`, the branches of
`local_failure`) are not all $C^2$: the first three are not twice differentiable at zero. -/
theorem not_four_C2_branches :
    (∀ i : Fin 3, ¬ DifferentiableAt ℝ (fderiv ℝ (LUniform.smoothBranch i.castSucc)) (0 : Vec 2)) ∧
      ∀ i : Fin 3, ¬ ContDiff ℝ 2 (LUniform.smoothBranch i.castSucc) := by
  refine ⟨LUniform.branch_not_twice_differentiable_zero, fun i hi => ?_⟩
  exact LUniform.branch_not_twice_differentiable_zero i (fderiv_differentiable_of_contDiff_two hi 0)

/-- Item `C/13_L/prose/012` (`companion/chapters/13_L.tex:61`), OPEN (stated without proof):
"That stronger combination remains unproved here." The stronger combination: a local
counterexample (in the sense of Theorem `L:thm:local`) whose objective is a maximum of four
globally $C^2$ branches having uniform lower curvature. Stated, as the article's open question
`BfgsCoverage.Article.Verification.C2StronglyConvexLocalFailure`, for the specified
implementation (`NonStrictLineSearch.fromMetric`) with one fixed pair $0<c_1<c_2<1$ and
$H_0=I$, here in the plane with four branches: starts tending to the minimizer $x_*$, all
queried points differentiable, and runs none of which converges to $x_*$. -/
def FourC2BranchLocalFailure : Prop :=
  ∃ (f : Fin 4 → Vec 2 → ℝ) (κ : ℝ), 0 < κ ∧
    (∀ i, ContDiff ℝ 2 (f i) ∧ FixedNormal.EuclideanStrongConvexOn univ κ (f i)) ∧
    let F : Vec 2 → ℝ := fun x => Finset.univ.sup' Finset.univ_nonempty (fun i => f i x)
    ∃ (xstar : Vec 2) (c₁ c₂ : ℝ) (R : ℕ → AdmissibleBFGSRun 2 F),
      (∀ x, F xstar ≤ F x) ∧ 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1 ∧
      Tendsto (fun n => (R n).x 0) atTop (𝓝 xstar) ∧
      ∀ n, (R n).H 0 = 1 ∧ (R n).c₁ = c₁ ∧ (R n).c₂ = c₂ ∧
        (∀ k, ∃ fuel : ℕ,
          (NonStrictLineSearch.fromMetric F ((R n).x k) ((R n).H k) c₁ c₂ fuel).1 = some ((R n).α k) ∧
          ∀ a ∈ (NonStrictLineSearch.fromMetric F ((R n).x k) ((R n).H k) c₁ c₂ fuel).2,
            DifferentiableAt ℝ F ((R n).x k + a • bfgsStep ((R n).H k) ((R n).g k) 1)) ∧
        ¬ Tendsto (R n).x atTop (𝓝 xstar)

/-! ### The inherited algebraic seed (lines 75-122)

Notation: $(c,d)$ = (`seedC`, `seedD`); $g_0,g_1,g_2$ = `SeedOrbit.gradient seedC seedD`;
$G$ = `SeedOrbit.objective seedC seedD`; $U,V,R,K,T,Y$ = `AlgebraicSeed.U` … `AlgebraicSeed.Y`
at $(c,d)$; $\rho$ = `seedRatio`; $z_j$, $s_j$, $p_j=-M_jg_j$ and the consecutive gradients
$g_0,g_1,g_2,g_0$ are the article's `Failure.seedPoint`, `Failure.seedStep`, `Failure.seedDir`,
`Failure.seedSlope`; $M_j$ = `SeedOrbit.metric seedC seedD j`; the update is
`Failure.fullUpdate` (display `C/13_L/disp/002`). -/

/-- Item `C/13_L/disp/007` (`companion/chapters/13_L.tex:86-88`), with lines 85 and 89-93: "The
algebraic constants solve
\[ 264192RK-UV(U+129)=0,\qquad 16VTK-RUY=0 \]
in the rational $\ell_\infty$ box of radius $10^{-30}$ about [$(c_0,d_0)$]." -/
theorem root_equations :
    264192 * AlgebraicSeed.R seedC seedD * AlgebraicSeed.K seedC seedD -
        AlgebraicSeed.U seedC seedD * AlgebraicSeed.V seedC seedD * (AlgebraicSeed.U seedC seedD + 129) = 0 ∧
      16 * AlgebraicSeed.V seedC seedD * AlgebraicSeed.T seedC seedD * AlgebraicSeed.K seedC seedD -
        AlgebraicSeed.R seedC seedD * AlgebraicSeed.U seedC seedD * AlgebraicSeed.Y seedC seedD = 0 ∧
      |seedC - 0.31848142762711863064645131250290703717912205023605| ≤ 1 / 10 ^ 30 ∧
      |seedD - (-1.02523211967574872548135087001300414284511909318444)| ≤ 1 / 10 ^ 30 := by
  obtain ⟨hP, hbox, -, hc, hd⟩ := BfgsCoverage.Article.SeedCertificate.root_def
  have hr : AlgebraicSeed.root = ![seedC, seedD] := by
    ext i
    fin_cases i
    · exact hc
    · exact hd
  rw [hr, BfgsCoverage.Article.SeedCertificate.seed_polynomials_def] at hP
  have hc0 : |seedC - AlgebraicSeed.center 0| ≤ 1 / 10 ^ 30 := by
    have h := (norm_le_pi_norm (AlgebraicSeed.root - AlgebraicSeed.center) 0).trans hbox
    rw [hr] at h
    simpa using h
  have hd0 : |seedD - AlgebraicSeed.center 1| ≤ 1 / 10 ^ 30 := by
    have h := (norm_le_pi_norm (AlgebraicSeed.root - AlgebraicSeed.center) 1).trans hbox
    rw [hr] at h
    simpa using h
  rw [BfgsCoverage.Article.SeedCertificate.center_def] at hc0 hd0
  exact ⟨congrFun hP 0, congrFun hP 1, hc0, hd0⟩

/-- Item `C/13_L/disp/009` (`companion/chapters/13_L.tex:95-99`), with line 94 ("Define"):
\[ \rho=\frac{129R}{V(U+129)}\in(0.060,0.061),\qquad
   z_0=\frac1{1-\rho}\begin{pmatrix}897/1024-\rho(1-c)\\ \rho d-1/64\end{pmatrix}. \]
`seedRatio` is $\rho$ and `SeedOrbit.point seedC seedD seedRatio 0` is $z_0$ (the library's
formulas); the assertion is $0.060<\rho<0.061$. -/
theorem seed_ratio_def :
    seedRatio = 129 * AlgebraicSeed.R seedC seedD /
        (AlgebraicSeed.V seedC seedD * (AlgebraicSeed.U seedC seedD + 129)) ∧
      (0.060 : ℝ) < seedRatio ∧ seedRatio < 0.061 ∧
      SeedOrbit.point seedC seedD seedRatio 0 =
        (1 / (1 - seedRatio)) • ![897/1024 - seedRatio * (1 - seedC), seedRatio * seedD - 1/64] := by
  obtain ⟨h1, h2, h3⟩ := BfgsCoverage.Article.Failure.seed_rho
  refine ⟨?_, h2, h3, BfgsCoverage.Article.Failure.seedStart_eq.symm⟩
  rw [h1]
  simp only [AlgebraicSeed.R, AlgebraicSeed.V, AlgebraicSeed.U]

/-- Item `C/13_L/disp/010` (`companion/chapters/13_L.tex:101-104`), with lines 100 and 105: "Let
$M_0=I$ and use consecutive gradients $g_0,g_1,g_2,g_0$ with lengths $1,1/4,1/16$. Exact
full-BFGS algebra gives
\[ M_1=\begin{pmatrix}129/256&-1/16\\-1/16&1\end{pmatrix},\qquad M_3=\rho I,\qquad z_3=\rho z_0. \]
Here $z_{j+1}=z_j-\alpha_jM_jg_j$." The matrices and points are variables with these defining
equations: $M_{j+1}$ is the full update `Failure.fullUpdate` of $M_j$ with gradients
$g_j,g_{j+1}$ (`Failure.seedSlope`, $g_3=g_0$) and length $\alpha_j$ (`SeedOrbit.length`),
and $z_0$ is the point of display `C/13_L/disp/009`. -/
theorem seed_matrix_closure (M : Fin 4 → Mat 2) (z : Fin 4 → Vec 2) (hM0 : M 0 = 1)
    (hM : ∀ j : Fin 3, M j.succ = BfgsCoverage.Article.Failure.fullUpdate (M j.castSucc)
      (BfgsCoverage.Article.Failure.seedSlope j.castSucc)
      (BfgsCoverage.Article.Failure.seedSlope j.succ) (SeedOrbit.length j))
    (hz0 : z 0 = SeedOrbit.point seedC seedD seedRatio 0)
    (hz : ∀ j : Fin 3, z j.succ = z j.castSucc -
      SeedOrbit.length j • (M j.castSucc *ᵥ BfgsCoverage.Article.Failure.seedSlope j.castSucc)) :
    M 1 = !![129/256, -1/16; -1/16, 1] ∧ M 3 = seedRatio • (1 : Mat 2) ∧ z 3 = seedRatio • z 0 := by
  obtain ⟨hc1, hc3, hz3⟩ := BfgsCoverage.Article.Failure.seed_closures
  obtain ⟨-, hm1, hm2, -⟩ := BfgsCoverage.Article.Failure.seed_matrices_steps
  have e1 : M 1 = metric seedC seedD 1 := by
    have h := hM 0
    change M 1 = BfgsCoverage.Article.Failure.fullUpdate (M 0) g0 g1 1 at h
    rw [h, hM0, hc1]
  have e2 : M 2 = metric seedC seedD 2 := by
    have h := hM 1
    change M 2 = BfgsCoverage.Article.Failure.fullUpdate (M 1) g1 (g2 seedC seedD) (1/4) at h
    rw [h, e1, hm2]
  have e3 : M 3 = seedRatio • (1 : Mat 2) := by
    have h := hM 2
    change M 3 = BfgsCoverage.Article.Failure.fullUpdate (M 2) (g2 seedC seedD) g0 (1/16) at h
    rw [h, e2, hc3]
  have hstep (j : Fin 3) (hMj : M j.castSucc = metric seedC seedD j) :
      z j.succ = z j.castSucc + BfgsCoverage.Article.Failure.seedStep j := by
    rw [hz j, hMj, BfgsCoverage.Article.Failure.seedStep_eq, BfgsCoverage.Article.Failure.seedSlope_castSucc,
      bfgsStep, neg_smul, sub_eq_add_neg]
  have p0 : z 0 = BfgsCoverage.Article.Failure.seedPoint 0 := by
    rw [hz0, ← BfgsCoverage.Article.Failure.seedStart_eq]
    rfl
  have p1 : z 1 = BfgsCoverage.Article.Failure.seedPoint 1 := by
    have h := hstep 0 hM0
    change z 1 = z 0 + BfgsCoverage.Article.Failure.seedStep 0 at h
    rw [h, p0]
    rfl
  have p2 : z 2 = BfgsCoverage.Article.Failure.seedPoint 2 := by
    have h := hstep 1 e1
    change z 2 = z 1 + BfgsCoverage.Article.Failure.seedStep 1 at h
    rw [h, p1]
    rfl
  have p3 : z 3 = BfgsCoverage.Article.Failure.seedPoint 3 := by
    have h := hstep 2 e2
    change z 3 = z 2 + BfgsCoverage.Article.Failure.seedStep 2 at h
    rw [h, p2]
    rfl
  refine ⟨by rw [e1, hm1], e3, by rw [p3, p0, hz3]⟩

/-- Item `C/13_L/prose/017` (`companion/chapters/13_L.tex:105`): "Every displayed accepted
gradient is uniquely active for $G(z)=\max_ig_i\T z$." The displayed accepted gradients are the
consecutive gradients $g_0,g_1,g_2,g_0$ at $z_0,z_1,z_2,z_3$ (`Failure.seedSlope j` at
`Failure.seedPoint j`; $g_{\sigma(j)}$ with $\sigma=(0,1,2,0)$). -/
theorem accepted_gradients_active :
    (∀ z : Vec 2, objective seedC seedD z =
      max (max (dot g0 z) (dot g1 z)) (dot (g2 seedC seedD) z)) ∧
    ∀ j : Fin 4, ∀ i : Fin 3, i ≠ (![0, 1, 2, 0] : Fin 4 → Fin 3) j →
      dot (SeedOrbit.gradient seedC seedD i) (BfgsCoverage.Article.Failure.seedPoint j) <
        dot (SeedOrbit.gradient seedC seedD ((![0, 1, 2, 0] : Fin 4 → Fin 3) j))
          (BfgsCoverage.Article.Failure.seedPoint j) := by
  have hact := BfgsCoverage.Article.Failure.seed_cycle.2.2.2.2.1
  refine ⟨BfgsCoverage.Article.Failure.seed_slopes.2.2.2.2.2.2, fun j i hi => ?_⟩
  fin_cases j
  · exact hact 0 i hi
  · exact hact 1 i hi
  · exact hact 2 i hi
  · have h0 := hact 0 i hi
    have hρ := source_ratio_pos_lt_one.1
    change dot (SeedOrbit.gradient seedC seedD i) (BfgsCoverage.Article.Failure.seedPoint 3) <
      dot (SeedOrbit.gradient seedC seedD 0) (BfgsCoverage.Article.Failure.seedPoint 3)
    rw [BfgsCoverage.Article.Failure.seed_closures.2.2, dot_smul_right, dot_smul_right]
    exact mul_lt_mul_of_pos_left h0 hρ

/-- Item `C/13_L/disp/011` (`companion/chapters/13_L.tex:108-110`), with line 107: "The finite
line-search query lists are
\[ [1],\qquad[1,1/2,1/4],\qquad[1,1/2,1/4,1/8,1/16]." \]
For every pair $0<c_1\le1/3$, $c_1<c_2<1$ (display `C/13_L/disp/001`) and every trial budget
`N ≥ 5`, the specified search on $G$ from $(z_j,M_j)$ makes exactly these trials and accepts the
last one. -/
theorem query_lists (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (_hc₂ : c₂ < 1)
    (N : ℕ) (hN : 5 ≤ N) :
    NonStrictLineSearch.fromMetric (objective seedC seedD) (BfgsCoverage.Article.Failure.seedPoint 0)
        (metric seedC seedD 0) c₁ c₂ N = (some 1, [1]) ∧
      NonStrictLineSearch.fromMetric (objective seedC seedD) (BfgsCoverage.Article.Failure.seedPoint 1)
        (metric seedC seedD 1) c₁ c₂ N = (some (1/4), [1, 1/2, 1/4]) ∧
      NonStrictLineSearch.fromMetric (objective seedC seedD) (BfgsCoverage.Article.Failure.seedPoint 2)
        (metric seedC seedD 2) c₁ c₂ N = (some (1/16), [1, 1/2, 1/4, 1/8, 1/16]) := by
  obtain ⟨h0, h1, h2⟩ := BfgsCoverage.Article.Failure.seed_cycle.2.2.2.2.2.1 c₁ c₂ hc₁ hc₁' (hc₁.trans hc)
  exact ⟨BfgsCoverage.Article.LowerCurvature.fromMetric_fuel_mono h0 N hN,
    BfgsCoverage.Article.LowerCurvature.fromMetric_fuel_mono h1 N hN,
    BfgsCoverage.Article.LowerCurvature.fromMetric_fuel_mono h2 N hN⟩

/-- Item `C/13_L/prose/019` (`companion/chapters/13_L.tex:111`): "The accepted decrease ratios
exceed $1/3$, and the accepted new-to-old directional-derivative ratios are negative." At the
acceptance of phase $j$: $(G(z_j)-G(z_{j+1}))/(-g_j^Ts_j)>1/3$ and
$(g_{j+1}^Ts_j)/(g_j^Ts_j)<0$, with $g_3=g_0$. -/
theorem accepted_ratios (j : Fin 3) :
    1/3 < (objective seedC seedD (BfgsCoverage.Article.Failure.seedPoint j.castSucc) -
        objective seedC seedD (BfgsCoverage.Article.Failure.seedPoint j.succ)) /
        (-dot (BfgsCoverage.Article.Failure.seedSlope j.castSucc) (BfgsCoverage.Article.Failure.seedStep j)) ∧
      dot (BfgsCoverage.Article.Failure.seedSlope j.succ) (BfgsCoverage.Article.Failure.seedStep j) /
        dot (BfgsCoverage.Article.Failure.seedSlope j.castSucc) (BfgsCoverage.Article.Failure.seedStep j) < 0 := by
  obtain ⟨-, hnew, hold⟩ := BfgsCoverage.Article.Failure.seed_margins j
  refine ⟨?_, div_neg_of_pos_of_neg hnew hold⟩
  rw [BfgsCoverage.Article.Failure.seedSlope_castSucc]
  obtain ⟨a0, -, a1, -, a2, -⟩ := BfgsCoverage.Article.Failure.accepted_armijo_ratios
  fin_cases j
  · exact lt_trans (by norm_num) a0
  · exact lt_trans (by norm_num) a1
  · exact lt_trans (by norm_num) a2

/-- Item `C/13_L/prose/023` (`companion/chapters/13_L.tex:113`): "The vector $(-1,16)\T$ has
negative inner product with every $g_i$, so $0\notin\operatorname{conv}\{g_i\}$." -/
theorem downhill_pairings :
    (∀ i : Fin 3, dot (SeedOrbit.gradient seedC seedD i) ![-1, 16] < 0) ∧
      (0 : Vec 2) ∉ convexHull ℝ {g0, g1, g2 seedC seedD} := by
  obtain ⟨h0, h1, h2, h3⟩ := BfgsCoverage.Article.Failure.downhill_direction
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · change dot g0 ![-1, 16] < 0
      rw [h0]; norm_num
    · change dot g1 ![-1, 16] < 0
      rw [h1]; norm_num
    · change dot (g2 seedC seedD) ![-1, 16] < 0
      rw [h2]; linarith
  · rw [← BfgsCoverage.Article.LowerCurvature.slopes_eq]
    exact LQuadraticSeed.zero_not_mem_convexHull

/-- $G=Q_0$: the seed maximum is the library's quadratic perturbation with $\mu=0$. -/
theorem seed_objective_eq_zero_quadratic :
    objective seedC seedD = LQuadraticSeed.objective 0 := by
  funext x
  simp [LQuadraticSeed.objective, LQuadraticSeed.quadratic]

/-- Item `C/13_L/prose/025` (`companion/chapters/13_L.tex:122`): "At $x_*$ precisely the first two
branches are active; their gradients differ, so the unique minimizer is nonsmooth. At the origin
$Q_\mu(0)=0$ and the subdifferential is the same nonstationary triangle as for $G$." For every
$\mu>0$, with $x_*=-\bar g/\mu$ (equation `L:eq:minimizer`); the branches of $Q_\mu$ are
$\mu\|x\|^2/2+g_i^Tx$ (`LQuadraticSeed.branch`) with gradients $\mu x+g_i$. -/
theorem minimizer_and_origin (μ : ℝ) (hμ : 0 < μ) (xs : Vec 2)
    (hxs : xs = -(μ⁻¹ • LQuadraticSeed.gbar)) :
    (∀ i, LQuadraticSeed.branch μ i xs = LQuadraticSeed.objective μ xs ↔ i = 0 ∨ i = 1) ∧
      LQuadraticSeed.branchGradient μ xs 0 ≠ LQuadraticSeed.branchGradient μ xs 1 ∧
      ¬ DifferentiableAt ℝ (LQuadraticSeed.objective μ) xs ∧
      LQuadraticSeed.objective μ 0 = 0 ∧
      ConvexSubdifferential.subdifferential (LQuadraticSeed.objective μ) 0 =
        ConvexSubdifferential.subdifferential (objective seedC seedD) 0 ∧
      ConvexSubdifferential.subdifferential (objective seedC seedD) 0 =
        convexHull ℝ {g0, g1, g2 seedC seedD} ∧
      (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential (LQuadraticSeed.objective μ) 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := BfgsCoverage.Article.LowerCurvature.minimizer_nonsmooth μ hμ xs hxs
  have hG : ConvexSubdifferential.subdifferential (objective seedC seedD) 0 =
      convexHull ℝ {g0, g1, g2 seedC seedD} := by
    rw [seed_objective_eq_zero_quadratic, LQuadraticSeed.origin_subdifferential le_rfl,
      BfgsCoverage.Article.LowerCurvature.slopes_eq]
  exact ⟨h1, h2, h3, LQuadraticSeed.objective_zero μ, h4.trans hG.symm, hG, h5⟩

/-! ### Blowing up the shrinking cycle (lines 136-173) -/

/-- Item `C/13_L/prose/033` (`companion/chapters/13_L.tex:162`): "Only its positive-$\tau$ part
represents actual BFGS." At a state with $\tau\le0$ the matrix $H=\tau M(b,e)$ is not positive
definite, so it is not a BFGS state; positive-$\tau$ states near $P_*$ are actual BFGS states by
Lemma `L:lem:agreement` (`agreement`). -/
theorem positive_scale_part (w : LNormalizedReturn.State) (hw : LNormalizedReturn.scale w ≤ 0) :
    ¬ (LNormalizedReturn.scale w • LNormalizedReturn.shape w).PosDef := by
  intro hP
  have h := hP.2 (Pi.single 0 1) (by
    intro he
    have := congrFun he 0
    simp at this)
  have e : star (Pi.single (0 : Fin 2) (1 : ℝ)) ⬝ᵥ
      ((LNormalizedReturn.scale w • LNormalizedReturn.shape w) *ᵥ Pi.single 0 1) =
      LNormalizedReturn.scale w := by
    simp [LNormalizedReturn.shape, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]
  rw [e] at h
  linarith

/-- Item `C/13_L/lemma/L:lem:agreement`, Lemma `L:lem:agreement` (`companion/chapters/13_L.tex:164-166`),
"Agreement with the actual implementation".

"There is an open neighborhood $\mathcal N$ of $P_*$ such that for every state in $\mathcal N$
with $\tau>0$ and every such pair $(c_1,c_2)$, the actual three consecutive full-BFGS iterations
on $Q_\mu$ have exactly the certified trial lists and return map~\eqref{L:eq:return}."

For every $\mu>0$. Reading (as the article's Lemma `art:lower_hyperbolic`, part (i)): from a state
`w` with $\tau>0$ the actual algorithm starts at $x_0=\tau z$, $H_0=\tau M(b,e)$; at each of the
three steps the matrix is positive definite, the point and every query are differentiable, the
point and every query have the certified unique active branch (the branch itinerary), the
search's trial list is the certified list `trialHistory j` with accepted length $\alpha_j$ (every
budget `N ≥ 5`), and the next point and matrix are the full-BFGS step and update with actual
gradients; finally $x_3=\tau'z'$, $H_3=\tau'M(b',e')$ for
$(z',b',e',\tau')=\mathcal T_\mu(z,b,e,\tau)$. -/
theorem agreement (μ : ℝ) (hμ : 0 < μ) :
    ∃ N : Set LNormalizedReturn.State, IsOpen N ∧ LNormalizedReturn.seed ∈ N ∧
      ∀ w ∈ N, 0 < LNormalizedReturn.scale w →
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
              LQuadraticSeed.branch μ (trialActive q) (x j.castSucc + trialLength q •
                bfgsStep (H j.castSucc) (coordinateGradient (LQuadraticSeed.objective μ) (x j.castSucc)) 1)) ∧
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
            LNormalizedReturn.shape (LNormalizedReturn.returnMap μ w) := by
  obtain ⟨⟨N, hN, hw⟩, -, -⟩ := BfgsCoverage.Article.LowerCurvature.lower_hyperbolic μ hμ
  exact ⟨interior N, isOpen_interior, mem_interior_iff_mem_nhds.mpr hN,
    fun w hwN => hw w (interior_subset hwN)⟩

/-- Item `C/13_L/disp/018` (`companion/chapters/13_L.tex:169-171`), in the proof of Lemma
`L:lem:agreement`: "At a query $\tau Z$ [...] Its function value divided by $\tau$ is
\[ G(Z)+\tfrac{\mu\tau}{2}\norm Z^2." \] -/
theorem query_value_scaled (μ τ : ℝ) (hτ : 0 < τ) (Z : Vec 2) :
    LQuadraticSeed.objective μ (τ • Z) / τ = objective seedC seedD Z + μ * τ / 2 * sqNorm Z := by
  rw [LQuadraticSeed.objective, LQuadraticSeed.quadratic, RadialPower.sqNorm_smul,
    BfgsCoverage.Article.Failure.seed_objective_homogeneous hτ.le]
  field_simp
  ring

/-! ### A certified hyperbolic fixed point (lines 187-239) -/

/-- Item `C/13_L/prose/034` (`companion/chapters/13_L.tex:189`): "At $\tau=0$ the matrix return
depends only on $(b,e)$, not on $z$." Two states with $\tau=0$ and the same $(b,e)$ have the same
matrix coordinates $(M_3)_{12}/(M_3)_{11}$, $(M_3)_{22}/(M_3)_{11}$ of $\mathcal T_\mu$. -/
theorem boundary_shape_return (μ : ℝ) (w w' : LNormalizedReturn.State)
    (hw : LNormalizedReturn.scale w = 0) (hw' : LNormalizedReturn.scale w' = 0)
    (h2 : w 2 = w' 2) (h3 : w 3 = w' 3) :
    LNormalizedReturn.returnMap μ w 2 = LNormalizedReturn.returnMap μ w' 2 ∧
      LNormalizedReturn.returnMap μ w 3 = LNormalizedReturn.returnMap μ w' 3 := by
  have e := (BfgsCoverage.Article.LowerCurvature.shape_map_def μ w hw).1
  have e' := (BfgsCoverage.Article.LowerCurvature.shape_map_def μ w' hw').1
  rw [h2, h3, e'] at e
  exact ⟨(congrFun e 0).symm, (congrFun e 1).symm⟩

/-- The derivative of the normalized shape map at $(0,1)$ is the library's
`LShapeDerivative.jacobian seedC seedD` (the article's `shape_jacobian_eq`). -/
theorem shape_jacobian {J : Mat 2}
    (hJ : ∀ i j, J i j = fderiv ℝ (LShapeDerivative.shapeMap seedC seedD) ![0, 1] (Pi.single j 1) i) :
    J = LShapeDerivative.jacobian seedC seedD :=
  BfgsCoverage.Article.LowerCurvature.shape_jacobian_eq hJ

/-- Item `C/13_L/disp/020` (`companion/chapters/13_L.tex:194-199`), with line 193: "Let $J$ be its
derivative at $(0,1)$. [...] their decimal displays are
\[ J\simeq\begin{pmatrix}1.112398625073290&0.645970102731598\\
   0.751501570427498&0.490513688583175\end{pmatrix}." \]
A decimal display is the entry rounded to fifteen decimals: each displayed decimal is within half
a unit of the fifteenth decimal of the actual entry $J_{ij}=\partial S_i/\partial x_j$. -/
theorem jacobian_display (J : Mat 2)
    (hJ : ∀ i j, J i j = fderiv ℝ (LShapeDerivative.shapeMap seedC seedD) ![0, 1] (Pi.single j 1) i) :
    |J 0 0 - 1.112398625073290| < 1 / (2 * 10 ^ 15) ∧ |J 0 1 - 0.645970102731598| < 1 / (2 * 10 ^ 15) ∧
      |J 1 0 - 0.751501570427498| < 1 / (2 * 10 ^ 15) ∧
      |J 1 1 - 0.490513688583175| < 1 / (2 * 10 ^ 15) := by
  have he (i j : Fin 2) : J i j = LShapePrecision.actualEntry i j := hJ i j
  have h00 := LShapePrecision.corrected_display_error 0 0
  have h01 := LShapePrecision.corrected_display_error 0 1
  have h10 := LShapePrecision.corrected_display_error 1 0
  have h11 := LShapePrecision.corrected_display_error 1 1
  rw [← he] at h00 h01 h10 h11
  norm_num [LShapePrecision.correctedDisplay15] at h00 h01 h10 h11 ⊢
  exact ⟨h00, h01, h10, h11⟩

/-- Item `C/13_L/prose/037` (`companion/chapters/13_L.tex:200-201`): "$P_J(\lambda)=\lambda^2
-\operatorname{tr}(J)\lambda+\det J$". The library's `LShapeSpectralAlgebra.characteristic J` is
$P_J$. -/
theorem characteristic_def (J : Mat 2) (t : ℝ) :
    LShapeSpectralAlgebra.characteristic J t = t ^ 2 - J.trace * t + J.det := by
  rw [LShapeSpectralAlgebra.characteristic, Matrix.trace_fin_two, Matrix.det_fin_two]

/-- Item `C/13_L/disp/021`, equation `L:eq:eigshape` (`companion/chapters/13_L.tex:202-204`), with
lines 200-201: "using exact rational interval signs of
$P_J(\lambda)=\lambda^2-\operatorname{tr}(J)\lambda+\det J$, it proves
\[ 0.038<\lambda_s<0.039,\qquad 1.564<\lambda_u<1.565." \]
The eigenvalues $\lambda_s,\lambda_u$ of $J$: $P_J(\lambda)=(\lambda-\lambda_s)(\lambda-\lambda_u)$. -/
theorem shape_eigenvalues (J : Mat 2)
    (hJ : ∀ i j, J i j = fderiv ℝ (LShapeDerivative.shapeMap seedC seedD) ![0, 1] (Pi.single j 1) i) :
    ∃ ls lu : ℝ, ((0.038 : ℝ) < ls ∧ ls < 0.039) ∧ ((1.564 : ℝ) < lu ∧ lu < 1.565) ∧
      ∀ t : ℝ, t ^ 2 - J.trace * t + J.det = (t - ls) * (t - lu) := by
  rw [shape_jacobian hJ]
  obtain ⟨ls, lu, hs, hu, -, -, hf⟩ := LShapeSpectrum.source_shape_roots
  refine ⟨ls, lu, ⟨by norm_num at hs ⊢; linarith [hs.1], by norm_num at hs ⊢; linarith [hs.2]⟩,
    ⟨by norm_num at hu ⊢; linarith [hu.1], by norm_num at hu ⊢; linarith [hu.2]⟩, fun t => ?_⟩
  rw [← characteristic_def, hf]

/-- Item `C/13_L/prose/038` (`companion/chapters/13_L.tex:205`): "Specifically $P_J(0.038)>0$,
$P_J(0.039)<0$, $P_J(1.564)<0$, and $P_J(1.565)>0$ throughout the algebraic root box. The two
disjoint sign-change intervals contain the two distinct real roots." For every $(c,d)$ in the
root box $\|(c,d)-(c_0,d_0)\|_\infty\le10^{-30}$, with $J$ the forward-mode derivative of the
normalized shape map at $(c,d)$ (`LShapeDerivative.jacobian c d`, the actual $J$ at the root):
the four signs, and $P_J(\lambda)=(\lambda-\lambda_s)(\lambda-\lambda_u)$ with
$\lambda_s\in(0.038,0.039)$, $\lambda_u\in(1.564,1.565)$. -/
theorem characteristic_signs_box (x : Vec 2) (hx : ‖x - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30) :
    0 < LShapeSpectralAlgebra.characteristic (LShapeDerivative.jacobian (x 0) (x 1)) 0.038 ∧
      LShapeSpectralAlgebra.characteristic (LShapeDerivative.jacobian (x 0) (x 1)) 0.039 < 0 ∧
      LShapeSpectralAlgebra.characteristic (LShapeDerivative.jacobian (x 0) (x 1)) 1.564 < 0 ∧
      0 < LShapeSpectralAlgebra.characteristic (LShapeDerivative.jacobian (x 0) (x 1)) 1.565 ∧
      ∃ ls lu : ℝ, ((0.038 : ℝ) < ls ∧ ls < 0.039) ∧ ((1.564 : ℝ) < lu ∧ lu < 1.565) ∧
        ∀ t, LShapeSpectralAlgebra.characteristic (LShapeDerivative.jacobian (x 0) (x 1)) t =
          (t - ls) * (t - lu) := by
  obtain ⟨hc, hd⟩ := LShapeSpectrum.box_of_original_ball (by simpa [AlgebraicSeed.radius] using hx)
  obtain ⟨h00, h01, h10, h11⟩ := LShapeIntervalCertificate.jacobian_bounds hc hd
  obtain ⟨s1, s2, s3, s4⟩ := LShapeSpectralAlgebra.signs_of_entry_bounds h00 h01 h10 h11
  obtain ⟨ls, lu, hs, hu, -, -, hf⟩ := LShapeSpectralAlgebra.two_roots_of_signs s1 s2 s3 s4
  refine ⟨by norm_num at s1 ⊢; exact s1, by norm_num at s2 ⊢; exact s2, by norm_num at s3 ⊢; exact s3,
    by norm_num at s4 ⊢; exact s4, ls, lu, ⟨by norm_num at hs ⊢; linarith [hs.1],
      by norm_num at hs ⊢; linarith [hs.2]⟩, ⟨by norm_num at hu ⊢; linarith [hu.1],
      by norm_num at hu ⊢; linarith [hu.2]⟩, hf⟩

/-! #### The factor $\mu$ in the last column of $D\mathcal T_\mu(P_*)$

In the substeps the scale enters only through $\mu\tau$ (`substep_scale`), so
$\mathcal T_\mu=D_{1/\mu}\circ\mathcal T_1\circ S_\mu$ with $S_\mu$ multiplying $\tau$ by $\mu$ and
$D_{1/\mu}$ dividing the last coordinate by $\mu$ (`returnMap_scale`); $S_\mu$ fixes $P_*$. -/

/-- $S_\mu(z,b,e,\tau)=(z,b,e,\mu\tau)$. -/
theorem scaleLast_apply (μ : ℝ) (w : LNormalizedReturn.State) :
    LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ] w = ![w 0, w 1, w 2, w 3, μ * w 4] := by
  ext i
  fin_cases i <;> simp [LBlockSplitting.diagonalMap_apply]

/-- The three substeps depend on $(\mu,\tau)$ only through $\mu\tau$. -/
theorem substep_scale (μ τ : ℝ) (j : Fin 3) (s : LNormalizedReturn.PhaseState) :
    LNormalizedReturn.substep 1 (μ * τ) j s = LNormalizedReturn.substep μ τ j s := by
  simp only [LNormalizedReturn.substep, LNormalizedReturn.step, LNormalizedReturn.secant,
    LNormalizedReturn.currentGradient, one_mul]

theorem internal_scale (μ : ℝ) (w : LNormalizedReturn.State) (k : ℕ) :
    LNormalizedReturn.internal 1 (LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ] w) k =
      LNormalizedReturn.internal μ w k := by
  induction k with
  | zero =>
    show LNormalizedReturn.initial _ = LNormalizedReturn.initial w
    rw [scaleLast_apply]
    rfl
  | succ k ih =>
    rw [LNormalizedReturn.internal, LNormalizedReturn.internal, ih]
    rw [scaleLast_apply]
    exact substep_scale μ (w 4) _ _

theorem returnMap_scale (μ : ℝ) (hμ : μ ≠ 0) (w : LNormalizedReturn.State) :
    LNormalizedReturn.returnMap μ w = LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ⁻¹]
      (LNormalizedReturn.returnMap 1 (LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ] w)) := by
  have hf : LNormalizedReturn.returnFactor 1 (LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ] w) =
      LNormalizedReturn.returnFactor μ w := by
    simp only [LNormalizedReturn.returnFactor, internal_scale]
  ext i
  fin_cases i <;>
    simp [LNormalizedReturn.returnMap, internal_scale, hf, LBlockSplitting.diagonalMap_apply,
      LNormalizedReturn.scale]
  all_goals field_simp
  all_goals ring

theorem fderiv_returnMap_scale (μ : ℝ) (hμ : μ ≠ 0) :
    fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed =
      (LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ⁻¹]).comp
        ((fderiv ℝ (LNormalizedReturn.returnMap 1) LNormalizedReturn.seed).comp
          (LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ])) := by
  have hS : LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ] LNormalizedReturn.seed =
      LNormalizedReturn.seed := by
    rw [scaleLast_apply]
    ext i
    fin_cases i <;> simp [LNormalizedReturn.seed]
  have h1 : HasFDerivAt (LNormalizedReturn.returnMap 1)
      (fderiv ℝ (LNormalizedReturn.returnMap 1) LNormalizedReturn.seed)
      (LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ] LNormalizedReturn.seed) := by
    rw [hS]
    exact (LNormalizedReturn.analytic_returnMap_seed 1).differentiableAt.hasFDerivAt
  have hcomp := (LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ⁻¹]).hasFDerivAt.comp LNormalizedReturn.seed
    (h1.comp LNormalizedReturn.seed (LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ]).hasFDerivAt)
  have he : LNormalizedReturn.returnMap μ = fun w => LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ⁻¹]
      (LNormalizedReturn.returnMap 1 (LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ] w)) :=
    funext (returnMap_scale μ hμ)
  rw [he]
  exact hcomp.fderiv

/-- Item `C/13_L/disp/022`, equation `L:eq:jacobian` (`companion/chapters/13_L.tex:208-215`), with
line 207: "The full derivative has the analytically determined block-triangular form
\[ D\mathcal T_\mu(P_*)=\begin{pmatrix}\rho^{-1}I_2&C&\mu a\\0&J&\mu b\\0&0&\rho\end{pmatrix}." \]
The matrix of $D\mathcal T_\mu(P_*)$ in the coordinates $(z_1,z_2,b,e,\tau)$, with $J$ the
Jacobian matrix of the normalized shape map; the blocks $C$, $a$, $b$ are the same for every
$\mu>0$ (the $\tau$-column of the first four rows is $\mu$ times a fixed vector). -/
theorem jacobian_block_form :
    ∃ (C : Mat 2) (a b : Vec 2), ∀ μ : ℝ, 0 < μ → ∀ J : Mat 2,
      (∀ i j, J i j = fderiv ℝ (LShapeDerivative.shapeMap seedC seedD) ![0, 1] (Pi.single j 1) i) →
      LinearMap.toMatrix' (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed).toLinearMap =
        !![seedRatio⁻¹, 0, C 0 0, C 0 1, μ * a 0;
           0, seedRatio⁻¹, C 1 0, C 1 1, μ * a 1;
           0, 0, J 0 0, J 0 1, μ * b 0;
           0, 0, J 1 0, J 1 1, μ * b 1;
           0, 0, 0, 0, seedRatio] := by
  let L1 := fderiv ℝ (LNormalizedReturn.returnMap 1) LNormalizedReturn.seed
  refine ⟨!![L1 (Pi.single 2 1) 0, L1 (Pi.single 3 1) 0; L1 (Pi.single 2 1) 1, L1 (Pi.single 3 1) 1],
    ![L1 (Pi.single 4 1) 0, L1 (Pi.single 4 1) 1], ![L1 (Pi.single 4 1) 2, L1 (Pi.single 4 1) 3],
    fun μ hμ J hJ => ?_⟩
  rw [shape_jacobian hJ]
  have hsc := fderiv_returnMap_scale μ hμ.ne'
  have hD (v : LNormalizedReturn.State) (i : Fin 5) (hi : i.val < 4) :
      LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ⁻¹] v i = v i := by
    fin_cases i <;> simp [LBlockSplitting.diagonalMap_apply] at hi ⊢
  have hS (j : Fin 5) (hj : j.val < 4) :
      LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ] (Pi.single j 1) = Pi.single j 1 := by
    rw [scaleLast_apply]
    ext k
    fin_cases j <;> fin_cases k <;> simp [Pi.single_apply] at hj ⊢
  have hS4 : LBlockSplitting.diagonalMap ![1, 1, 1, 1, μ] (Pi.single 4 1) =
      μ • (Pi.single 4 1 : LNormalizedReturn.State) := by
    rw [scaleLast_apply]
    ext k
    fin_cases k <;> simp [Pi.single_apply]
  have hmid (j : Fin 5) (hj : j.val < 4) (i : Fin 5) (hi : i.val < 4) :
      fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed (Pi.single j 1) i = L1 (Pi.single j 1) i := by
    rw [hsc]
    simp only [ContinuousLinearMap.comp_apply, hS j hj]
    exact hD _ i hi
  have hlast (i : Fin 5) (hi : i.val < 4) :
      fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed (Pi.single 4 1) i =
        μ * L1 (Pi.single 4 1) i := by
    rw [hsc]
    simp only [ContinuousLinearMap.comp_apply, hS4, map_smul]
    rw [Pi.smul_apply, hD _ i hi, smul_eq_mul]
  have hrow (v : LNormalizedReturn.State) :
      fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed v 4 = seedRatio * v 4 :=
    LNormalizedReturn.return_derivative_last_row μ v
  have col0 : fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed (Pi.single 0 1) =
      ![seedRatio⁻¹, 0, 0, 0, 0] := by
    have h : fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed (Pi.single 0 1) =
        seedRatio⁻¹ • (Pi.single 0 1 : LNormalizedReturn.State) := by
      have h' := LNormalizedReturn.return_derivative_point_columns μ (Pi.single 0 1)
      rw [BfgsCoverage.Article.LowerCurvature.pointLift_single] at h'
      exact h'
    rw [h]
    ext k
    fin_cases k <;> simp [Pi.single_apply]
  have col1 : fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed (Pi.single 1 1) =
      ![0, seedRatio⁻¹, 0, 0, 0] := by
    have h : fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed (Pi.single 1 1) =
        seedRatio⁻¹ • (Pi.single 1 1 : LNormalizedReturn.State) := by
      have h' := LNormalizedReturn.return_derivative_point_columns μ (Pi.single 1 1)
      rw [BfgsCoverage.Article.LowerCurvature.pointLift_single] at h'
      exact h'
    rw [h]
    ext k
    fin_cases k <;> simp [Pi.single_apply]
  have col2 : fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed (Pi.single 2 1) =
      ![L1 (Pi.single 2 1) 0, L1 (Pi.single 2 1) 1, LShapeDerivative.jacobian seedC seedD 0 0,
        LShapeDerivative.jacobian seedC seedD 1 0, 0] := by
    ext k
    fin_cases k
    · exact hmid 2 (by decide) 0 (by decide)
    · exact hmid 2 (by decide) 1 (by decide)
    · exact LShapeSpectrum.actual_middle_block μ 0 0
    · exact LShapeSpectrum.actual_middle_block μ 1 0
    · simp [hrow, Pi.single_apply]
  have col3 : fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed (Pi.single 3 1) =
      ![L1 (Pi.single 3 1) 0, L1 (Pi.single 3 1) 1, LShapeDerivative.jacobian seedC seedD 0 1,
        LShapeDerivative.jacobian seedC seedD 1 1, 0] := by
    ext k
    fin_cases k
    · exact hmid 3 (by decide) 0 (by decide)
    · exact hmid 3 (by decide) 1 (by decide)
    · exact LShapeSpectrum.actual_middle_block μ 0 1
    · exact LShapeSpectrum.actual_middle_block μ 1 1
    · simp [hrow, Pi.single_apply]
  have col4 : fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed (Pi.single 4 1) =
      ![μ * L1 (Pi.single 4 1) 0, μ * L1 (Pi.single 4 1) 1, μ * L1 (Pi.single 4 1) 2,
        μ * L1 (Pi.single 4 1) 3, seedRatio] := by
    ext k
    fin_cases k
    · exact hlast 0 (by decide)
    · exact hlast 1 (by decide)
    · exact hlast 2 (by decide)
    · exact hlast 3 (by decide)
    · simp [hrow, Pi.single_apply]
  ext i j
  have hsingle : (fun j' => if j' = j then (1 : ℝ) else 0) = (Pi.single j 1 : LNormalizedReturn.State) := by
    funext j'
    simp [Pi.single_apply]
  rw [LinearMap.toMatrix'_apply, hsingle]
  simp only [ContinuousLinearMap.coe_coe]
  fin_cases j
  · show fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed (Pi.single 0 1) i = _
    rw [col0]; fin_cases i <;> rfl
  · show fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed (Pi.single 1 1) i = _
    rw [col1]; fin_cases i <;> rfl
  · show fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed (Pi.single 2 1) i = _
    rw [col2]; fin_cases i <;> rfl
  · show fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed (Pi.single 3 1) i = _
    rw [col3]; fin_cases i <;> rfl
  · show fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed (Pi.single 4 1) i = _
    rw [col4]; fin_cases i <;> rfl

/-- Item `C/13_L/prose/041` (`companion/chapters/13_L.tex:216`): "The upper left block follows
because, at $\tau=0$, $Z_3=z+v(b,e)$ and $r$ is independent of $z$. The last row follows from
$\tau^+=\tau r$." At a state with $\tau=0$: $Z_3=z+v(b,e)$ with $v(b,e)$ the value of $Z_3$ at
$(0,0,b,e,0)$, and $r=(M_3)_{11}$ is its value there; the last coordinate of $\mathcal T_\mu$ is
$\tau r$, so the last row of $D\mathcal T_\mu(P_*)$ is $(0,0,0,0,\rho)$. -/
theorem block_reasons (μ : ℝ) (w : LNormalizedReturn.State) (hw : LNormalizedReturn.scale w = 0) :
    (LNormalizedReturn.internal μ w 3).1 =
        LNormalizedReturn.point w + (LNormalizedReturn.internal μ ![0, 0, w 2, w 3, 0] 3).1 ∧
      LNormalizedReturn.returnFactor μ w = LNormalizedReturn.returnFactor μ ![0, 0, w 2, w 3, 0] ∧
      LNormalizedReturn.scale (LNormalizedReturn.returnMap μ w) =
        LNormalizedReturn.scale w * LNormalizedReturn.returnFactor μ w ∧
      ∀ v : LNormalizedReturn.State,
        (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed v) 4 = seedRatio * v 4 := by
  have h0 : LNormalizedReturn.scale (![0, 0, w 2, w 3, 0] : LNormalizedReturn.State) = 0 := rfl
  have hw' : w = LNormalizedReturn.shiftPoint (LNormalizedReturn.point w) ![0, 0, w 2, w 3, 0] := by
    ext i
    fin_cases i <;> simp [LNormalizedReturn.shiftPoint, LNormalizedReturn.point]
    exact hw
  have hi := LNormalizedReturn.internal_boundary_translate μ h0 (LNormalizedReturn.point w) 3
  have hr := LNormalizedReturn.returnFactor_boundary_translate μ h0 (LNormalizedReturn.point w)
  rw [← hw'] at hi hr
  refine ⟨?_, hr, rfl, LNormalizedReturn.return_derivative_last_row μ⟩
  rw [hi, add_comm]

/-- $0.06<\rho<0.061$. -/
theorem ratio_bounds : (0.06 : ℝ) < seedRatio ∧ seedRatio < 0.061 := by
  obtain ⟨-, h2, h3⟩ := BfgsCoverage.Article.Failure.seed_rho
  exact ⟨by linarith, h3⟩

/-- Item `C/13_L/disp/023` (`companion/chapters/13_L.tex:219-221`), with line 218: "The
eigenvalues are therefore
\[ \rho^{-1},\ \rho^{-1},\ \lambda_s,\ \lambda_u,\ \rho." \]
With $\lambda_s,\lambda_u$ the eigenvalues of $J$ (display `C/13_L/disp/021`: the roots of $P_J$),
the characteristic polynomial of $D\mathcal T_\mu(P_*)$ is
$(X-\rho^{-1})^2(X-\lambda_s)(X-\lambda_u)(X-\rho)$. -/
theorem return_eigenvalues (μ : ℝ) (J : Mat 2)
    (hJ : ∀ i j, J i j = fderiv ℝ (LShapeDerivative.shapeMap seedC seedD) ![0, 1] (Pi.single j 1) i) :
    ∃ ls lu : ℝ, ((0.038 : ℝ) < ls ∧ ls < 0.039) ∧ ((1.564 : ℝ) < lu ∧ lu < 1.565) ∧
      (∀ t : ℝ, t ^ 2 - J.trace * t + J.det = (t - ls) * (t - lu)) ∧
      (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed).toLinearMap.charpoly =
        (Polynomial.X - Polynomial.C seedRatio⁻¹) ^ 2 * (Polynomial.X - Polynomial.C ls) *
          (Polynomial.X - Polynomial.C lu) * (Polynomial.X - Polynomial.C seedRatio) := by
  rw [shape_jacobian hJ]
  obtain ⟨ls, lu, hs, hu, hsroot, huroot, hfactor⟩ := LShapeSpectrum.source_shape_roots
  have hr := tight_ratio root_tight_box.1 root_tight_box.2
  have hs0 : 0 < ls := by linarith [hs.1]
  have hsr : ls < seedRatio := by linarith [hs.2, hr.1]
  have hu1 : 1 < lu := by linarith [hu.1]
  have hr2 : 2 < 1 / seedRatio := (lt_div_iff₀ source_ratio_pos_lt_one.1).mpr (by linarith [hr.2])
  rw [one_div] at hr2
  have hua : lu < seedRatio⁻¹ := by linarith [hu.2]
  have hs' : (ls - LShapeDerivative.jacobian seedC seedD 0 0) * (ls - LShapeDerivative.jacobian seedC seedD 1 1) =
      LShapeDerivative.jacobian seedC seedD 0 1 * LShapeDerivative.jacobian seedC seedD 1 0 := by
    dsimp [LShapeSpectralAlgebra.characteristic] at hsroot
    nlinarith
  have hu' : (lu - LShapeDerivative.jacobian seedC seedD 0 0) * (lu - LShapeDerivative.jacobian seedC seedD 1 1) =
      LShapeDerivative.jacobian seedC seedD 0 1 * LShapeDerivative.jacobian seedC seedD 1 0 := by
    dsimp [LShapeSpectralAlgebra.characteristic] at huroot
    nlinarith
  obtain ⟨E, -, hE⟩ := LExactDiagonalization.exact_block_diagonalization (LReturnOrbitCore.actual_block μ)
    source_ratio_pos_lt_one.1 source_ratio_pos_lt_one.2 hs0 hsr hu1 hua
    LShapeSpectrum.source_jacobian_offdiag_positive.ne' hs' hu'
  refine ⟨ls, lu, ⟨by norm_num at hs ⊢; linarith [hs.1], by norm_num at hs ⊢; linarith [hs.2]⟩,
    ⟨by norm_num at hu ⊢; linarith [hu.1], by norm_num at hu ⊢; linarith [hu.2]⟩, fun t => ?_,
    LExactDiagonalization.charpoly_of_exact_diagonalization E hE⟩
  rw [← characteristic_def, hfactor]

/-- The roots, with multiplicity, of $(X-a)^2(X-b)(X-c)(X-d)$. -/
theorem five_roots (a b c d : ℝ) :
    ((Polynomial.X - Polynomial.C a) ^ 2 * (Polynomial.X - Polynomial.C b) *
      (Polynomial.X - Polynomial.C c) * (Polynomial.X - Polynomial.C d)).roots = {a, a, b, c, d} := by
  have he : (Polynomial.X - Polynomial.C a) ^ 2 * (Polynomial.X - Polynomial.C b) *
      (Polynomial.X - Polynomial.C c) * (Polynomial.X - Polynomial.C d) =
      (({a, a, b, c, d} : Multiset ℝ).map (fun t => Polynomial.X - Polynomial.C t)).prod := by
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
      Multiset.prod_singleton]
    ring
  rw [he, Polynomial.roots_multiset_prod_X_sub_C]

/-- Item `C/13_L/prose/042` (`companion/chapters/13_L.tex:222`): "None lies on the unit circle
and none is zero. There are exactly two stable eigenvalues. The derivative is invertible, so the
inverse function theorem makes $\mathcal T_\mu$ a local diffeomorphism." The eigenvalues, with
multiplicity, are the five roots of the characteristic polynomial (all real); the stable ones
(modulus less than one) are exactly $\lambda_s$ and $\rho$; no complex root has modulus one; zero
is not a root; $D\mathcal T_\mu(P_*)$ is a linear isomorphism; $\mathcal T_\mu$ is smooth at
$P_*$ and has a smooth local inverse $S$ ($S\circ\mathcal T_\mu=\mathrm{id}$ and
$\mathcal T_\mu\circ S=\mathrm{id}$ near $P_*$). -/
theorem hyperbolic_spectrum (μ : ℝ) :
    ∃ ls lu : ℝ, ((0.038 : ℝ) < ls ∧ ls < 0.039) ∧ ((1.564 : ℝ) < lu ∧ lu < 1.565) ∧
      (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed).toLinearMap.charpoly.roots =
        {seedRatio⁻¹, seedRatio⁻¹, ls, lu, seedRatio} ∧
      Multiset.filter (fun t => |t| < 1) {seedRatio⁻¹, seedRatio⁻¹, ls, lu, seedRatio} = {ls, seedRatio} ∧
      (∀ z : ℂ, ‖z‖ = 1 → Polynomial.eval₂ (algebraMap ℝ ℂ) z
        (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed).toLinearMap.charpoly ≠ 0) ∧
      (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed).toLinearMap.charpoly.eval 0 ≠ 0 ∧
      (∃ E : LNormalizedReturn.State ≃L[ℝ] LNormalizedReturn.State,
        E.toContinuousLinearMap = fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed) ∧
      ContDiffAt ℝ ⊤ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed ∧
      ∃ S : LNormalizedReturn.State → LNormalizedReturn.State, ContDiffAt ℝ ⊤ S LNormalizedReturn.seed ∧
        S LNormalizedReturn.seed = LNormalizedReturn.seed ∧
        (∀ᶠ x in 𝓝 LNormalizedReturn.seed, S (LNormalizedReturn.returnMap μ x) = x) ∧
        (∀ᶠ y in 𝓝 LNormalizedReturn.seed, LNormalizedReturn.returnMap μ (S y) = y) := by
  obtain ⟨ls, lu, hs, hu, -, -, -, hchar⟩ := LReturnSpectrum.actual_spectral_contract μ
  have hrs := source_ratio_pos_lt_one
  have hra : 1 < seedRatio⁻¹ := (one_lt_inv₀ hrs.1).mpr hrs.2
  have hls : 0 < ls := by linarith [hs.1]
  refine ⟨ls, lu, ⟨by norm_num at hs ⊢; linarith [hs.1], by norm_num at hs ⊢; linarith [hs.2]⟩,
    ⟨by norm_num at hu ⊢; linarith [hu.1], by norm_num at hu ⊢; linarith [hu.2]⟩,
    by rw [hchar, five_roots], ?_, fun z hz => LReturnSpectrum.actual_no_unit_complex_root μ hz,
    fun h0 => (LReturnSpectrum.actual_no_zero_or_unit_real_root μ (lam := 0) (by rw [← Polynomial.IsRoot.def]; exact h0)).1 rfl,
    LReturnLocalInverse.actual_derivative_equiv μ, (LNormalizedReturn.analytic_returnMap_seed μ).contDiffAt,
    LReturnLocalInverse.actual_local_inverse μ⟩
  have h1 : ¬ |seedRatio⁻¹| < 1 := by rw [abs_of_pos (by linarith)]; linarith
  have h2 : |ls| < 1 := by rw [abs_of_pos hls]; linarith [hs.2]
  have h3 : ¬ |lu| < 1 := by rw [abs_of_pos (by linarith [hu.1])]; linarith [hu.1]
  have h4 : |seedRatio| < 1 := by rw [abs_of_pos hrs.1]; exact hrs.2
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons, h1, h2, h3, h4, if_true, if_false,
    Multiset.filter_singleton]
  rfl

/-- Item `C/13_L/prose/043` (`companion/chapters/13_L.tex:224`): "Crucially $\rho$ is different
from every eigenvalue of the upper left $4\times4$ block. Thus its eigenvector can be chosen with
last coordinate one: solve the top four linear equations after assigning $v_\tau=1$. The stable
subspace is not contained in the artificial boundary $\{\tau=0\}$." The upper left block is
the submatrix of the first four coordinates; the stable subspace is the article's
`LowerCurvature.stableSubspace` (the sum of the generalized eigenspaces of the eigenvalues of
modulus less than one). For every $\mu>0$. -/
theorem scale_eigenvector (μ : ℝ) (hμ : 0 < μ) :
    (∀ v : Fin 4 → ℝ, ((LinearMap.toMatrix' (fderiv ℝ (LNormalizedReturn.returnMap μ)
        LNormalizedReturn.seed).toLinearMap).submatrix Fin.castSucc Fin.castSucc) *ᵥ v = seedRatio • v →
        v = 0) ∧
      (∃ v : LNormalizedReturn.State, v 4 = 1 ∧
        (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed) v = seedRatio • v) ∧
      ∃ v ∈ BfgsCoverage.Article.LowerCurvature.stableSubspace
        (fderiv ℝ (LNormalizedReturn.returnMap μ) LNormalizedReturn.seed).toLinearMap, v 4 ≠ 0 := by
  obtain ⟨-, -, hstab⟩ := BfgsCoverage.Article.LowerCurvature.lower_hyperbolic μ hμ
  obtain ⟨v, hv, hv4⟩ := hstab
  refine ⟨fun v hv => ?_, LReturnSpectrum.actual_scale_eigenvector μ, v, hv, by rw [hv4]; norm_num⟩
  obtain ⟨s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, hform⟩ :=
    BfgsCoverage.Article.LowerCurvature.return_block_form μ (LShapeDerivative.jacobian seedC seedD)
      (fun i j => (LShapePrecision.actualEntry_eq_jacobian i j).symm)
  rw [hform] at hv
  obtain ⟨ls, lu, hs, hu, -, -, hf⟩ := LShapeSpectrum.source_shape_roots
  have hρ := ratio_bounds
  have hP : LShapeSpectralAlgebra.characteristic (LShapeDerivative.jacobian seedC seedD) seedRatio ≠ 0 := by
    rw [hf]
    apply mul_ne_zero <;> intro h <;> norm_num at hs hu <;> linarith
  have e0 := congrFun hv 0
  have e1 := congrFun hv 1
  have e2 := congrFun hv 2
  have e3 := congrFun hv 3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] at e0 e1 e2 e3
  have hD : (LShapeDerivative.jacobian seedC seedD 0 0 - seedRatio) *
      (LShapeDerivative.jacobian seedC seedD 1 1 - seedRatio) -
      LShapeDerivative.jacobian seedC seedD 0 1 * LShapeDerivative.jacobian seedC seedD 1 0 ≠ 0 := by
    intro h
    apply hP
    dsimp [LShapeSpectralAlgebra.characteristic]
    linear_combination h
  have hv2 : v 2 = 0 := by
    have h : ((LShapeDerivative.jacobian seedC seedD 0 0 - seedRatio) *
        (LShapeDerivative.jacobian seedC seedD 1 1 - seedRatio) -
        LShapeDerivative.jacobian seedC seedD 0 1 * LShapeDerivative.jacobian seedC seedD 1 0) * v 2 = 0 := by
      linear_combination (LShapeDerivative.jacobian seedC seedD 1 1 - seedRatio) * e2 -
        LShapeDerivative.jacobian seedC seedD 0 1 * e3
    exact (mul_eq_zero.mp h).resolve_left hD
  have hv3 : v 3 = 0 := by
    have h : ((LShapeDerivative.jacobian seedC seedD 0 0 - seedRatio) *
        (LShapeDerivative.jacobian seedC seedD 1 1 - seedRatio) -
        LShapeDerivative.jacobian seedC seedD 0 1 * LShapeDerivative.jacobian seedC seedD 1 0) * v 3 = 0 := by
      linear_combination (LShapeDerivative.jacobian seedC seedD 0 0 - seedRatio) * e3 -
        LShapeDerivative.jacobian seedC seedD 1 0 * e2
    exact (mul_eq_zero.mp h).resolve_left hD
  have hri : seedRatio⁻¹ - seedRatio ≠ 0 := by
    have hrs := source_ratio_pos_lt_one
    have : 1 < seedRatio⁻¹ := (one_lt_inv₀ hrs.1).mpr hrs.2
    linarith
  rw [hv2, hv3] at e0 e1
  have hv0 : v 0 = 0 := by
    have h : (seedRatio⁻¹ - seedRatio) * v 0 = 0 := by linear_combination e0
    exact (mul_eq_zero.mp h).resolve_left hri
  have hv1 : v 1 = 0 := by
    have h : (seedRatio⁻¹ - seedRatio) * v 1 = 0 := by linear_combination e1
    exact (mul_eq_zero.mp h).resolve_left hri
  ext i
  fin_cases i
  · exact hv0
  · exact hv1
  · exact hv2
  · exact hv3

/-- Item `C/13_L/disp/024` (`companion/chapters/13_L.tex:232-234`), in the proof of Theorem
`L:thm:global`: "Its physical states satisfy
\[ x_{3m}=\tau_m z_m\to0,\qquad H_{3m}=\tau_mM(b_m,e_m)\to0." \]
Standing assumptions: the return-map orbit $(z_m,b_m,e_m,\tau_m)$ (`O.state m`) of an orbit `O`
along which the decisions are those of every admissible pair (`LUniform.Orbit`, the orbits of the
proof), converging to $P_*$; its physical states are `O.x k`, `O.H k`. -/
theorem orbit_physical_states (μ : ℝ) (O : LUniform.Orbit μ)
    (hO : Tendsto O.state atTop (𝓝 LNormalizedReturn.seed)) :
    (∀ m, O.x (3 * m) = LNormalizedReturn.scale (O.state m) • LNormalizedReturn.point (O.state m) ∧
      O.H (3 * m) = LNormalizedReturn.scale (O.state m) • LNormalizedReturn.shape (O.state m)) ∧
      Tendsto (fun m => O.x (3 * m)) atTop (𝓝 0) ∧ Tendsto (fun m => O.H (3 * m)) atTop (𝓝 0) := by
  have h₀ : LUniform.Admissible (1/10000) (1/2) := LUniform.sourcePair
  have h3 : Tendsto (fun m : ℕ => 3 * m) atTop atTop :=
    tendsto_id.const_mul_atTop' (by norm_num : (0 : ℕ) < 3)
  refine ⟨fun m => ?_, ((O.data h₀).point_tendsto hO).comp h3, ((O.data h₀).metric_tendsto hO).comp h3⟩
  have hp : period (3 * m) = m := by simp [period]
  have hq : phase (3 * m) = 0 := by
    ext
    simp [phase, Nat.mul_mod_right]
  constructor
  · change LNormalizedOracle.physicalPoint μ (O.state (period (3 * m))) (phase (3 * m)) = _
    rw [hp, hq]
    rfl
  · change LNormalizedOracle.physicalMetric μ (O.state (period (3 * m))) (phase (3 * m)) = _
    rw [hp, hq]
    rfl

/-! ### A local accumulation embedding with positive lower curvature (lines 253-329)

Notation: $\mu=1/4096$ = `LEmbedding.mu`, $c_*$ = `LEmbedding.center`, $q_i$ = `LEmbedding.slope i`,
$b_i$ = `LEmbedding.parameter i`, $r=1/128$ = `LScalarGeometric.theta`, $a_n$ =
`LScalarGeometric.scale n`, $\vartheta_b$ = `LScalarRamp.center b`, $\epsilon$ =
`LScalarRamp.epsilon`, $P_b$ = `LScalarRamp.ramp b`, $J_b$ = `LScalarRamp.primitive b`,
$\varphi_b$ = `LScalar.phi b` (the article's $\psi_b$), $f_i$ = `LEmbedding.branch i`, $F$ =
`LEmbedding.objective`. The statements about $P_b$, $J_b$, $\varphi_b$ are made for the two values
$b=b_i$ (`b = LEmbedding.parameter i`). -/

/-- Item `C/13_L/prose/048` (`companion/chapters/13_L.tex:267`): "Define a monotone $C^1$ ramp
$P_b$ on $[0,1]$: it is zero for $\xi\le\vartheta_b-\epsilon$, one for
$\xi\ge\vartheta_b+\epsilon$, and on the intervening interval equals [display
`C/13_L/disp/028`]." For each of the values $b=b_i$. -/
theorem monotone_ramp (i : Fin 3) {b : ℝ} (hb : b = LEmbedding.parameter i) :
    Monotone (LScalarRamp.ramp b) ∧ ContDiff ℝ 1 (LScalarRamp.ramp b) ∧
      (∀ ξ, ξ ≤ LScalarRamp.center b - LScalarRamp.epsilon → LScalarRamp.ramp b ξ = 0) ∧
      (∀ ξ, LScalarRamp.center b + LScalarRamp.epsilon ≤ ξ → LScalarRamp.ramp b ξ = 1) ∧
      ∀ ξ t, LScalarRamp.center b - LScalarRamp.epsilon < ξ → ξ < LScalarRamp.center b + LScalarRamp.epsilon →
        t = (ξ - LScalarRamp.center b + LScalarRamp.epsilon) / (2 * LScalarRamp.epsilon) →
        LScalarRamp.ramp b ξ = 3 * t ^ 2 - 2 * t ^ 3 := by
  have hr := (BfgsCoverage.Article.LowerCurvature.ramp_def_bi i hb).1
  refine ⟨LScalarRamp.ramp_monotone b, LScalarRamp.ramp_contDiff b, fun ξ h => LScalarRamp.ramp_eq_zero h,
    fun ξ h => LScalarRamp.ramp_eq_one h, fun ξ t h1 h2 ht => ?_⟩
  rw [hr, BfgsCoverage.Article.LowerCurvature.cubicRamp, if_neg (not_le.mpr h1), if_neg (not_le.mpr h2), ht]

/-- Item `C/13_L/disp/029` (`companion/chapters/13_L.tex:272-274`), with line 271: "Let
$J_b(\xi)=\int_0^\xi P_b(v)\,dv$. The elementary formulas give
\[ \int_0^1P_b=1-\vartheta_b,\qquad 0\le P_b'\le768." \]
For each of the values $b=b_i$; $P_b'$ is the derivative of $P_b$. -/
theorem ramp_integral_bounds (i : Fin 3) {b : ℝ} (hb : b = LEmbedding.parameter i) :
    (∀ ξ, LScalarRamp.primitive b ξ = ∫ v in (0 : ℝ)..ξ, LScalarRamp.ramp b v) ∧
      (∫ ξ in (0 : ℝ)..1, LScalarRamp.ramp b ξ) = 1 - LScalarRamp.center b ∧
      ∀ ξ, 0 ≤ deriv (LScalarRamp.ramp b) ξ ∧ deriv (LScalarRamp.ramp b) ξ ≤ 768 := by
  obtain ⟨hl, hr⟩ := BfgsCoverage.Article.LowerCurvature.parameter_range hb
  exact ⟨LScalarRamp.primitive_eq_integral hl hr, LScalarRamp.integral_ramp hl hr,
    LScalarRamp.deriv_ramp_bounds b⟩

/-- Item `C/13_L/lemma/L:lem:scalar`, Lemma `L:lem:scalar` (`companion/chapters/13_L.tex:283-293`),
"Scalar regularity and exact affine neighborhoods", including its displays `C/13_L/disp/031`
(lines 285-287) and `C/13_L/disp/032` (equation `L:eq:plateau`, lines 289-291).

"Each $\varphi_b$ is convex, nonnegative, coercive, uniquely minimized at zero, and globally
$C^{1,1}$. It is $C^2$ on $(0,\infty)$ and on $(-\infty,0)$, but is not twice differentiable at
zero. At every node,
\[ \varphi_b(ba_n)=a_n^2,\quad \varphi_b'(ba_n)=a_n, \]
and
\[ \varphi_b(ba_n+h)=a_n^2+a_nh\qquad (|h|\le a_n/2). \]
Where its second derivative exists, $0\le\varphi_b''\le\max\{1,768/b\}$."

For each of the values $b=b_i$. Globally $C^{1,1}$: $C^1$ with a Lipschitz derivative; not twice
differentiable at zero: $\varphi_b'$ is not differentiable at zero; "where its second derivative
exists": wherever $\varphi_b'$ has a derivative $s$. -/
theorem scalar_lemma (i : Fin 3) {b : ℝ} (hb : b = LEmbedding.parameter i) :
    ConvexOn ℝ univ (LScalar.phi b) ∧ (∀ x, 0 ≤ LScalar.phi b x) ∧
      Tendsto (LScalar.phi b) (cocompact ℝ) atTop ∧
      (∀ x, LScalar.phi b 0 ≤ LScalar.phi b x) ∧ (∀ x, LScalar.phi b x = LScalar.phi b 0 → x = 0) ∧
      ContDiff ℝ 1 (LScalar.phi b) ∧ (∃ K, LipschitzWith K (deriv (LScalar.phi b))) ∧
      ContDiffOn ℝ 2 (LScalar.phi b) (Ioi 0) ∧ ContDiffOn ℝ 2 (LScalar.phi b) (Iio 0) ∧
      ¬ DifferentiableAt ℝ (deriv (LScalar.phi b)) 0 ∧
      (∀ n, LScalar.phi b (b * LScalarGeometric.scale n) = LScalarGeometric.scale n ^ 2 ∧
        HasDerivAt (LScalar.phi b) (LScalarGeometric.scale n) (b * LScalarGeometric.scale n)) ∧
      (∀ n h, |h| ≤ LScalarGeometric.scale n / 2 →
        LScalar.phi b (b * LScalarGeometric.scale n + h) =
          LScalarGeometric.scale n ^ 2 + LScalarGeometric.scale n * h) ∧
      ∀ x s, HasDerivAt (deriv (LScalar.phi b)) s x → 0 ≤ s ∧ s ≤ max 1 (768 / b) := by
  obtain ⟨hl, hr⟩ := BfgsCoverage.Article.LowerCurvature.parameter_range hb
  obtain ⟨hconv, hnn, hcoer, ⟨hmin, huniq⟩, hC1, hlip, hpos, hneg, hnot, hsec⟩ := lScalarRegularity b hl hr
  exact ⟨hconv, hnn, hcoer, hmin, huniq, hC1, hlip, fun x hx => (hpos x hx).contDiffWithinAt,
    fun x hx => (hneg x hx).contDiffWithinAt, hnot,
    fun n => ⟨LScalar.phi_node hl hr n, LScalar.phi_node_hasDerivAt hl hr n⟩,
    fun n h hh => LScalar.phi_plateau hl hr n hh, hsec⟩

/-- Item `C/13_L/prose/053` (`companion/chapters/13_L.tex:316`): "the first three Hessian upper
bounds are less than $439,446,27$, respectively, wherever those Hessians exist, and the fourth
has Hessian $\mu I$." For $i<3$, wherever $f_i$ is twice differentiable, $\nabla^2f_i\preceq L_iI$
with $L_i=\mu+(768/b_i)\|q_i\|^2$ (`LEmbedding.gradientBound i`, the gradient-Lipschitz constants
of the article), and $L_0<439$, $L_1<446$, $L_2<27$; $f_3$ is twice differentiable everywhere
with Hessian $\mu I$. -/
theorem branch_hessian_bounds :
    (LEmbedding.gradientBound 0 < 439 ∧ LEmbedding.gradientBound 1 < 446 ∧ LEmbedding.gradientBound 2 < 27) ∧
      (∀ (i : Fin 3) (x : Vec 2), DifferentiableAt ℝ (fderiv ℝ (LEmbedding.branch i.castSucc)) x →
        ∀ v, dot v ((RadialHessian.matrix (LEmbedding.branch i.castSucc) x).mulVec v) ≤
          LEmbedding.gradientBound i * sqNorm v) ∧
      ∀ x : Vec 2, DifferentiableAt ℝ (fderiv ℝ (LEmbedding.branch 3)) x ∧
        RadialHessian.matrix (LEmbedding.branch 3) x = LEmbedding.mu • (1 : Mat 2) := by
  refine ⟨⟨by simpa using LEmbedding.gradientBound_source 0, by simpa using LEmbedding.gradientBound_source 1,
      by simpa using LEmbedding.gradientBound_source 2⟩,
    fun i x hx v => ((LEmbedding.branch_old_actual_hessian_bounds i hx).2 v).2,
    fun x => ⟨(LEmbedding.branch_last_second_hasFDerivAt x).differentiableAt, LEmbedding.branch_last_hessian x⟩⟩

/-- Item `C/13_L/prose/055` (`companion/chapters/13_L.tex:316`): "Thus the maximum is
$\mu$-strongly convex." -/
theorem objective_strongly_convex :
    FixedNormal.EuclideanStrongConvexOn univ LEmbedding.mu LEmbedding.objective :=
  LEmbedding.objective_strongConvex

/-- Item `C/13_L/prose/057` (`companion/chapters/13_L.tex:322`): "consequently
$F'(0;h)=\max\{0,h_2\}$ and the minimizer is nonsmooth." The one-sided directional derivative at
zero ($h_2$ is `h 1`). -/
theorem directional_derivative :
    (∀ h : Vec 2, Tendsto (fun t : ℝ => (LEmbedding.objective (t • h) - LEmbedding.objective 0) / t)
      (𝓝[>] 0) (𝓝 (max 0 (h 1)))) ∧ ¬ DifferentiableAt ℝ LEmbedding.objective (0 : Vec 2) :=
  ⟨LEmbedding.objective_directional_derivative_zero, LEmbedding.objective_not_differentiable_zero⟩

/-! ### Copying one perturbed bad orbit at every scale (lines 343-381) -/

/-- Item `C/13_L/disp/038` (`companion/chapters/13_L.tex:346-350`), with line 345: "Set
$p_n=a_nc_*$ and $C_*=1+\mu\norm{c_*}^2/2$. For any $y$ with $|q_i\T y|\le1/2$,
\[ f_i(p_n+a_ny)=a_n^2\left\{\tfrac\mu2\norm{c_*+y}^2+1+q_i\T y\right\}
   =a_n^2\{C_*+g_i\T y+\tfrac\mu2\norm y^2\}." \]
For $i=0,1,2$ and every $n$; $p_n$ = `LEmbedding.copyCenter n`, $C_*$ = `LEmbedding.offset`. -/
theorem branch_copy_formula (n : ℕ) (i : Fin 3) (y : Vec 2) (hy : |dot (LEmbedding.slope i) y| ≤ 1/2) :
    LEmbedding.branch i.castSucc (LEmbedding.copyCenter n + LScalarGeometric.scale n • y) =
        LScalarGeometric.scale n ^ 2 *
          (LEmbedding.mu / 2 * sqNorm (LEmbedding.center + y) + 1 + dot (LEmbedding.slope i) y) ∧
      LScalarGeometric.scale n ^ 2 *
          (LEmbedding.mu / 2 * sqNorm (LEmbedding.center + y) + 1 + dot (LEmbedding.slope i) y) =
        LScalarGeometric.scale n ^ 2 *
          (LEmbedding.offset + dot (SeedOrbit.gradient seedC seedD i) y + LEmbedding.mu / 2 * sqNorm y) := by
  have hx : LEmbedding.copyPoint n y = LScalarGeometric.scale n • (LEmbedding.center + y) := by
    rw [smul_add]
    rfl
  constructor
  · change LQuadraticSeed.quadratic LEmbedding.mu (LEmbedding.copyPoint n y) +
        LEmbedding.residualBranch i.castSucc (LEmbedding.copyPoint n y) = _
    rw [LEmbedding.scalar_copy n i hy, hx, LQuadraticSeed.quadratic, RadialPower.sqNorm_smul]
    ring
  · have hq : LEmbedding.slope i = SeedOrbit.gradient seedC seedD i - LEmbedding.mu • LEmbedding.center := rfl
    rw [hq, LEmbedding.offset]
    simp only [sqNorm, dot, Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Item `C/13_L/prose/061` (`companion/chapters/13_L.tex:351`): "The fourth branch is negative
relative to its quadratic part there if $y$ is sufficiently small and $n\ge1$." For $y$ near zero
(in the fixed neighbourhood `LEmbedding.localDomain`) and $n\ge1$,
$f_3(p_n+a_ny)-\tfrac\mu2\|p_n+a_ny\|^2=(p_n+a_ny)_2<0$ (it holds for every $n$). -/
theorem fourth_branch_negative :
    ∀ᶠ y in 𝓝 (0 : Vec 2), ∀ n : ℕ, 1 ≤ n →
      LEmbedding.branch 3 (LEmbedding.copyCenter n + LScalarGeometric.scale n • y) -
        LEmbedding.mu / 2 * sqNorm (LEmbedding.copyCenter n + LScalarGeometric.scale n • y) < 0 := by
  filter_upwards [LEmbedding.localDomain_nhds] with y hy n _
  have h := LEmbedding.last_residual_copy_negative n hy
  change LQuadraticSeed.quadratic LEmbedding.mu (LEmbedding.copyPoint n y) +
    LEmbedding.residualBranch 3 (LEmbedding.copyPoint n y) - LEmbedding.mu / 2 * sqNorm (LEmbedding.copyPoint n y) < 0
  rw [LQuadraticSeed.quadratic]
  linarith

/-- Item `C/13_L/prose/066` (`companion/chapters/13_L.tex:369`): "At $p_n$ the three active
gradients are $a_ng_i$, so $0\notin\partial F(p_n)$. Meanwhile $x_0^{(n)}\to0$". At $p_n$ the
branches $f_0,f_1,f_2$ are active with gradients $a_ng_i$ and $f_3$ is inactive; the starts
$x_0^{(n)}=p_n+a_n\bar x_0$ (display `C/13_L/disp/040`, $\bar x_0$ = `LUniform.source.x 0`) tend
to zero. -/
theorem center_active_nonstationary :
    (∀ n : ℕ, (∀ i : Fin 3, LEmbedding.branch i.castSucc (LEmbedding.copyCenter n) =
        LEmbedding.objective (LEmbedding.copyCenter n) ∧
      coordinateGradient (LEmbedding.branch i.castSucc) (LEmbedding.copyCenter n) =
        LScalarGeometric.scale n • SeedOrbit.gradient seedC seedD i) ∧
      LEmbedding.branch 3 (LEmbedding.copyCenter n) < LEmbedding.objective (LEmbedding.copyCenter n) ∧
      (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential LEmbedding.objective (LEmbedding.copyCenter n)) ∧
    Tendsto (fun n => LEmbedding.copyCenter n + LScalarGeometric.scale n • LUniform.source.x 0) atTop (𝓝 0) := by
  refine ⟨fun n => ⟨(BfgsCoverage.Article.LowerCurvature.copy_limits n).2.2.2.2.2.1,
    (BfgsCoverage.Article.LowerCurvature.copy_limits n).2.2.2.2.2.2.1, LEmbedding.center_nonstationary n⟩,
    LEmbedding.copyPoint_tendsto (LUniform.source.x 0)⟩

/-- Item `C/13_L/disp/044` (`companion/chapters/13_L.tex:377-380`), with line 376: "The branch
strong-convexity and gradient-Lipschitz constants become, for example,
\[ \underline\mu=\mu\lambda_{\min}(\bar H_0)>0,\qquad \overline L=512\lambda_{\max}(\bar H_0)<\infty." \]
$\bar H_0$ = `LUniform.initialMetric`; the whitened branches $f_i(Az)$ (`LUniform.smoothBranch`) are
$\underline\mu$-strongly convex with $\overline L$-Lipschitz (Euclidean) gradients; $\overline L$ is
a real number. -/
theorem whitened_constants :
    LUniform.lowerConstant = LEmbedding.mu *
        AffineWhitening.minEigenvalue LUniform.initialMetric LUniform.initialMetric_posDef.1 ∧
      0 < LUniform.lowerConstant ∧
      LUniform.upperConstant = 512 *
        AffineWhitening.maxEigenvalue LUniform.initialMetric LUniform.initialMetric_posDef.1 ∧
      (∀ i, FixedNormal.EuclideanStrongConvexOn univ LUniform.lowerConstant (LUniform.smoothBranch i)) ∧
      ∀ i x y, ‖euclideanVector (coordinateGradient (LUniform.smoothBranch i) x -
        coordinateGradient (LUniform.smoothBranch i) y)‖ ≤ LUniform.upperConstant * ‖euclideanVector (x - y)‖ := by
  obtain ⟨h1, h2, -, h4, h5, -⟩ := BfgsCoverage.Article.LowerCurvature.whitening_constants
  exact ⟨h1, LUniform.lowerConstant_pos, h2, h4, h5⟩

/-! ### The literal Hessian condition permits an even simpler variant (lines 395-403)

The step scalar function is `LScalarStep.phi b` (step `LScalarStep.ramp b`, primitive
`LScalarStep.primitive b`), the step embedding `LStepEmbedding.objective` with branches
`LStepEmbedding.branch i` and nonsmooth part `LStepEmbedding.residual`. -/

/-- Item `C/13_L/prose/071` (`companion/chapters/13_L.tex:396`): "Replace the smooth ramp by the
step $P_b(\xi)=\mathbf1_{\{\xi>\vartheta_b\}}$ and its primitive by $J_b(\xi)=(\xi-\vartheta_b)_+$.
Use~\eqref{L:eq:scalar} on the positive intervals, the negative extension $\varphi_b(x)=-x$ for
$x<0$, and the same affine positive outer extension." For each of the values $b=b_i$ the library's
step function satisfies these equations (and $\varphi_b(0)=0$). -/
theorem step_scalar_def (i : Fin 3) {b : ℝ} (hb : b = LEmbedding.parameter i) :
    (∀ ξ, LScalarStep.ramp b ξ = if LScalarRamp.center b < ξ then 1 else 0) ∧
      (∀ ξ, LScalarStep.primitive b ξ = max 0 (ξ - LScalarRamp.center b)) ∧
      (∀ ξ, LScalarStep.primitive b ξ = ∫ v in (0 : ℝ)..ξ, LScalarStep.ramp b v) ∧
      (∀ (n : ℕ) (x ξ : ℝ), b * LScalarGeometric.scale (n + 1) ≤ x → x ≤ b * LScalarGeometric.scale n →
        ξ = (x / (b * LScalarGeometric.scale n) - LScalarGeometric.theta) / (1 - LScalarGeometric.theta) →
        LScalarStep.phi b x = (LScalarGeometric.theta * LScalarGeometric.scale n) ^ 2 +
          b * LScalarGeometric.scale n ^ 2 * (1 - LScalarGeometric.theta) *
            (LScalarGeometric.theta * ξ + (1 - LScalarGeometric.theta) * LScalarStep.primitive b ξ)) ∧
      LScalarStep.phi b 0 = 0 ∧ (∀ x, x < 0 → LScalarStep.phi b x = -x) ∧
      ∀ x, b ≤ x → LScalarStep.phi b x = 1 + x - b := by
  obtain ⟨hl, hr⟩ := BfgsCoverage.Article.LowerCurvature.parameter_range hb
  obtain ⟨hprim, h0, hneg, hout, hint⟩ := lScalarStepDefinition b hl hr
  refine ⟨fun ξ => rfl, fun ξ => rfl, hprim, fun n x ξ hlo hhi hξ => ?_, h0, hneg, hout⟩
  have hlo' : b * LScalarGeometric.theta * LScalarGeometric.scale n ≤ x := by
    rw [LScalarGeometric.scale_succ] at hlo
    linarith
  rw [hint n x hlo' hhi, hξ]
  rfl

/-- Item `C/13_L/prose/072` (`companion/chapters/13_L.tex:396`): "This scalar function is convex
and piecewise affine with countably many pieces; it has the same node values, node slopes, and
affine neighborhoods~\eqref{L:eq:plateau}." For each of the values $b=b_i$: convex; the maximum,
attained, of the countably many affine functions `LScalarStep.affineFamily b j`
($j\in$ `Option ℕ`); a maximum of at most two affine functions near every nonzero point; the node
values, slopes and plateaus of Lemma `L:lem:scalar`. -/
theorem step_scalar_props (i : Fin 3) {b : ℝ} (hb : b = LEmbedding.parameter i) :
    ConvexOn ℝ univ (LScalarStep.phi b) ∧ Countable (Option ℕ) ∧
      (∀ j, ∃ s c : ℝ, ∀ x, LScalarStep.affineFamily b j x = s * x + c) ∧
      (∀ x, IsGreatest (range (fun j => LScalarStep.affineFamily b j x)) (LScalarStep.phi b x)) ∧
      (∀ x, x ≠ 0 → LScalarStep.BinaryAffineGerm (LScalarStep.phi b) x) ∧
      ∀ n, LScalarStep.phi b (b * LScalarGeometric.scale n) = LScalarGeometric.scale n ^ 2 ∧
        HasDerivAt (LScalarStep.phi b) (LScalarGeometric.scale n) (b * LScalarGeometric.scale n) ∧
        ∀ h, |h| ≤ LScalarGeometric.scale n / 2 →
          LScalarStep.phi b (b * LScalarGeometric.scale n + h) =
            LScalarGeometric.scale n ^ 2 + LScalarGeometric.scale n * h := by
  obtain ⟨hl, hr⟩ := BfgsCoverage.Article.LowerCurvature.parameter_range hb
  obtain ⟨hconv, -, -, -, -, hmax⟩ := lScalarStepGeometry b hl hr
  obtain ⟨hbin, -, -⟩ := lScalarStepLocal b hl hr
  refine ⟨hconv, inferInstance, fun j => ?_, hmax, hbin, lScalarStepNodes b hl hr⟩
  cases j with
  | none => exact ⟨-1, 0, fun x => by simp [LScalarStep.affineFamily]⟩
  | some n => exact ⟨LScalarGeometric.scale n, (1 - b) * LScalarGeometric.scale n ^ 2,
      fun x => rfl⟩

/-- Item `C/13_L/prose/073` (`companion/chapters/13_L.tex:396`): "Thus the entire local-copy
construction and the same fixed initial matrix work unchanged." For every admissible pair and
every $n$: the local model $F(p_n+a_ny)=a_n^2\{C_*+Q_\mu(y)\}$ holds for the step embedding on a
fixed neighbourhood of zero (`LStepEmbedding.copyNeighborhood`, with
`LStepEmbedding.copyConstant` $=C_*$), and the copies of the same orbit (`LUniform.family` with
the step data) are runs of the implementation with $x_k^{(n)}=p_n+a_n\bar x_k$,
$H_k^{(n)}=\bar H_k$, the same initial matrix as the copies on the smooth embedding. -/
theorem step_copies (c₁ c₂ : ℝ) (h : LUniform.Admissible c₁ c₂) (n : ℕ) :
    LStepEmbedding.copyNeighborhood ∈ 𝓝 (0 : Vec 2) ∧
      (∀ y ∈ LStepEmbedding.copyNeighborhood, LStepEmbedding.objective (LStepEmbedding.copyPoint n y) =
        LScalarGeometric.scale n ^ 2 * (LStepEmbedding.copyConstant + LQuadraticSeed.objective LEmbedding.mu y)) ∧
      LStepEmbedding.copyConstant = LEmbedding.offset ∧
      (LUniform.family LActualCopies.stepData h n).H 0 = (LUniform.family LActualCopies.smoothData h n).H 0 ∧
      (∀ k, (LUniform.family LActualCopies.stepData h n).x k =
          LEmbedding.copyCenter n + LScalarGeometric.scale n • LUniform.source.x k ∧
        (LUniform.family LActualCopies.stepData h n).H k = LUniform.source.H k) ∧
      ∀ k N, 5 ≤ N → NonStrictLineSearch.fromMetric LStepEmbedding.objective
        ((LUniform.family LActualCopies.stepData h n).x k) ((LUniform.family LActualCopies.stepData h n).H k)
          c₁ c₂ N = (some ((LUniform.family LActualCopies.stepData h n).α k), trialHistory (phase k)) := by
  obtain ⟨hopen, hzero, -, hcopies⟩ := lStepEmbeddingCopies
  exact ⟨hopen.mem_nhds hzero, (hcopies n).1, rfl, rfl, fun k => ⟨rfl, rfl⟩,
    fun k N hN => BfgsCoverage.Article.LowerCurvature.fromMetric_fuel_mono
      (LUniform.copy_nonstrict_actual_search LActualCopies.stepData h n k) N hN⟩

/-- Item `C/13_L/prose/074` (`companion/chapters/13_L.tex:398`): "For this variant
$F=\mu\norm{x}^2/2+p(x)$, with convex countably piecewise-affine $p$." $p$ =
`LStepEmbedding.residual`: convex, the maximum, attained, of the countable family of affine
functions `LStepEmbedding.countableLinear j x + LStepEmbedding.countableOffset j`. -/
theorem step_objective_structure :
    (∀ x, LStepEmbedding.objective x = LEmbedding.mu / 2 * sqNorm x + LStepEmbedding.residual x) ∧
      ConvexOn ℝ univ LStepEmbedding.residual ∧ Countable LStepEmbedding.CountableIndex ∧
      ∀ x, IsGreatest (range fun j => LStepEmbedding.countableLinear j x + LStepEmbedding.countableOffset j)
        (LStepEmbedding.residual x) :=
  ⟨fun _ => rfl, LStepEmbedding.residual_convex, LStepEmbedding.countable_index,
    LStepEmbedding.residual_countable_max⟩

/-- Item `C/13_L/prose/075` (`companion/chapters/13_L.tex:398`): "At a nonzero point, any branch
with $q_i\T x=0$ is strictly below the maximum: its scalar value is zero, whereas at least one of
$q_0\T x,q_1\T x$ is nonzero and has positive scalar value. Here $q_0,q_1$ are independent." -/
theorem step_zero_argument_inactive :
    (∀ x : Vec 2, x ≠ 0 → ∀ i : Fin 3, dot (LEmbedding.slope i) x = 0 →
      LStepEmbedding.residualBranch i.castSucc x = 0 ∧
        LStepEmbedding.residualBranch i.castSucc x < LStepEmbedding.residual x) ∧
      (∀ x : Vec 2, x ≠ 0 →
        (dot (LEmbedding.slope 0) x ≠ 0 ∧ 0 < LScalarStep.phi (LEmbedding.parameter 0) (dot (LEmbedding.slope 0) x)) ∨
        (dot (LEmbedding.slope 1) x ≠ 0 ∧ 0 < LScalarStep.phi (LEmbedding.parameter 1) (dot (LEmbedding.slope 1) x))) ∧
      LinearIndependent ℝ ![LEmbedding.slope 0, LEmbedding.slope 1] := by
  have hb (i : Fin 3) := LEmbedding.parameter_bounds i
  refine ⟨fun x hx i hi => ?_, fun x hx => ?_, ?_⟩
  · have hz : LStepEmbedding.residualBranch i.castSucc x = 0 := by
      rw [LStepEmbedding.residualBranch_old, hi, LScalarStep.phi_zero (hb i).1.le (hb i).2.le]
    exact ⟨hz, hz ▸ LStepEmbedding.residual_positive_of_ne_zero hx⟩
  · by_cases h0 : dot (LEmbedding.slope 0) x = 0
    · have h1 : dot (LEmbedding.slope 1) x ≠ 0 := fun h1 => hx (LStepEmbedding.slope_pair_joint_kernel h0 h1)
      exact Or.inr ⟨h1, LScalarStep.phi_positive_of_ne_zero (hb 1).1.le (hb 1).2.le h1⟩
    · exact Or.inl ⟨h0, LScalarStep.phi_positive_of_ne_zero (hb 0).1.le (hb 0).2.le h0⟩
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    have e0 := congrFun hst 0
    have e1 := congrFun hst 1
    rw [LEmbedding.slope_first, LEmbedding.slope_second] at e0 e1
    simp at e0 e1
    constructor <;> linarith

/-- Item `C/13_L/prose/076` (`companion/chapters/13_L.tex:398`): "All potentially active scalar
arguments are therefore nonzero and encounter only finitely many breakpoints in a small
neighborhood. Hence $p$ is locally finite-polyhedral near every nonzero point. At any
differentiable such point it is locally affine. The origin is nonsmooth." At $x\ne0$ every active
ridge branch has $q_i^Tx\ne0$, and there the branch is, near $x$, a maximum of two affine
functions (at most one breakpoint); $p$ is near $x$ a finite maximum of affine functions
(`FiniteAffineLocal.PolyhedralGerm`); at a differentiable point of $F$, $p$ is affine near it
(`FiniteAffineLocal.AffineGerm`); $F$ is not differentiable at the origin. -/
theorem step_local_polyhedral :
    (∀ x : Vec 2, x ≠ 0 → ∀ i : Fin 3,
      i.castSucc ∈ ConvexSubdifferential.activeIndices LStepEmbedding.residual LStepEmbedding.residualBranch x →
      dot (LEmbedding.slope i) x ≠ 0) ∧
      (∀ (x : Vec 2) (i : Fin 3), dot (LEmbedding.slope i) x ≠ 0 →
        FiniteAffineLocal.BinaryAffineGerm (LStepEmbedding.residualBranch i.castSucc) x) ∧
      (∀ x : Vec 2, x ≠ 0 → FiniteAffineLocal.PolyhedralGerm LStepEmbedding.residual x) ∧
      (∀ x : Vec 2, DifferentiableAt ℝ LStepEmbedding.objective x →
        FiniteAffineLocal.AffineGerm LStepEmbedding.residual x) ∧
      ¬ DifferentiableAt ℝ LStepEmbedding.objective (0 : Vec 2) :=
  ⟨fun _ hx i hi => LStepEmbedding.active_scalar_argument_ne_zero hx i hi,
    fun _ i hi => LStepEmbedding.ridge_binary_affine i hi,
    fun _ hx => LStepEmbedding.residual_polyhedral_of_ne_zero hx,
    fun _ hd => LStepEmbedding.residual_affine_at_differentiable hd,
    LStepEmbedding.objective_not_differentiable_zero⟩

/-- Item `C/13_L/disp/045` (`companion/chapters/13_L.tex:399-402`), with line 398 ("Consequently"):
\[ \nabla^2F(x)=\mu I\quad\text{at every twice-differentiable point}. \]
For the step embedding $F$ (`LStepEmbedding.objective`). -/
theorem step_hessian_identity (x : Vec 2)
    (hfirst : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ LStepEmbedding.objective z)
    (_hsecond : DifferentiableAt ℝ (fderiv ℝ LStepEmbedding.objective) x) :
    RadialHessian.matrix LStepEmbedding.objective x = LEmbedding.mu • (1 : Mat 2) :=
  (LStepEmbedding.objective_actual_hessian hfirst.self_of_nhds).2

/-- Item `C/13_L/prose/077` (`companion/chapters/13_L.tex:403`): "After the fixed affine
transformation making $H_0=I$, that Hessian is the one fixed SPD matrix $\mu\bar H_0$." The
whitened step objective $\widetilde F(z)=F(Az)$ (`stepObjective`, $A$ = `LUniform.coordinateMatrix`,
$AA=\bar H_0$), whose runs start with $H_0=I$, has Hessian $\mu\bar H_0$ (positive definite) at
every twice-differentiable point. -/
theorem whitened_step_hessian :
    (∀ z, stepObjective z = LStepEmbedding.objective (LUniform.coordinateMatrix *ᵥ z)) ∧
      LUniform.coordinateMatrix * LUniform.coordinateMatrix = LUniform.initialMetric ∧
      (∀ (c₁ c₂ : ℝ) (h : LUniform.Admissible c₁ c₂) (n : ℕ),
        (LUniform.failureFamily LActualCopies.stepData h n).H 0 = 1) ∧
      (LEmbedding.mu • LUniform.initialMetric).PosDef ∧
      ∀ z, (∀ᶠ y in 𝓝 z, DifferentiableAt ℝ stepObjective y) → DifferentiableAt ℝ (fderiv ℝ stepObjective) z →
        RadialHessian.matrix stepObjective z = LEmbedding.mu • LUniform.initialMetric :=
  ⟨step_apply, LUniform.coordinateMatrix_square, fun _ _ h n => LUniform.failure_initial _ h n,
    stepHessian_posDef, fun _ hf _ => (step_actual_hessian hf.self_of_nhds).2⟩

/-! ### Non-vacuity -/

/-- The standing assumptions of this file can hold at once: an admissible pair exists;
$\mu=1/4096>0$; a return-map orbit converging to $P_*$ along which every admissible pair makes
the same decisions exists (`LUniform.source`); the Jacobian matrix $J$ of the shape map exists;
the root box is nonempty; matrices and points with the defining equations of display
`C/13_L/disp/010` exist; every neighbourhood of $P_*$ contains a state with $\tau>0$; $y=0$
satisfies $|q_i^Ty|\le1/2$; and $Q_\mu$ is a function. -/
example : (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ 1/3 ∧ c₁ < c₂ ∧ c₂ < 1 ∧ LUniform.Admissible c₁ c₂) ∧
    (0 : ℝ) < LEmbedding.mu ∧
    (∃ O : LUniform.Orbit LEmbedding.mu, Tendsto O.state atTop (𝓝 LNormalizedReturn.seed)) ∧
    (∃ J : Mat 2, ∀ i j, J i j =
      fderiv ℝ (LShapeDerivative.shapeMap seedC seedD) ![0, 1] (Pi.single j 1) i) ∧
    (∃ x : Vec 2, ‖x - AlgebraicSeed.center‖ ≤ 1 / 10 ^ 30) ∧
    (∃ (M : Fin 4 → Mat 2) (z : Fin 4 → Vec 2), M 0 = 1 ∧
      (∀ j : Fin 3, M j.succ = BfgsCoverage.Article.Failure.fullUpdate (M j.castSucc)
        (BfgsCoverage.Article.Failure.seedSlope j.castSucc)
        (BfgsCoverage.Article.Failure.seedSlope j.succ) (SeedOrbit.length j)) ∧
      z 0 = SeedOrbit.point seedC seedD seedRatio 0 ∧
      ∀ j : Fin 3, z j.succ = z j.castSucc -
        SeedOrbit.length j • (M j.castSucc *ᵥ BfgsCoverage.Article.Failure.seedSlope j.castSucc)) ∧
    (∀ N ∈ 𝓝 LNormalizedReturn.seed, ∃ w ∈ N, 0 < LNormalizedReturn.scale w) ∧
    (∀ i : Fin 3, |dot (LEmbedding.slope i) (0 : Vec 2)| ≤ 1/2) ∧
    ∃ Q : Vec 2 → ℝ, ∀ x, Q x = LEmbedding.mu / 2 * sqNorm x +
      max (max (dot (SeedOrbit.gradient seedC seedD 0) x) (dot (SeedOrbit.gradient seedC seedD 1) x))
        (dot (SeedOrbit.gradient seedC seedD 2) x) := by
  set M1 := BfgsCoverage.Article.Failure.fullUpdate 1 g0 g1 1
  set M2 := BfgsCoverage.Article.Failure.fullUpdate M1 g1 (g2 seedC seedD) (1/4)
  set M3 := BfgsCoverage.Article.Failure.fullUpdate M2 (g2 seedC seedD) g0 (1/16)
  set M : Fin 4 → Mat 2 := ![1, M1, M2, M3]
  set z0 := SeedOrbit.point seedC seedD seedRatio 0
  set z1 := z0 - (1 : ℝ) • ((1 : Mat 2) *ᵥ g0)
  set z2 := z1 - (1/4 : ℝ) • (M1 *ᵥ g1)
  set z3 := z2 - (1/16 : ℝ) • (M2 *ᵥ g2 seedC seedD)
  refine ⟨⟨1/10000, 1/2, by norm_num, by norm_num, by norm_num, by norm_num, LUniform.sourcePair⟩,
    LEmbedding.mu_pos, ⟨LUniform.source, LUniform.source_spec.1⟩,
    ⟨fun i j => fderiv ℝ (LShapeDerivative.shapeMap seedC seedD) ![0, 1] (Pi.single j 1) i,
      fun _ _ => rfl⟩, ⟨AlgebraicSeed.center, by simp⟩,
    ⟨M, ![z0, z1, z2, z3], rfl, fun j => ?_, rfl, fun j => ?_⟩, fun N hN => ?_,
    fun i => by simp [dot], ⟨_, fun _ => rfl⟩⟩
  · fin_cases j <;> rfl
  · fin_cases j <;> rfl
  · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hN
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

/-! #### Twice-differentiable points -/

/-- A convex function with `f 0 = 0` and `f b = 1` lies below its chord on `[0,b]`. -/
theorem convex_chord {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) {b t : ℝ} (hb : 0 < b) (ht0 : 0 ≤ t)
    (htb : t ≤ b) (h0 : f 0 = 0) (h1 : f b = 1) : f t ≤ t / b := by
  have hs0 : 0 ≤ t / b := div_nonneg ht0 hb.le
  have hs1 : 0 ≤ 1 - t / b := by rw [sub_nonneg, div_le_one hb]; exact htb
  have h := hf.2 (mem_univ (0 : ℝ)) (mem_univ b) hs1 hs0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, h0, h1, mul_one] at h
  have he : t / b * b = t := by field_simp
  rw [he] at h
  exact h

/-- The scalar arguments at `x₀ = (0,1)`. -/
theorem slope_dot_e2 :
    dot (LEmbedding.slope 0) ![0, 1] = 1/128 ∧ dot (LEmbedding.slope 1) ![0, 1] = -15/128 ∧
      dot (LEmbedding.slope 2) ![0, 1] = seedD + 1/128 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [LEmbedding.slope_first]; simp [dot, Fin.sum_univ_two]
  · rw [LEmbedding.slope_second]; simp [dot, Fin.sum_univ_two]
  · rw [LEmbedding.slope_third]; simp [dot, Fin.sum_univ_two]

/-- $x\mapsto v^Tx$ is continuous. -/
theorem dot_continuous (v : Vec 2) : Continuous (fun x : Vec 2 => dot v x) :=
  (gradientFunctional v).continuous.congr (fun x => gradientFunctional_apply v x)

/-- Near `x₀ = (0,1)` the fourth branch strictly dominates the four-branch embedding. -/
theorem smooth_eq_last_near_e2 :
    LEmbedding.objective =ᶠ[𝓝 (![0, 1] : Vec 2)] LEmbedding.branch 3 := by
  obtain ⟨d0, d1, d2⟩ := slope_dot_e2
  obtain ⟨-, -, hd1, hd2⟩ := BfgsCoverage.Article.Failure.seed_coarse_bounds
  have hb (i : Fin 3) := LEmbedding.parameter_bounds i
  have hgap (k : Fin 3) : LEmbedding.branch k.castSucc ![0, 1] < LEmbedding.branch 3 ![0, 1] := by
    change LQuadraticSeed.quadratic LEmbedding.mu _ + LEmbedding.residualBranch k.castSucc _ <
      LQuadraticSeed.quadratic LEmbedding.mu _ + LEmbedding.residualBranch 3 _
    rw [LEmbedding.residualBranch_old, LEmbedding.residualBranch_last]
    simp only [Matrix.cons_val_one, Matrix.head_cons, add_lt_add_iff_left]
    fin_cases k
    · change LScalar.phi (LEmbedding.parameter 0) (dot (LEmbedding.slope 0) ![0, 1]) < 1
      rw [d0]
      have h := convex_chord (b := LEmbedding.parameter 0) (t := 1/128)
        (LScalar.phi_convex (hb 0).1.le (hb 0).2.le) (by linarith [(hb 0).1])
        (by norm_num) (by linarith [(hb 0).1]) (LScalar.phi_zero (hb 0).1.le (hb 0).2.le)
        (by rw [LScalar.phi_eq_outer (hb 0).1.le (hb 0).2.le le_rfl]; ring)
      have : (1/128 : ℝ) / LEmbedding.parameter 0 < 1 := by
        rw [div_lt_one (by linarith [(hb 0).1])]; linarith [(hb 0).1]
      linarith
    · change LScalar.phi (LEmbedding.parameter 1) (dot (LEmbedding.slope 1) ![0, 1]) < 1
      rw [d1, LScalar.phi_eq_negative (hb 1).1.le (hb 1).2.le (by norm_num)]
      norm_num
    · change LScalar.phi (LEmbedding.parameter 2) (dot (LEmbedding.slope 2) ![0, 1]) < 1
      rw [d2, LScalar.phi_eq_negative (hb 2).1.le (hb 2).2.le (by norm_num at hd2 ⊢; linarith)]
      norm_num at hd1 hd2 ⊢
      nlinarith
  have hcont (k : Fin 4) : Continuous (LEmbedding.branch k) := (LEmbedding.branch_contDiff k).continuous
  have hev (k : Fin 3) : ∀ᶠ x in 𝓝 (![0, 1] : Vec 2), LEmbedding.branch k.castSucc x < LEmbedding.branch 3 x :=
    ((hcont k.castSucc).continuousAt.prodMk (hcont 3).continuousAt).eventually
      (isOpen_lt continuous_fst continuous_snd |>.mem_nhds (hgap k))
  filter_upwards [hev 0, hev 1, hev 2] with x h0 h1 h2
  apply le_antisymm
  · apply LEmbedding.objective_le
    intro i
    fin_cases i
    · exact h0.le
    · exact h1.le
    · exact h2.le
    · exact le_rfl
  · exact LEmbedding.branch_le 3 x

/-- $x\mapsto\mu\|x\|^2/2$ is continuous. -/
theorem quadratic_continuous : Continuous (LQuadraticSeed.quadratic LEmbedding.mu) :=
  continuous_iff_continuousAt.2 fun x => (LQuadraticSeed.quadratic_hasGradient _ x).continuousAt

/-- The branches of the step embedding are continuous. -/
theorem step_branch_continuous (k : Fin 4) : Continuous (LStepEmbedding.branch k) := by
  have hb (i : Fin 3) := LEmbedding.parameter_bounds i
  have hr : Continuous (LStepEmbedding.residualBranch k) := by
    refine Fin.lastCases ?_ (fun i => ?_) k
    · exact continuous_apply 1
    · rw [show LStepEmbedding.residualBranch i.castSucc =
          fun x => LScalarStep.phi (LEmbedding.parameter i) (dot (LEmbedding.slope i) x) from
          funext (LStepEmbedding.residualBranch_old i)]
      exact (LScalarStep.phi_continuous (hb i).1.le (hb i).2.le).comp (dot_continuous _)
  exact quadratic_continuous.add hr

/-- Near `x₀ = (0,1)` the third ridge branch strictly dominates the step embedding, on its
affine side: there `F(x) = μ‖x‖²/2 - q₂ᵀx`. -/
theorem step_eq_near_e2 : LStepEmbedding.objective =ᶠ[𝓝 (![0, 1] : Vec 2)]
    fun x => LQuadraticSeed.quadratic LEmbedding.mu x - dot (LEmbedding.slope 2) x := by
  obtain ⟨d0, d1, d2⟩ := slope_dot_e2
  obtain ⟨-, -, hd1, hd2⟩ := BfgsCoverage.Article.Failure.seed_coarse_bounds
  norm_num at hd1 hd2
  have hb (i : Fin 3) := LEmbedding.parameter_bounds i
  have h2val : LStepEmbedding.residualBranch (2 : Fin 3).castSucc ![0, 1] = -(seedD + 1/128) := by
    rw [LStepEmbedding.residualBranch_old, d2,
      LScalarStep.phi_eq_negative (hb 2).1.le (hb 2).2.le (by linarith)]
  have hgap (k : Fin 4) (hk : k ≠ 2) :
      LStepEmbedding.branch k ![0, 1] < LStepEmbedding.branch 2 ![0, 1] := by
    change LQuadraticSeed.quadratic LEmbedding.mu _ + LStepEmbedding.residualBranch k _ <
      LQuadraticSeed.quadratic LEmbedding.mu _ + LStepEmbedding.residualBranch (2 : Fin 3).castSucc _
    rw [h2val, add_lt_add_iff_left]
    fin_cases k
    · change LStepEmbedding.residualBranch (0 : Fin 3).castSucc ![0, 1] < _
      rw [LStepEmbedding.residualBranch_old, d0]
      have h := convex_chord (b := LEmbedding.parameter 0) (t := 1/128)
        (LScalarStep.phi_convex (hb 0).1.le (hb 0).2.le) (by linarith [(hb 0).1])
        (by norm_num) (by linarith [(hb 0).1]) (LScalarStep.phi_zero (hb 0).1.le (hb 0).2.le)
        (by rw [LScalarStep.phi_eq_outer (hb 0).1.le (hb 0).2.le le_rfl]; ring)
      have : (1/128 : ℝ) / LEmbedding.parameter 0 < 1 := by
        rw [div_lt_one (by linarith [(hb 0).1])]; linarith [(hb 0).1]
      linarith
    · change LStepEmbedding.residualBranch (1 : Fin 3).castSucc ![0, 1] < _
      rw [LStepEmbedding.residualBranch_old, d1,
        LScalarStep.phi_eq_negative (hb 1).1.le (hb 1).2.le (by norm_num)]
      linarith
    · exact absurd rfl hk
    · change (![0, 1] : Vec 2) 1 < _
      rw [show (![0, 1] : Vec 2) 1 = 1 from rfl]
      linarith
  have hev (k : Fin 4) (hk : k ≠ 2) :
      ∀ᶠ x in 𝓝 (![0, 1] : Vec 2), LStepEmbedding.branch k x < LStepEmbedding.branch 2 x :=
    ((step_branch_continuous k).continuousAt.prodMk (step_branch_continuous 2).continuousAt).eventually
      (isOpen_lt continuous_fst continuous_snd |>.mem_nhds (hgap k hk))
  have hneg : ∀ᶠ x in 𝓝 (![0, 1] : Vec 2), dot (LEmbedding.slope 2) x < 0 :=
    (dot_continuous _).continuousAt.eventually (gt_mem_nhds (by
      show dot (LEmbedding.slope 2) ![0, 1] < 0
      rw [d2]
      linarith))
  filter_upwards [hev 0 (by decide), hev 1 (by decide), hev 3 (by decide), hneg] with x h0 h1 h3 hx
  have heq : LStepEmbedding.objective x = LStepEmbedding.branch 2 x := by
    apply le_antisymm
    · apply LStepEmbedding.objective_le
      intro i
      fin_cases i
      · exact h0.le
      · exact h1.le
      · exact le_rfl
      · exact h3.le
    · exact LStepEmbedding.branch_le 2 x
  rw [heq]
  change LQuadraticSeed.quadratic LEmbedding.mu x + LStepEmbedding.residualBranch (2 : Fin 3).castSucc x = _
  rw [LStepEmbedding.residualBranch_old, LScalarStep.phi_eq_negative (hb 2).1.le (hb 2).2.le hx.le]
  ring

/-- A function that agrees near `x₀` with a function differentiable everywhere is differentiable
at every point near `x₀`. -/
theorem eventually_differentiable_of_eventuallyEq {f g : Vec 2 → ℝ} {x₀ : Vec 2}
    (h : f =ᶠ[𝓝 x₀] g) (hg : ∀ x, DifferentiableAt ℝ g x) :
    ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ f x := by
  filter_upwards [h.eventually_nhds] with x hx
  exact (hg x).congr_of_eventuallyEq hx

/-- Twice differentiability at `point A x₀` of `F(A·)` from twice differentiability of `F` at
`x₀`. -/
theorem whitened_twice {F : Vec 2 → ℝ} {x₀ : Vec 2}
    (h1 : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ F x) (h2 : DifferentiableAt ℝ (fderiv ℝ F) x₀) :
    (∀ᶠ z in 𝓝 (AffineWhitening.point LUniform.coordinateMatrix x₀),
        DifferentiableAt ℝ (AffineWhitening.objective LUniform.coordinateMatrix F) z) ∧
      DifferentiableAt ℝ (fderiv ℝ (AffineWhitening.objective LUniform.coordinateMatrix F))
        (AffineWhitening.point LUniform.coordinateMatrix x₀) := by
  have hA := LUniform.coordinateMatrix_invertible
  have hmap := AffineWhitening.map_point LUniform.coordinateMatrix hA x₀
  have ht : Tendsto (fun z => LUniform.coordinateMatrix *ᵥ z)
      (𝓝 (AffineWhitening.point LUniform.coordinateMatrix x₀)) (𝓝 x₀) := by
    have hc := (AffineProjection.matrixCLM LUniform.coordinateMatrix).continuous.tendsto
      (AffineWhitening.point LUniform.coordinateMatrix x₀)
    simpa only [AffineProjection.matrixCLM_apply, hmap] using hc
  refine ⟨?_, ?_⟩
  · filter_upwards [ht h1] with z hz
    exact hz.comp z (AffineProjection.matrixCLM LUniform.coordinateMatrix).differentiableAt
  · rw [AffineWhitening.second_differentiableAt_iff LUniform.coordinateMatrix hA, hmap]
    exact h2

/-- $x\mapsto v^Tx$ is differentiable. -/
theorem dot_differentiable (v x : Vec 2) : DifferentiableAt ℝ (fun y : Vec 2 => dot v y) x :=
  ((gradientFunctional v).differentiableAt).congr_of_eventuallyEq
    (Eventually.of_forall fun y => (gradientFunctional_apply v y).symm)

/-- The ridge branches $f_0,f_1,f_2$ are twice differentiable at $c_*$, where $q_i^Tc_*=b_i>0$
(there $\varphi_{b_i}$ is $C^2$). -/
theorem branch_twice_at_center (i : Fin 3) :
    DifferentiableAt ℝ (fderiv ℝ (LEmbedding.branch i.castSucc)) LEmbedding.center := by
  have hb := LEmbedding.parameter_bounds i
  have he : LEmbedding.branch i.castSucc =
      fun x => LQuadraticSeed.quadratic LEmbedding.mu x +
        LScalar.phi (LEmbedding.parameter i) (dot (LEmbedding.slope i) x) := by
    funext x
    change LQuadraticSeed.quadratic LEmbedding.mu x + LEmbedding.residualBranch i.castSucc x = _
    rw [LEmbedding.residualBranch_old]
  have hq : ContDiff ℝ 2 (LQuadraticSeed.quadratic LEmbedding.mu) := by
    unfold LQuadraticSeed.quadratic sqNorm
    simp only [Fin.sum_univ_two]
    fun_prop
  have hd : ContDiff ℝ 2 (fun x : Vec 2 => dot (LEmbedding.slope i) x) := by
    unfold dot
    simp only [Fin.sum_univ_two]
    fun_prop
  have hphi : ContDiffAt ℝ 2 (LScalar.phi (LEmbedding.parameter i))
      (dot (LEmbedding.slope i) LEmbedding.center) :=
    LScalar.phi_contDiffAt_pos hb.1.le hb.2.le (by
      change 0 < LEmbedding.parameter i
      linarith [hb.1])
  have hc : ContDiffAt ℝ 2 (LEmbedding.branch i.castSucc) LEmbedding.center := by
    rw [he]
    exact hq.contDiffAt.add (hphi.comp LEmbedding.center hd.contDiffAt)
  exact (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

/-- The clauses "at every twice-differentiable point" are not vacuous: twice-differentiable points
(differentiable nearby, with a differentiable derivative map at the point) exist for the
four-branch objective $F$ and the step embedding at $x_0=(0,1)$ (where a single branch strictly
dominates: the fourth, resp. the third ridge branch on its affine side), for their whitened versions
`LUniform.smoothObjective` and `stepObjective` (the witnesses `F₁`, `F₂` in the proof of
`local_failure`) at $A^{-1}x_0$,
and for the ridge branches $f_0,f_1,f_2$ at $c_*$ (hypotheses of `local_failure`,
`step_hessian_identity`, `whitened_step_hessian`, `branch_hessian_bounds`). -/
example : (∃ z : Vec 2, (∀ᶠ y in 𝓝 z, DifferentiableAt ℝ LUniform.smoothObjective y) ∧
      DifferentiableAt ℝ (fderiv ℝ LUniform.smoothObjective) z) ∧
    (∃ z : Vec 2, (∀ᶠ y in 𝓝 z, DifferentiableAt ℝ stepObjective y) ∧
      DifferentiableAt ℝ (fderiv ℝ stepObjective) z) ∧
    (∃ x : Vec 2, (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ LEmbedding.objective y) ∧
      DifferentiableAt ℝ (fderiv ℝ LEmbedding.objective) x) ∧
    (∃ x : Vec 2, (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ LStepEmbedding.objective y) ∧
      DifferentiableAt ℝ (fderiv ℝ LStepEmbedding.objective) x) ∧
    ∀ i : Fin 3, ∃ x : Vec 2, DifferentiableAt ℝ (fderiv ℝ (LEmbedding.branch i.castSucc)) x := by
  have hs1 : ∀ᶠ y in 𝓝 (![0, 1] : Vec 2), DifferentiableAt ℝ LEmbedding.objective y :=
    eventually_differentiable_of_eventuallyEq smooth_eq_last_near_e2
      (fun y => (LEmbedding.branch_hasGradient 3 y).differentiableAt)
  have hs2 : DifferentiableAt ℝ (fderiv ℝ LEmbedding.objective) ![0, 1] :=
    (LEmbedding.branch_last_second_hasFDerivAt _).differentiableAt.congr_of_eventuallyEq
      smooth_eq_last_near_e2.fderiv
  have ht1 : ∀ᶠ y in 𝓝 (![0, 1] : Vec 2), DifferentiableAt ℝ LStepEmbedding.objective y :=
    eventually_differentiable_of_eventuallyEq step_eq_near_e2
      (fun y => (LQuadraticSeed.quadratic_hasGradient _ y).differentiableAt.sub (dot_differentiable _ y))
  have ht2 : DifferentiableAt ℝ (fderiv ℝ LStepEmbedding.objective) ![0, 1] :=
    (LStepEmbedding.objective_actual_hessian ht1.self_of_nhds).1.differentiableAt
  exact ⟨⟨_, whitened_twice hs1 hs2⟩, ⟨_, whitened_twice ht1 ht2⟩, ⟨_, hs1, hs2⟩, ⟨_, ht1, ht2⟩,
    fun i => ⟨_, branch_twice_at_center i⟩⟩

end BfgsCoverage.Companion.Ch13L
