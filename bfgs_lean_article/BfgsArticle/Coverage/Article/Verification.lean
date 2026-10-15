import BfgsArticle.LUniformLocal
import BfgsArticle.LNonStrictGlobal
import BfgsArticle.HomogeneousModels
import BfgsVerification.UnexcitedMetric
import BfgsVerification.DEmbeddingTarget
import BfgsVerification.AlgebraicSeedCoercive
import BfgsVerification.ConvexCellRadial
import BfgsVerification.LEmbeddingSourceDetails
import BfgsVerification.PointwiseCertificateFeasibility

/-!
# Lean coverage of `paper/sections/verification.tex`

Coverage theorems for the claims made only in Section `art:verification`
("Synthesis, verification and the remaining questions"), and the open question
stated there. Register: `editorial/lean_coverage/register/A_verification.json`.

Objects. `G(z)=max_i g_i^T z` is `SeedOrbit.objective seedC seedD` and its coercive
cap `Ḡ` of Corollary `art:failure_polyhedral` is `SeedOrbit.coerciveObjective`.
The objective `art:upper_objective` of Theorem `art:local-failure` is
`DEmbedding.objective` with branches `DEmbedding.branch`; the objective
`art:lower_objective` before whitening is `LEmbedding.objective` with branches
`LEmbedding.branch`; the whitened objective `F(Az)` of Theorem
`art:local-failure-lower` is `LUniform.smoothObjective`, with branches
`LUniform.smoothBranch` and `A = LUniform.coordinateMatrix`. The perturbed seed
objective `Q_μ(x)=μ‖x‖^2/2+G(x)` is `LQuadraticSeed.objective μ`.
-/

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsCoverage.Article.Verification
open BfgsVerification

/-! ## The homogeneous seed and its coercive cap -/

/-- Item `A/verification/prose/004` (`paper/sections/verification.tex:11-12`): "The homogeneous
seed satisfies $G(t(-1,16))=-t$ for $t\ge0$" (the range was added on 15 October 2026, M9), as
stated in `paper/sections/failure.tex:201`. -/
theorem seed_ray {t : ℝ} (ht : 0 ≤ t) :
    SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD (t • ![-1, 16]) = -t :=
  DEmbedding.seed_descent_ray ht

/-- Item `A/verification/prose/004` (`paper/sections/verification.tex:11-12`),
the range is needed (the reading of the text before M9, for every real `t`): at `t=-1`,
`G(t(-1,16)) = G(1,-16) ≥ c_∘-16d_∘ > 1 = -t`. -/
theorem seed_ray_fails_at_minus_one :
    SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD ((-1 : ℝ) • ![-1, 16]) ≠ -(-1 : ℝ) := by
  intro h
  have hb := (SeedOrbit.family SeedOrbit.seedC SeedOrbit.seedD).branch_le 2 ((-1 : ℝ) • ![-1, 16])
  obtain ⟨⟨hc0, _⟩, ⟨_, hd1⟩⟩ := SeedOrbit.root_tight_box
  change _ ≤ SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD _ at hb
  rw [h] at hb
  simp only [MaxAffine.Family.branch, SeedOrbit.family, SeedOrbit.gradient, SeedCycle.g2, dot,
    Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, add_zero] at hb
  change _ ≤ _ at hb
  dsimp only [SeedOrbit.seedC, SeedOrbit.seedD] at hb
  linarith

/-- Item `A/verification/prose/005` (`paper/sections/verification.tex:11-12`): "... so it is
unbounded below". -/
theorem seed_unbounded_below (M : ℝ) :
    ∃ x : Vec 2, SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD x < M := by
  refine ⟨(|M| + 1) • ![-1, 16], ?_⟩
  rw [seed_ray (by positivity)]
  linarith [neg_abs_le M]

/-- The cap `Ḡ(u,v)=max{u,-u-v/8,c_∘u+d_∘v,v-17}` of Corollary
`art:failure_polyhedral`, as a formula. -/
theorem cap_formula (x : Vec 2) :
    SeedOrbit.coerciveObjective x =
      max (max (x 0) (-x 0 - x 1 / 8)) (max (SeedOrbit.seedC * x 0 + SeedOrbit.seedD * x 1) (x 1 - 17)) := by
  have hb : ∀ i : Fin 4, SeedOrbit.coerciveFamily.branch i x =
      (![x 0, -x 0 - x 1 / 8, SeedOrbit.seedC * x 0 + SeedOrbit.seedD * x 1, x 1 - 17] : Fin 4 → ℝ) i := by
    intro i
    fin_cases i <;>
      simp [MaxAffine.Family.branch, SeedOrbit.coerciveFamily, dot, Fin.sum_univ_two,
        SeedCycle.g0, SeedCycle.g1, SeedCycle.g2] <;> ring
  have hle : ∀ i, SeedOrbit.coerciveFamily.branch i x ≤ SeedOrbit.coerciveObjective x :=
    fun i => SeedOrbit.coerciveFamily.branch_le i x
  obtain ⟨i, hi⟩ := SeedOrbit.coerciveFamily.exists_active x
  apply le_antisymm
  · change SeedOrbit.coerciveFamily.objective x ≤ _
    rw [← hi, hb i]
    fin_cases i
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  · have h0 := hle 0
    have h1 := hle 1
    have h2 := hle 2
    have h3 := hle 3
    rw [hb] at h0 h1 h2 h3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.cons_val_three] at h0 h1 h2 h3
    exact max_le (max_le h0 h1) (max_le h2 h3)

/-- Item `A/verification/prose/006` (`paper/sections/verification.tex:13`): "its coercive
cap contains the affine term $v-17$ and is not homogeneous." -/
theorem cap_not_homogeneous :
    (∀ x : Vec 2, SeedOrbit.coerciveObjective x =
      max (max (x 0) (-x 0 - x 1 / 8)) (max (SeedOrbit.seedC * x 0 + SeedOrbit.seedD * x 1) (x 1 - 17))) ∧
      ¬ Homogeneous.PositiveDegreeOne SeedOrbit.coerciveObjective := by
  refine ⟨cap_formula, fun hh => ?_⟩
  have h2 := hh 2 (by norm_num) ![-1, 16]
  obtain ⟨⟨hc0, hc1⟩, ⟨hd0, hd1⟩⟩ := SeedOrbit.root_tight_box
  have hlow : (15 : ℝ) ≤ SeedOrbit.coerciveObjective ((2 : ℝ) • ![-1, 16]) := by
    rw [cap_formula]
    refine le_trans ?_ ((le_max_right _ _).trans (le_max_right _ _))
    norm_num
  have hup : SeedOrbit.coerciveObjective ![-1, 16] ≤ -1 := by
    rw [cap_formula]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    dsimp only [SeedOrbit.seedC, SeedOrbit.seedD]
    refine max_le (max_le (by norm_num) (by norm_num)) (max_le ?_ (by norm_num))
    linarith
  rw [h2] at hlow
  linarith

/-- Item `A/verification/prose/007` (`paper/sections/verification.tex:14-15`): "Neither
belongs to the coercive homogeneous class of
Theorem~\ref{art:homogeneous}." Neither `G` nor `Ḡ` is both positively homogeneous
of degree one and coercive (`F → ∞` along the cocompact filter), the hypotheses of
`AdmissibleBFGSRun.homogeneous_coercive_iterates_zero`. -/
theorem neither_coercive_homogeneous :
    ¬ (Homogeneous.PositiveDegreeOne (SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD) ∧
        Tendsto (SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD) (cocompact (Vec 2)) atTop) ∧
      ¬ (Homogeneous.PositiveDegreeOne SeedOrbit.coerciveObjective ∧
        Tendsto SeedOrbit.coerciveObjective (cocompact (Vec 2)) atTop) := by
  refine ⟨fun ⟨_, hc⟩ => ?_, fun ⟨hh, _⟩ => cap_not_homogeneous.2 hh⟩
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.mp (tendsto_atTop.mp hc 0)
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  have ht : (0 : ℝ) ≤ |R| + 1 := by positivity
  have hmem : (|R| + 1) • (![-1, 16] : Vec 2) ∈ K := by
    by_contra hn
    have h := hKs hn
    simp only [mem_setOf_eq] at h
    rw [seed_ray ht] at h
    linarith [abs_nonneg R]
  have hn := hR _ hmem
  have hco := norm_le_pi_norm ((|R| + 1) • (![-1, 16] : Vec 2)) 1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_zero, Real.norm_eq_abs] at hco
  rw [abs_of_nonneg (by positivity)] at hco
  linarith [le_abs_self R, abs_nonneg R]

/-! ## The local embeddings and finite polyhedral partitions -/

/-- A finite local polyhedral-cell partition around `star`, as in the hypotheses of
Theorem `art:polyhedral`: an open neighbourhood `U` of `star` covered by finitely
many closed full-dimensional polyhedra `P_i = {x | a_{ij}^T x ≤ b_{ij}}`, open sets
`V_i ⊇ U ∩ P_i` and functions `f_i ∈ C^{1,1}_loc(V_i)` with `F = f_i` on `U ∩ P_i`. -/
def HasLocalPolyhedralPartition {n : ℕ} (F : Vec n → ℝ) (star : Vec n) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (a : (i : ι) → Fin (m i) → Vec n)
    (b : (i : ι) → Fin (m i) → ℝ) (V : ι → Set (Vec n)) (f : ι → Vec n → ℝ) (U : Set (Vec n)),
    IsOpen U ∧ star ∈ U ∧
    (∀ x ∈ U, ∃ i, x ∈ ConvexCellRadial.polyhedron (a i) (b i)) ∧
    (∀ i, (interior (ConvexCellRadial.polyhedron (a i) (b i))).Nonempty) ∧
    (∀ i, IsOpen (V i) ∧ U ∩ ConvexCellRadial.polyhedron (a i) (b i) ⊆ V i ∧
      CenteredSmoothSublinear.LocallyC11On (V i) (f i)) ∧
    ∀ i, ∀ x ∈ U, x ∈ ConvexCellRadial.polyhedron (a i) (b i) → F x = f i x

/-- Admissible runs from starts tending to the unique minimizer that do not
converge to it exclude a finite local polyhedral-cell partition there (by
`ConvexCellRadial.finite_polyhedral_basin`, the Lean form of Theorem
`art:polyhedral`). -/
theorem no_partition_of_failing_runs {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    {star : Vec n} (hmin : ∀ x, F star ≤ F x) (huniq : ∀ x, F x = F star → x = star)
    (R : ℕ → AdmissibleBFGSRun n F) (hstart : Tendsto (fun ℓ => (R ℓ).x 0) atTop (𝓝 star))
    (hfail : ∀ ℓ, ¬ Tendsto (R ℓ).x atTop (𝓝 star)) :
    ¬ HasLocalPolyhedralPartition F star := by
  rintro ⟨ι, hι, m, a, b, V, f, U, hU, hsU, hcover, _, hV, heq⟩
  obtain ⟨δ, hδ, hbasin⟩ := ConvexCellRadial.finite_polyhedral_basin hF a b V f
    (fun i => (hV i).1) (fun i => (hV i).2.2) hU hsU (fun i => (hV i).2.1) hcover heq hmin huniq
  have hv : Tendsto (fun ℓ => F ((R ℓ).x 0)) atTop (𝓝 (F star)) :=
    ((convex_continuous hF).tendsto star).comp hstart
  obtain ⟨ℓ, hℓ⟩ := (hv.eventually (eventually_le_nhds (lt_add_of_pos_right (F star) hδ))).exists
  exact hfail ℓ (hbasin (R ℓ) hℓ).2.2

/-- Item `A/verification/prose/009` (`paper/sections/verification.tex:17-19`): "In the
local embeddings, ... the resulting switching geometry is not resolved by a finite
local polyhedral-cell partition as in Theorem~\ref{art:polyhedral}." Neither the
objective `art:upper_objective` of Theorem `art:local-failure` nor the objective of
Theorem `art:local-failure-lower` has such a partition around its minimizer `0`. -/
theorem local_embeddings_no_polyhedral_partition :
    ¬ HasLocalPolyhedralPartition DEmbedding.objective 0 ∧
      ¬ HasLocalPolyhedralPartition LUniform.smoothObjective 0 := by
  constructor
  · have hc₁ : (0 : ℝ) < 1 / 4 := by norm_num
    have hc₁' : (1 / 4 : ℝ) ≤ 1 / 3 := by norm_num
    have hc : (1 / 4 : ℝ) < 1 / 2 := by norm_num
    have hc₂ : (1 / 2 : ℝ) < 1 := by norm_num
    obtain ⟨hstart, -⟩ := DEmbedding.deterministic_embedding_failure
    obtain ⟨h0, hnn, hz⟩ := DEmbedding.objective_unique_minimum
    refine no_partition_of_failing_runs DEmbedding.objective_convex
      (fun x => h0 ▸ hnn x) (fun x hx => (hz x).mp (h0 ▸ hx))
      (fun ℓ => DEmbedding.run (n := ℓ + 1) (by omega) (1 / 4) (1 / 2) hc₁ hc₁' hc hc₂)
      (hstart.comp (tendsto_add_atTop_nat 1)) (fun ℓ h => ?_)
    exact DEmbedding.center_ne_zero (ℓ + 1)
      (tendsto_nhds_unique (DEmbedding.run_point_tendsto (n := ℓ + 1) (by omega) hc₁ hc₁' hc hc₂) h)
  · obtain ⟨x, H, g, -, hx0, hall⟩ :=
      LUniform.uniform_identity_failure LActualCopies.smoothData LEmbedding.objective_zero
    obtain ⟨R, hR, -⟩ := hall (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hnn : ∀ z, 0 ≤ LUniform.smoothObjective z := fun z =>
      le_trans (mul_nonneg (div_nonneg LUniform.lowerConstant_pos.le (by norm_num)) (sqNorm_nonneg z))
        (LUniform.smooth_lower z)
    have hmin : ∀ z, LUniform.smoothObjective 0 ≤ LUniform.smoothObjective z := fun z =>
      LUniform.smooth_zero ▸ hnn z
    refine no_partition_of_failing_runs LUniform.smooth_convex hmin
      (fun z hz => LUniform.smooth_unique_zero (LUniform.smooth_zero ▸ hz)) R ?_ (fun ℓ h => ?_)
    · simpa only [(hR _).1] using hx0
    · obtain ⟨-, -, hlim, -, -, -, hnon, -, -, -⟩ := (hR ℓ).2.2.2
      have hc := tendsto_nhds_unique hlim h
      refine hnon ?_
      rw [hc]
      intro z
      have h1 : dot (0 : Vec 2) (z - 0) = 0 := by simp [dot]
      have h2 := hnn z
      change dot 0 (z - 0) ≤ LUniform.smoothObjective z - LUniform.smoothObjective 0
      rw [h1, LUniform.smooth_zero]
      linarith

/-! ## Active gradients at the minimizer and the planar nondegeneracy -/

/-- The degenerate gradient pattern `0,0,0,e` with `e ≠ 0`: it is affinely
dependent, every combination equals `w_3 e`, which is nonzero when `w_3>0`, and no
strictly positive weights summing to one combine it to zero. -/
theorem degenerate_pattern {e : Vec 2} (he : e ≠ 0) :
    ¬ AffineIndependent ℝ (![0, 0, 0, e] : Fin 4 → Vec 2) ∧
      (∀ w : Fin 4 → ℝ, 0 < w 3 →
        ∑ i, w i • (![0, 0, 0, e] : Fin 4 → Vec 2) i = w 3 • e ∧ w 3 • e ≠ 0) ∧
      ¬ ∃ w : Fin 4 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
        ∑ i, w i • (![0, 0, 0, e] : Fin 4 → Vec 2) i = 0 := by
  have hsum : ∀ w : Fin 4 → ℝ, ∑ i, w i • (![0, 0, 0, e] : Fin 4 → Vec 2) i = w 3 • e := by
    intro w
    simp [Fin.sum_univ_four]
  have hne : ∀ w : Fin 4 → ℝ, 0 < w 3 → w 3 • e ≠ 0 := fun w hw =>
    smul_ne_zero hw.ne' he
  refine ⟨fun h => ?_, fun w hw => ⟨hsum w, hne w hw⟩, ?_⟩
  · have h01 := h.injective (a₁ := 0) (a₂ := 1) (by simp)
    exact absurd h01 (by decide)
  · rintro ⟨w, hw, -, hz⟩
    rw [hsum] at hz
    exact hne w (hw 3) hz

/-- Item `A/verification/prose/011` (`paper/sections/verification.tex:22-24`);
Item `A/verification/prose/014` (`paper/sections/verification.tex:28-29`);
Item `A/verification/prose/015` (`paper/sections/verification.tex:29-31`);
Item `A/verification/prose/016` (`paper/sections/verification.tex:31-32`):
"In \eqref{art:upper_objective}, all four branches are active at zero, with indexed
gradients $0,0,0,e_2$ ... the repeated zero gradients violate affine independence,
and a combination with positive weight $\lambda_3$ on the fourth branch equals
$\lambda_3e_2\ne0$ ... The strictly positive optimal weights in
Corollary~\ref{art:planar-max} therefore fail as well." -/
theorem upper_active_gradients :
    (∀ i, DEmbedding.branch i 0 = DEmbedding.objective 0) ∧
      (∀ i, HasFDerivAt (DEmbedding.branch i)
        (gradientFunctional ((![0, 0, 0, ![0, 1]] : Fin 4 → Vec 2) i)) 0) ∧
      ¬ AffineIndependent ℝ (![0, 0, 0, ![0, 1]] : Fin 4 → Vec 2) ∧
      (∀ w : Fin 4 → ℝ, 0 < w 3 →
        ∑ i, w i • (![0, 0, 0, ![0, 1]] : Fin 4 → Vec 2) i = w 3 • ![0, 1] ∧
          w 3 • (![0, 1] : Vec 2) ≠ 0) ∧
      ¬ ∃ w : Fin 4 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
        ∑ i, w i • (![0, 0, 0, ![0, 1]] : Fin 4 → Vec 2) i = 0 := by
  have he : (![0, 1] : Vec 2) ≠ 0 := fun h => by simpa using congrFun h 1
  have hold : ∀ i : Fin 3, HasFDerivAt (DEmbedding.branch i.castSucc) (gradientFunctional 0) 0 := by
    intro i
    have h := DEmbedding.branch_old_hasGradient i 0
    have hz : DEmbedding.ridgeGradient (DEmbedding.parameter i)
        (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i) 0 = 0 := by
      simp only [DEmbedding.ridgeGradient, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
        DEmbedding.phiFirst_zero (DEmbedding.parameter_bounds i).1 (DEmbedding.parameter_bounds i).2,
        zero_smul]
    rwa [hz] at h
  refine ⟨fun i => ?_, fun i => ?_, (degenerate_pattern he).1, (degenerate_pattern he).2.1,
    (degenerate_pattern he).2.2⟩
  · rw [DEmbedding.branch_zero, DEmbedding.objective_zero]
  · fin_cases i
    · exact hold 0
    · exact hold 1
    · exact hold 2
    · exact DEmbedding.branch_last_hasGradient 0

/-- The branch gradients of `art:lower_objective` at zero: `0,0,0,e_2`. -/
theorem lower_branch_gradients_zero (i : Fin 4) :
    LEmbedding.branchGradient i 0 = (![0, 0, 0, ![0, 1]] : Fin 4 → Vec 2) i := by
  fin_cases i
  · exact LEmbedding.branchGradient_zero 0
  · exact LEmbedding.branchGradient_zero 1
  · exact LEmbedding.branchGradient_zero 2
  · simp [LEmbedding.branchGradient, LEmbedding.residualGradient]

/-- Item `A/verification/prose/012` (`paper/sections/verification.tex:25-26`), with the
consequences of `A/verification/prose/014`–`016`: "Equation~\eqref{art:lower_objective}
gives the same pattern before whitening: the common quadratic has zero gradient at
zero, and $\psi_b'(0)=0$." All four branches
`f_i(x)=μ‖x‖^2/2+ψ_{b_i}(q_i^Tx)`, `f_3(x)=μ‖x‖^2/2+x_2` are active at zero with
gradients `0,0,0,e_2`; the gradient pattern has the same consequences as in
`upper_active_gradients`. -/
theorem lower_active_gradients :
    (∀ i, LEmbedding.branch i 0 = LEmbedding.objective 0) ∧
      HasFDerivAt (LQuadraticSeed.quadratic LEmbedding.mu) (gradientFunctional 0) 0 ∧
      (∀ i : Fin 3, HasDerivAt (LScalar.phi (LEmbedding.parameter i)) 0 0) ∧
      (∀ i, HasFDerivAt (LEmbedding.branch i)
        (gradientFunctional ((![0, 0, 0, ![0, 1]] : Fin 4 → Vec 2) i)) 0) ∧
      ¬ AffineIndependent ℝ (![0, 0, 0, ![0, 1]] : Fin 4 → Vec 2) ∧
      (∀ w : Fin 4 → ℝ, 0 < w 3 →
        ∑ i, w i • (![0, 0, 0, ![0, 1]] : Fin 4 → Vec 2) i = w 3 • ![0, 1] ∧
          w 3 • (![0, 1] : Vec 2) ≠ 0) ∧
      ¬ ∃ w : Fin 4 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
        ∑ i, w i • (![0, 0, 0, ![0, 1]] : Fin 4 → Vec 2) i = 0 := by
  have he : (![0, 1] : Vec 2) ≠ 0 := fun h => by simpa using congrFun h 1
  have hgrad := lower_branch_gradients_zero
  refine ⟨fun i => ?_, ?_, fun i => ?_, fun i => ?_, (degenerate_pattern he).1,
    (degenerate_pattern he).2.1, (degenerate_pattern he).2.2⟩
  · rw [LEmbedding.branch_zero, LEmbedding.objective_zero]
  · simpa using LQuadraticSeed.quadratic_hasGradient LEmbedding.mu 0
  · have hb := LEmbedding.parameter_bounds i
    have h := LScalar.phi_hasDerivAt (b := LEmbedding.parameter i) (by linarith [hb.1]) hb.2.le 0
    rwa [LScalar.phiFirst_zero (by linarith [hb.1]) hb.2.le] at h
  · rw [← hgrad i]
    exact LEmbedding.branch_hasGradient i 0

/-- Item `A/verification/prose/013` (`paper/sections/verification.tex:27-28`), with the
consequences of `A/verification/prose/014`–`016` (lines 27-31): "After the one fixed
change $x=Az$, the gradients are $0,0,0,A^Te_2$, with $A^Te_2\ne0$ ... (or
$\lambda_3A^Te_2\ne0$ after whitening)." For the whitened objective of Theorem
`art:local-failure-lower`, all four branches are active at zero with gradients
`0,0,0,A^Te_2`, `A^Te_2 ≠ 0`, and the gradient pattern has the same consequences. -/
theorem whitened_active_gradients :
    (∀ i, LUniform.smoothBranch i 0 = LUniform.smoothObjective 0) ∧
      (∀ i, HasFDerivAt (LUniform.smoothBranch i)
        (gradientFunctional
          ((![0, 0, 0, LUniform.coordinateMatrixᵀ.mulVec ![0, 1]] : Fin 4 → Vec 2) i)) 0) ∧
      LUniform.coordinateMatrixᵀ.mulVec ![0, 1] ≠ 0 ∧
      ¬ AffineIndependent ℝ (![0, 0, 0, LUniform.coordinateMatrixᵀ.mulVec ![0, 1]] : Fin 4 → Vec 2) ∧
      (∀ w : Fin 4 → ℝ, 0 < w 3 →
        ∑ i, w i • (![0, 0, 0, LUniform.coordinateMatrixᵀ.mulVec ![0, 1]] : Fin 4 → Vec 2) i =
            w 3 • LUniform.coordinateMatrixᵀ.mulVec ![0, 1] ∧
          w 3 • LUniform.coordinateMatrixᵀ.mulVec ![0, 1] ≠ 0) ∧
      ¬ ∃ w : Fin 4 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
        ∑ i, w i • (![0, 0, 0, LUniform.coordinateMatrixᵀ.mulVec ![0, 1]] : Fin 4 → Vec 2) i = 0 := by
  have he : LUniform.coordinateMatrixᵀ.mulVec ![0, 1] ≠ 0 := by
    intro h
    have hi := AffineWhitening.gradient_inverse LUniform.coordinateMatrix
      LUniform.coordinateMatrix_invertible ![0, 1]
    rw [AffineWhitening.gradient, h, Matrix.mulVec_zero] at hi
    simpa using congrFun hi 1
  have hgrad : ∀ i, LUniform.smoothGradient i 0 =
      (![0, 0, 0, LUniform.coordinateMatrixᵀ.mulVec ![0, 1]] : Fin 4 → Vec 2) i := by
    intro i
    simp only [LUniform.smoothGradient, AffineWhitening.gradient, Matrix.mulVec_zero,
      lower_branch_gradients_zero]
    fin_cases i <;> simp
  refine ⟨fun i => ?_, fun i => ?_, he, (degenerate_pattern he).1, (degenerate_pattern he).2.1,
    (degenerate_pattern he).2.2⟩
  · simp only [LUniform.smoothBranch, LUniform.smoothObjective, AffineWhitening.objective,
      Matrix.mulVec_zero, LEmbedding.branch_zero, LEmbedding.objective_zero]
  · rw [← hgrad i]
    exact (LUniform.smooth_branch_regular i).2.2.1 0

/-- Item `A/verification/prose/017` (`paper/sections/verification.tex:33-34`): "Three of the four
lower-curvature branches also lose second differentiability at zero" (corrected on 15 October
2026, M8, like the abstract's `A/master/prose/009`, `paper/master.tex` lines 53-55; both spoke of
all branches). Of the four branches of the objective of Theorem
`art:local-failure-lower`, the first three are not twice differentiable at the
minimizer `0`, while the fourth is. -/
theorem lower_branch_second_differentiability :
    (∀ i : Fin 3, ¬ DifferentiableAt ℝ (fderiv ℝ (LUniform.smoothBranch i.castSucc)) (0 : Vec 2)) ∧
      DifferentiableAt ℝ (fderiv ℝ (LUniform.smoothBranch 3)) (0 : Vec 2) :=
  ⟨LUniform.branch_not_twice_differentiable_zero,
    (AffineWhitening.second_differentiableAt_iff LUniform.coordinateMatrix
      LUniform.coordinateMatrix_invertible (LEmbedding.branch 3) 0).mpr
      (LEmbedding.branch_last_second_hasFDerivAt _).differentiableAt⟩

/-! ## The secant decomposition along the perturbed orbit -/

/-- At a differentiable point of `Q_μ` where the slope `g_i` is active
(`G(x)=g_i^T x`), the actual gradient is `μx+g_i`. -/
theorem gradient_of_active {μ : ℝ} {x : Vec 2} {i : Fin 3}
    (hx : DifferentiableAt ℝ (LQuadraticSeed.objective μ) x)
    (hi : SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD x =
      dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i) x) :
    coordinateGradient (LQuadraticSeed.objective μ) x =
      μ • x + SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i := by
  set c := coordinateGradient (LQuadraticSeed.objective μ) x
  have hQ : HasFDerivAt (LQuadraticSeed.objective μ) (gradientFunctional c) x :=
    hasFDerivAt_coordinateGradient hx
  have hG : HasFDerivAt (SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD)
      (gradientFunctional (c - μ • x)) x := by
    have hsub := hQ.sub (LQuadraticSeed.quadratic_hasGradient μ x)
    have hfun : (fun z => LQuadraticSeed.objective μ z - LQuadraticSeed.quadratic μ z) =
        SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD := by
      funext z
      simp [LQuadraticSeed.objective]
    have hlin : gradientFunctional c - gradientFunctional (μ • x) = gradientFunctional (c - μ • x) := by
      ext v
      simp [dot, sub_mul, Finset.sum_sub_distrib]
    rw [hfun, hlin] at hsub
    exact hsub
  have hact : (SeedOrbit.family SeedOrbit.seedC SeedOrbit.seedD).branch i x =
      (SeedOrbit.family SeedOrbit.seedC SeedOrbit.seedD).objective x := by
    simp only [MaxAffine.Family.branch, SeedOrbit.family, Pi.zero_apply, add_zero]
    exact hi.symm
  have h := (SeedOrbit.family SeedOrbit.seedC SeedOrbit.seedD).active_eq_gradient hact hG
  change SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i = c - μ • x at h
  rw [h]
  abel

/-- Item `A/verification/disp/001` (`paper/sections/verification.tex:41-44`), equation
`art:jump-secant`, with the hypotheses of lines 37-38: "For $Q_\mu(x)=\mu\|x\|^2/2+G(x)$, suppose
the differentiable endpoints $x$ and $x+s$ have active slopes $g_i$ and $g_j$. Then
exactly $y=(\mu(x+s)+g_j)-(\mu x+g_i)=\mu s+(g_j-g_i)$." Here `y` is the difference
of the actual gradients of `Q_μ` at the two endpoints. -/
theorem jump_secant {μ : ℝ} {x s : Vec 2} {i j : Fin 3}
    (hx : DifferentiableAt ℝ (LQuadraticSeed.objective μ) x)
    (hxs : DifferentiableAt ℝ (LQuadraticSeed.objective μ) (x + s))
    (hi : SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD x =
      dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i) x)
    (hj : SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD (x + s) =
      dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD j) (x + s)) :
    coordinateGradient (LQuadraticSeed.objective μ) (x + s) -
          coordinateGradient (LQuadraticSeed.objective μ) x =
        (μ • (x + s) + SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD j) -
          (μ • x + SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i) ∧
      (μ • (x + s) + SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD j) -
          (μ • x + SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i) =
        μ • s + (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD j -
          SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i) := by
  refine ⟨by rw [gradient_of_active hxs hj, gradient_of_active hx hi], ?_⟩
  rw [smul_add]
  abel

/-- Non-vacuity of the hypotheses of `jump_secant`: at `x=(1,0)` the slope `g_0` and at
`x+s=(-1,0)` the slope `g_1` are (strictly) active, and `Q_μ` is differentiable at both. -/
example (μ : ℝ) : ∃ x s : Vec 2,
    DifferentiableAt ℝ (LQuadraticSeed.objective μ) x ∧
      DifferentiableAt ℝ (LQuadraticSeed.objective μ) (x + s) ∧
      SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD x =
        dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD 0) x ∧
      SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD (x + s) =
        dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD 1) (x + s) := by
  obtain ⟨⟨hc0, hc1⟩, ⟨hd0, hd1⟩⟩ := SeedOrbit.root_tight_box
  set P := SeedOrbit.family SeedOrbit.seedC SeedOrbit.seedD
  have hxs : (![1, 0] : Vec 2) + ![-2, 0] = ![-1, 0] := by
    ext i
    fin_cases i <;> norm_num
  have hval : ∀ (i : Fin 3) (x : Vec 2), P.branch i x =
      dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i) x := by
    intro i x
    simp [P, MaxAffine.Family.branch, SeedOrbit.family]
  have h0 : ∀ j, j ≠ 0 → P.branch j ![1, 0] < P.branch 0 ![1, 0] := by
    intro j hj
    rw [hval, hval]
    fin_cases j
    · exact absurd rfl hj
    · norm_num [SeedOrbit.gradient, SeedCycle.g0, SeedCycle.g1, dot, Fin.sum_univ_two]
    · norm_num [SeedOrbit.gradient, SeedCycle.g0, SeedCycle.g2, dot, Fin.sum_univ_two]
      dsimp only [SeedOrbit.seedC]
      linarith
  have h1 : ∀ j, j ≠ 1 → P.branch j ![-1, 0] < P.branch 1 ![-1, 0] := by
    intro j hj
    rw [hval, hval]
    fin_cases j
    · norm_num [SeedOrbit.gradient, SeedCycle.g0, SeedCycle.g1, dot, Fin.sum_univ_two]
    · exact absurd rfl hj
    · norm_num [SeedOrbit.gradient, SeedCycle.g1, SeedCycle.g2, dot, Fin.sum_univ_two]
      dsimp only [SeedOrbit.seedC]
      linarith
  have hdiff : ∀ (i : Fin 3) (x : Vec 2), (∀ j, j ≠ i → P.branch j x < P.branch i x) →
      DifferentiableAt ℝ (LQuadraticSeed.objective μ) x ∧
        SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD x =
          dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i) x := by
    intro i x hi
    refine ⟨?_, ?_⟩
    · exact ((LQuadraticSeed.quadratic_hasGradient μ x).add (P.strict_active_hasGradient hi)).differentiableAt
    · rw [← hval]
      exact (P.strict_active_eventuallyEq hi).eq_of_nhds
  refine ⟨![1, 0], ![-2, 0], (hdiff 0 _ h0).1, ?_, (hdiff 0 _ h0).2, ?_⟩
  · rw [hxs]
    exact (hdiff 1 _ h1).1
  · rw [hxs]
    exact (hdiff 1 _ h1).2

/-- The three seed slopes are distinct. -/
theorem seed_slopes_distinct {i j : Fin 3} (hij : i ≠ j) :
    SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD j -
      SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD i ≠ 0 := by
  intro h
  have he := sub_eq_zero.mp h
  obtain ⟨⟨hc0, hc1⟩, ⟨hd0, hd1⟩⟩ := SeedOrbit.root_tight_box
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  fin_cases i <;> fin_cases j <;> simp_all [SeedOrbit.gradient, SeedCycle.g0, SeedCycle.g1,
    SeedCycle.g2] <;> dsimp only [SeedOrbit.seedC, SeedOrbit.seedD] at * <;> linarith

/-- Item `A/verification/prose/019` (`paper/sections/verification.tex:45-46`);
Item `A/verification/prose/020` (`paper/sections/verification.tex:46-47`): "Along the certified perturbed orbit,
$s\to0$ while the three distinct slopes continue to cycle. The positive-curvature
contribution therefore vanishes with the step, while the branch jumps persist."
For every `μ>0` there is one orbit `x_k`, `H_k` (with `H_0 ≻ 0`) that is the actual
run of the article's unit-first search on `Q_μ` for every pair `0<c₁≤1/3`,
`c₁<c₂<1`, with complete query trace; along it the active slope at `x_k` is
`g_{k mod 3}` (`∇Q_μ(x_k)=μx_k+g_{k mod 3}`), the secant is
`y_k=μs_k+(g_{(k+1) mod 3}-g_{k mod 3})`, `s_k → 0` and `μs_k → 0`, while the slope
jump `g_{(k+1) mod 3}-g_{k mod 3}` is nonzero for every `k`. -/
theorem perturbed_orbit_secants {μ : ℝ} (hμ : 0 < μ) :
    ∃ x : ℕ → Vec 2, ∃ H : ℕ → Mat 2, (H 0).PosDef ∧
      ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ 1 / 3 → c₁ < c₂ → c₂ < 1 →
        ∃ R : AdmissibleBFGSRun 2 (LQuadraticSeed.objective μ),
          R.x = x ∧ R.H = H ∧ R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
          (∀ k, NonStrictLineSearch.fromMetric (LQuadraticSeed.objective μ) (R.x k) (R.H k) c₁ c₂ 5 =
            (some (R.α k), SeedOrbit.trialHistory (SeedOrbit.phase k))) ∧
          (∀ k, ((SeedOrbit.phase k : Fin 3) : ℕ) = k % 3) ∧
          (∀ k, R.g k = μ • R.x k + SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD (SeedOrbit.phase k)) ∧
          (∀ k, R.g (k + 1) - R.g k = μ • (R.x (k + 1) - R.x k) +
            (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD (SeedOrbit.phase (k + 1)) -
              SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD (SeedOrbit.phase k))) ∧
          Tendsto (fun k => R.x (k + 1) - R.x k) atTop (𝓝 0) ∧
          Tendsto (fun k => μ • (R.x (k + 1) - R.x k)) atTop (𝓝 0) ∧
          ∀ k, SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD (SeedOrbit.phase (k + 1)) -
            SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD (SeedOrbit.phase k) ≠ 0 := by
  obtain ⟨O, ht, -, -⟩ := LUniform.orbit_exists μ univ univ_mem
  refine ⟨O.x, O.H, O.initial_posDef, ?_⟩
  intro c₁ c₂ hc₁ hc₁' hc hc₂
  have h : LUniform.Admissible c₁ c₂ := ⟨hc₁, hc₁', hc, hc₂⟩
  let R := O.run hμ.le h
  have hg : ∀ k, R.g k =
      μ • R.x k + SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD (SeedOrbit.phase k) := by
    intro k
    change (O.data h).g k = μ • (O.data h).x k + _
    rw [(O.data h).gradient_eq]
    simp only [LNormalizedOracle.phaseGradient, LNormalizedReturn.currentGradient,
      LFlatten.Data.x, LNormalizedOracle.physicalPoint, LNormalizedOracle.phasePoint, smul_smul]
    rw [add_comm, mul_comm]
  obtain ⟨hx, -⟩ := (O.data h).failure_contract hμ.le hc₁ hc hc₂ ht
  have hs : Tendsto (fun k => R.x (k + 1) - R.x k) atTop (𝓝 0) := by
    have := (hx.comp (tendsto_add_atTop_nat 1)).sub hx
    simpa using this
  have hphase : ∀ k, SeedOrbit.phase (k + 1) ≠ SeedOrbit.phase k := by
    intro k
    rcases SeedOrbit.phase_period_cases k with ⟨h0, h1, -⟩ | ⟨h0, h1, -⟩ | ⟨h0, h1, -⟩ <;>
      rw [h0, h1] <;> decide
  refine ⟨R, rfl, rfl, rfl, rfl, (O.data h).nonstrict_actual_search, fun k => rfl, hg,
    fun k => ?_, hs, by simpa using hs.const_smul μ, fun k => seed_slopes_distinct (hphase k).symm⟩
  rw [hg, hg, smul_sub]
  abel

/-! ## Branch changes without failure -/

/-- The library's explicit admissible run `UnexcitedMetric.run` on `u^2+|v|` with
`A = v₀ = 1`, `ρ = 1/2`, `c₁ = 1/4`, `c₂ = 1/2`: its iterates are `(0,(-1/2)^k)`. -/
def axisRun : AdmissibleBFGSRun 2 UnexcitedMetric.objective :=
  UnexcitedMetric.run 1 1 (1 / 2) (1 / 4) (1 / 2) one_pos one_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem axisRun_x (k : ℕ) :
    axisRun.x k = ![0, UnexcitedMetric.sign k * UnexcitedMetric.radius (1 / 2) 1 k] := rfl

theorem axisRun_g (k : ℕ) : axisRun.g k = ![0, UnexcitedMetric.sign k] := rfl

/-- The slopes `(0,1)`, `(0,-1)`, `(3,1/2)`, `(-3,1/2)`. -/
def fourSlopes : Finset (Vec 2) := {![0, 1], ![0, -1], ![3, 1 / 2], ![-3, 1 / 2]}

theorem fourSlopes_nonempty : fourSlopes.Nonempty := ⟨![0, 1], by simp [fourSlopes]⟩

/-- `F(u,v)=max{v,-v,3u+v/2,-3u+v/2}`, a coercive maximum of four linear functions. -/
abbrev fourMax : Vec 2 → ℝ := Homogeneous.finiteMaxLinear fourSlopes fourSlopes_nonempty

theorem fourMax_eq (x : Vec 2) :
    fourMax x = max (x 1) (max (-x 1) (max (3 * x 0 + x 1 / 2) (-3 * x 0 + x 1 / 2))) := by
  have hle : ∀ a ∈ fourSlopes, dot a x ≤ fourMax x := fun a ha =>
    Homogeneous.slope_le_finiteMaxLinear fourSlopes fourSlopes_nonempty ha x
  have m1 : (![0, 1] : Vec 2) ∈ fourSlopes := by simp [fourSlopes]
  have m2 : (![0, -1] : Vec 2) ∈ fourSlopes := by simp [fourSlopes]
  have m3 : (![3, 1 / 2] : Vec 2) ∈ fourSlopes := by simp [fourSlopes]
  have m4 : (![-3, 1 / 2] : Vec 2) ∈ fourSlopes := by simp [fourSlopes]
  have h1 := hle _ m1
  have h2 := hle _ m2
  have h3 := hle _ m3
  have h4 := hle _ m4
  simp only [dot, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    at h1 h2 h3 h4
  apply le_antisymm
  · apply Finset.sup'_le
    intro a ha
    simp only [fourSlopes, Finset.mem_insert, Finset.mem_singleton] at ha
    have l1 := le_max_left (x 1) (max (-x 1) (max (3 * x 0 + x 1 / 2) (-3 * x 0 + x 1 / 2)))
    have l2 := le_max_right (x 1) (max (-x 1) (max (3 * x 0 + x 1 / 2) (-3 * x 0 + x 1 / 2)))
    have l3 := le_max_left (-x 1) (max (3 * x 0 + x 1 / 2) (-3 * x 0 + x 1 / 2))
    have l4 := le_max_right (-x 1) (max (3 * x 0 + x 1 / 2) (-3 * x 0 + x 1 / 2))
    have l5 := le_max_left (3 * x 0 + x 1 / 2) (-3 * x 0 + x 1 / 2)
    have l6 := le_max_right (3 * x 0 + x 1 / 2) (-3 * x 0 + x 1 / 2)
    rcases ha with rfl | rfl | rfl | rfl <;>
      simp only [dot, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] <;> linarith
  · refine max_le (by linarith) (max_le (by linarith) (max_le (by linarith) (by linarith)))

theorem fourMax_axis (w : ℝ) : fourMax ![0, w] = |w| := by
  rw [fourMax_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_zero, zero_add,
    neg_zero]
  rcases le_total 0 w with h | h
  · rw [abs_of_nonneg h]
    exact le_antisymm (max_le le_rfl (max_le (by linarith) (max_le (by linarith) (by linarith))))
      (le_max_left _ _)
  · rw [abs_of_nonpos h]
    exact le_antisymm (max_le (by linarith) (max_le le_rfl (max_le (by linarith) (by linarith))))
      ((le_max_left _ _).trans (le_max_right _ _))

/-- On the axis `u=0`, away from `0`, `fourMax` has the gradient `(0, sign v)`. -/
theorem fourMax_hasGradient_axis {w : ℝ} (hw : w ≠ 0) :
    HasFDerivAt fourMax (gradientFunctional ![0, Real.sign w]) ![0, w] := by
  have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt
    (x := (![0, w] : Vec 2))
  rcases lt_or_gt_of_ne hw with h | h
  · have hS : {x : Vec 2 | x 1 < -x 1 ∧ 3 * x 0 + x 1 / 2 < -x 1 ∧ -3 * x 0 + x 1 / 2 < -x 1} ∈
        𝓝 (![0, w] : Vec 2) := by
      refine IsOpen.mem_nhds ?_ ?_
      · refine (isOpen_lt ?_ ?_).and ((isOpen_lt ?_ ?_).and (isOpen_lt ?_ ?_)) <;> fun_prop
      · simp only [Set.mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        exact ⟨by linarith, by linarith, by linarith⟩
    have heq : fourMax =ᶠ[𝓝 (![0, w] : Vec 2)] fun x => -x 1 := by
      filter_upwards [hS] with x hx
      rw [fourMax_eq]
      exact le_antisymm (max_le hx.1.le (max_le le_rfl (max_le hx.2.1.le hx.2.2.le)))
        ((le_max_left _ _).trans (le_max_right _ _))
    have hlin : HasFDerivAt (fun x : Vec 2 => -x 1) (gradientFunctional ![0, Real.sign w])
        ![0, w] := by
      convert hproj.neg using 1
      ext z
      simp [gradientFunctional_apply, dot, Fin.sum_univ_two, Real.sign_of_neg h]
    exact hlin.congr_of_eventuallyEq heq
  · have hS : {x : Vec 2 | -x 1 < x 1 ∧ 3 * x 0 + x 1 / 2 < x 1 ∧ -3 * x 0 + x 1 / 2 < x 1} ∈
        𝓝 (![0, w] : Vec 2) := by
      refine IsOpen.mem_nhds ?_ ?_
      · refine (isOpen_lt ?_ ?_).and ((isOpen_lt ?_ ?_).and (isOpen_lt ?_ ?_)) <;> fun_prop
      · simp only [Set.mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        exact ⟨by linarith, by linarith, by linarith⟩
    have heq : fourMax =ᶠ[𝓝 (![0, w] : Vec 2)] fun x => x 1 := by
      filter_upwards [hS] with x hx
      rw [fourMax_eq]
      exact le_antisymm (max_le le_rfl (max_le hx.1.le (max_le hx.2.1.le hx.2.2.le)))
        (le_max_left _ _)
    have hlin : HasFDerivAt (fun x : Vec 2 => x 1) (gradientFunctional ![0, Real.sign w])
        ![0, w] := by
      convert hproj using 1
      ext z
      simp [gradientFunctional_apply, dot, Fin.sum_univ_two, Real.sign_of_pos h]
    exact hlin.congr_of_eventuallyEq heq

/-- The zero sublevel of `fourMax` is `{0}`, so `fourMax` is coercive. -/
theorem fourMax_zero_sublevel : Bornology.IsBounded {x : Vec 2 | fourMax x ≤ 0} := by
  apply (Bornology.isBounded_singleton (x := (0 : Vec 2))).subset
  intro x hx
  simp only [Set.mem_setOf_eq, fourMax_eq] at hx
  have h1 := (le_max_left _ _).trans hx
  have h2 := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have h3 := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hx
  have h4 := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hx
  have hx1 : x 1 = 0 := by linarith
  have hx0 : x 0 = 0 := by linarith
  rw [Set.mem_singleton_iff]
  ext i
  fin_cases i
  · simpa using hx0
  · simpa using hx1

/-- The values of `fourMax` and of `u^2+|v|` agree on the axis `u=0`. -/
theorem fourMax_axisRun (k : ℕ) :
    fourMax (axisRun.x k) = UnexcitedMetric.objective (axisRun.x k) := by
  rw [axisRun_x, fourMax_axis]
  simp [UnexcitedMetric.objective]

/-- An admissible run of `fourMax`: the iterates, matrices, gradients and accepted
lengths of `axisRun`, which stay on the axis `u=0`, where `fourMax` coincides with
`u^2+|v|` together with its gradient `(0, ±1)`. -/
def fourMaxRun : AdmissibleBFGSRun 2 fourMax where
  convex := Homogeneous.finiteMaxLinear_convex fourSlopes fourSlopes_nonempty
  x := axisRun.x
  H := axisRun.H
  g := axisRun.g
  α := axisRun.α
  c₁ := axisRun.c₁
  c₂ := axisRun.c₂
  c₁_pos := axisRun.c₁_pos
  c₁_lt_c₂ := axisRun.c₁_lt_c₂
  c₂_lt_one := axisRun.c₂_lt_one
  initial_posDef := axisRun.initial_posDef
  alpha_pos := axisRun.alpha_pos
  gradient_nonzero := axisRun.gradient_nonzero
  hasGradient k := by
    have hr : 0 < UnexcitedMetric.radius (1 / 2) 1 k :=
      UnexcitedMetric.radius_pos (by norm_num) one_pos k
    have hs : UnexcitedMetric.sign k = 1 ∨ UnexcitedMetric.sign k = -1 :=
      (sq_eq_one_iff).mp (UnexcitedMetric.sign_sq k)
    rw [axisRun_x, axisRun_g]
    rcases hs with hs | hs
    · have h := fourMax_hasGradient_axis
        (w := UnexcitedMetric.sign k * UnexcitedMetric.radius (1 / 2) 1 k)
        (by rw [hs, one_mul]; exact hr.ne')
      rw [hs, one_mul, Real.sign_of_pos hr] at h
      rw [hs, one_mul]
      exact h
    · have h := fourMax_hasGradient_axis
        (w := UnexcitedMetric.sign k * UnexcitedMetric.radius (1 / 2) 1 k)
        (by rw [hs, neg_one_mul]; exact neg_ne_zero.mpr hr.ne')
      rw [hs, neg_one_mul, Real.sign_of_neg (neg_neg_of_pos hr)] at h
      rw [hs, neg_one_mul]
      exact h
  step := axisRun.step
  update := axisRun.update
  armijo k := by
    rw [fourMax_axisRun, fourMax_axisRun]
    exact axisRun.armijo k
  weak_wolfe := axisRun.weak_wolfe

/-- Item `A/verification/prose/022` (`paper/sections/verification.tex:49`): "a branch change
alone does not imply failure." For every coercive finite maximum of linear functions
`F(x)=max_{a∈A} a^Tx` (bounded zero sublevel), every infinite admissible run changes its
active linear piece at every accepted step: at `x_k` the only active slope is the gradient
`g_k ∈ A`, and `g_{k+1} ≠ g_k` because weak Wolfe gives `y_k^Ts_k > 0`. Yet every such run
converges to the unique minimizer `0` in value and iterates. Such runs exist: `fourMaxRun`
is one, for `F(u,v)=max{v,-v,3u+v/2,-3u+v/2}`. -/
theorem branch_change_without_failure :
    (∀ (n : ℕ) (A : Finset (Vec n)) (hA : A.Nonempty),
      Bornology.IsBounded {x | Homogeneous.finiteMaxLinear A hA x ≤ 0} →
      ∀ R : AdmissibleBFGSRun n (Homogeneous.finiteMaxLinear A hA),
        (∀ k, R.g k ∈ A ∧
          (∀ a ∈ A, Homogeneous.finiteMaxLinear A hA (R.x k) = dot a (R.x k) → a = R.g k) ∧
          R.g (k + 1) ≠ R.g k) ∧
        Homogeneous.finiteMaxLinear A hA 0 = 0 ∧
        (∀ x, x ≠ 0 → 0 < Homogeneous.finiteMaxLinear A hA x) ∧
        Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)) atTop (𝓝 0) ∧
        Tendsto R.x atTop (𝓝 0)) ∧
      ∃ (A : Finset (Vec 2)) (hA : A.Nonempty),
        Bornology.IsBounded {x | Homogeneous.finiteMaxLinear A hA x ≤ 0} ∧
        Nonempty (AdmissibleBFGSRun 2 (Homogeneous.finiteMaxLinear A hA)) := by
  refine ⟨fun n A hA hb R => ?_, fourSlopes, fourSlopes_nonempty, fourMax_zero_sublevel,
    ⟨fourMaxRun⟩⟩
  obtain ⟨h0, hpos, hv, hx⟩ := AdmissibleBFGSRun.finiteMaxLinear_conclusion A hA hb R
  refine ⟨fun k => ⟨Homogeneous.finiteMaxLinear_gradient_mem A hA (R.hasGradient k),
    fun a ha he => Homogeneous.finiteMaxLinear_active_eq_gradient A hA ha he (R.hasGradient k),
    fun h => ?_⟩, h0, hpos, hv, hx⟩
  have hc := R.curvature_pos k
  rw [h, sub_self] at hc
  simp [dot] at hc

/-! ## The open question -/

/-- Item `A/verification/prose/025` (`paper/sections/verification.tex:55-56`), OPEN
(stated without proof): "The broader local question for finitely many uniformly
strongly convex $C^2$ branches remains open here."

The proposition below is the local failure of Theorems `art:local-failure` and
`art:local-failure-lower` with the branch class of the question: a finite maximum
`F` of `C^2` branches that are all `κ`-strongly convex (Euclidean), with minimizer
`x_*`, and actual infinite runs of the article's unit-first Armijo--weak-Wolfe
search (non-strict tests, `NonStrictLineSearch.fromMetric`), all with `H_0=I` and
one fixed pair `0<c₁<c₂<1`, whose starts tend to `x_*`, whose queried points are
all differentiable, and none of which converges to `x_*`. Its truth would extend
the negative results to that class; its negation, for every such `F`, is an
every-start neighbourhood guarantee for the specified search. Neither is proved. -/
def C2StronglyConvexLocalFailure : Prop :=
  ∃ (n m : ℕ) (hm : 0 < m) (f : Fin m → Vec n → ℝ) (κ : ℝ), 0 < κ ∧
    (∀ i, ContDiff ℝ 2 (f i) ∧ FixedNormal.EuclideanStrongConvexOn univ κ (f i)) ∧
    let F : Vec n → ℝ := fun x =>
      (Finset.univ : Finset (Fin m)).sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i => f i x)
    ∃ (xstar : Vec n) (c₁ c₂ : ℝ) (R : ℕ → AdmissibleBFGSRun n F),
      (∀ x, F xstar ≤ F x) ∧ 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1 ∧
      Tendsto (fun ℓ => (R ℓ).x 0) atTop (𝓝 xstar) ∧
      ∀ ℓ, (R ℓ).H 0 = 1 ∧ (R ℓ).c₁ = c₁ ∧ (R ℓ).c₂ = c₂ ∧
        (∀ k, ∃ fuel : ℕ,
          (NonStrictLineSearch.fromMetric F ((R ℓ).x k) ((R ℓ).H k) c₁ c₂ fuel).1 = some ((R ℓ).α k) ∧
          ∀ a ∈ (NonStrictLineSearch.fromMetric F ((R ℓ).x k) ((R ℓ).H k) c₁ c₂ fuel).2,
            DifferentiableAt ℝ F ((R ℓ).x k + a • bfgsStep ((R ℓ).H k) ((R ℓ).g k) 1)) ∧
        ¬ Tendsto (R ℓ).x atTop (𝓝 xstar)

end BfgsCoverage.Article.Verification
