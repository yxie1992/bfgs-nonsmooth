import BfgsArticle.LUniformGlobal
import BfgsArticle.LNonStrictLocal
import ArticleBranchRegularity

/-!
# Lower-curvature local failure for every admissible line-search pair

The library's local construction (`LSeedCopies`, `LActualCopies`, `LWhitening`)
starts from a source orbit chosen for `c₁=10⁻⁴`, `c₂=1/2`. This file repeats the
three stages (source run, scaled copies, one fixed whitening) from the orbit of
`LUniformGlobal.lean`, which is chosen before the constants. The copies and the
whitening matrix are therefore the same for every `0<c₁≤1/3`, `c₁<c₂<1`, and so are
the objective, the starts, every iterate and matrix, and the complete decision tree.

The generic transfer lemmas (`ScaledCopy.Data`, `AffineWhitening`, their non-strict
versions in `NonStrictTransfer.lean`) and the local model data
`LActualCopies.smoothData` are reused unchanged; only the source run is new. The
geometry of the whitened objective is proved exactly as in `LWhiteningGeometry` and
`LIdentityGeometry`, for the new whitening matrix.
-/

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix

namespace BfgsVerification.LUniform
open SeedOrbit SeedCycle LScalarGeometric
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ## The source orbit, chosen once inside the local chart -/

theorem source_exists : ∃ O : Orbit LEmbedding.mu,
    Tendsto O.state atTop (𝓝 LNormalizedReturn.seed) ∧ (∀ k, O.x k∈LEmbedding.localDomain) ∧
    ∀ k q, trialPhase q=phase k →
      O.x k+trialLength q • bfgsStep (O.H k) (O.g k) 1∈LEmbedding.localDomain :=
  orbit_exists LEmbedding.mu LEmbedding.localDomain LEmbedding.localDomain_nhds

/-- The selected source orbit. It is chosen before, and independently of, the
line-search constants. -/
def source : Orbit LEmbedding.mu := Classical.choose source_exists

theorem source_spec : Tendsto source.state atTop (𝓝 LNormalizedReturn.seed) ∧
    (∀ k, source.x k∈LEmbedding.localDomain) ∧
    ∀ k q, trialPhase q=phase k →
      source.x k+trialLength q • bfgsStep (source.H k) (source.g k) 1∈LEmbedding.localDomain :=
  Classical.choose_spec source_exists

/-- The library's literal pair, used only to name the common sequences. -/
theorem sourcePair : Admissible (1/10000) (1/2) := ⟨by norm_num,by norm_num,by norm_num,by norm_num⟩

variable {c₁ c₂ : ℝ}

/-- The source run for one admissible pair. Its iterates, matrices and gradients are
`source.x`, `source.H`, `source.g` for every pair. -/
def sourceRun (h : Admissible c₁ c₂) : AdmissibleBFGSRun 2 (LQuadraticSeed.objective LEmbedding.mu) :=
  source.run LEmbedding.mu_pos.le h

theorem point_in (h : Admissible c₁ c₂) (k : ℕ) : (sourceRun h).x k∈LEmbedding.localDomain :=
  source_spec.2.1 k

theorem run_point_limit (h : Admissible c₁ c₂) : Tendsto (sourceRun h).x atTop (𝓝 0) :=
  (source.data h).point_tendsto source_spec.1

theorem run_matrix_limit (h : Admissible c₁ c₂) : Tendsto (sourceRun h).H atTop (𝓝 0) :=
  (source.data h).metric_tendsto source_spec.1

theorem run_value_limit (h : Admissible c₁ c₂) :
    Tendsto (fun k => LQuadraticSeed.objective LEmbedding.mu ((sourceRun h).x k)) atTop (𝓝 0) :=
  (source.data h).value_tendsto LEmbedding.mu_pos.le source_spec.1

theorem run_value_positive (h : Admissible c₁ c₂) (k : ℕ) :
    0<LQuadraticSeed.objective LEmbedding.mu ((sourceRun h).x k) :=
  (source.data h).value_positive k

theorem run_search (h : Admissible c₁ c₂) (k : ℕ) :
    DeterministicLineSearch.fromMetric (LQuadraticSeed.objective LEmbedding.mu) ((sourceRun h).x k)
      ((sourceRun h).H k) (sourceRun h).c₁ (sourceRun h).c₂ 5=
      (some ((sourceRun h).α k),trialHistory (phase k)) :=
  (source.data h).actual_search k

theorem nonstrict_run_search (h : Admissible c₁ c₂) (k : ℕ) :
    NonStrictLineSearch.fromMetric (LQuadraticSeed.objective LEmbedding.mu) ((sourceRun h).x k)
      ((sourceRun h).H k) (sourceRun h).c₁ (sourceRun h).c₂ 5=
      (some ((sourceRun h).α k),trialHistory (phase k)) :=
  (source.data h).nonstrict_actual_search k

theorem run_query_conditions (h : Admissible c₁ c₂) (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    (sourceRun h).x k+trialLength q • bfgsStep ((sourceRun h).H k) ((sourceRun h).g k) 1∈
      LEmbedding.localDomain ∧
    DifferentiableAt ℝ (LQuadraticSeed.objective LEmbedding.mu)
      ((sourceRun h).x k+trialLength q • bfgsStep ((sourceRun h).H k) ((sourceRun h).g k) 1) :=
  ⟨source_spec.2.2 k q hq,((source.data h).all_trial_derivatives k q hq).differentiableAt⟩

theorem history_query_conditions (h : Admissible c₁ c₂) (k : ℕ) (a : ℝ)
    (ha : a∈(DeterministicLineSearch.fromMetric (LQuadraticSeed.objective LEmbedding.mu) ((sourceRun h).x k)
      ((sourceRun h).H k) (sourceRun h).c₁ (sourceRun h).c₂ 5).2) :
    (sourceRun h).x k+a • bfgsStep ((sourceRun h).H k) ((sourceRun h).g k) 1∈LEmbedding.localDomain ∧
    DifferentiableAt ℝ (LQuadraticSeed.objective LEmbedding.mu)
      ((sourceRun h).x k+a • bfgsStep ((sourceRun h).H k) ((sourceRun h).g k) 1) := by
  rw [run_search] at ha
  obtain ⟨q,hq,rfl⟩ := trial_history_witness (phase k) ha
  exact run_query_conditions h k q hq

theorem nonstrict_history_query_conditions (h : Admissible c₁ c₂) (k : ℕ) (a : ℝ)
    (ha : a∈(NonStrictLineSearch.fromMetric (LQuadraticSeed.objective LEmbedding.mu) ((sourceRun h).x k)
      ((sourceRun h).H k) (sourceRun h).c₁ (sourceRun h).c₂ 5).2) :
    (sourceRun h).x k+a • bfgsStep ((sourceRun h).H k) ((sourceRun h).g k) 1∈LEmbedding.localDomain ∧
    DifferentiableAt ℝ (LQuadraticSeed.objective LEmbedding.mu)
      ((sourceRun h).x k+a • bfgsStep ((sourceRun h).H k) ((sourceRun h).g k) 1) := by
  rw [nonstrict_run_search] at ha
  obtain ⟨q,hq,rfl⟩ := trial_history_witness (phase k) ha
  exact run_query_conditions h k q hq

theorem query_tendsto (h : Admissible c₁ c₂) (q : ℕ → Fin 9) (hq : ∀ k, trialPhase (q k)=phase k) :
    Tendsto (fun k => (sourceRun h).x k+trialLength (q k) •
      bfgsStep ((sourceRun h).H k) ((sourceRun h).g k) 1) atTop (𝓝 0) :=
  (source.data h).actual_trials_tendsto source_spec.1 q hq

/-! ## Scaled copies with one fixed matrix -/

variable {F : Vec 2 → ℝ}

def family (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m : ℕ) : AdmissibleBFGSRun 2 F :=
  D.run (sourceRun h) (point_in h) m

theorem family_x (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ) :
    (family D h m).x k=LEmbedding.copyCenter m+scale m • source.x k := rfl

theorem family_H (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ) :
    (family D h m).H k=source.H k := rfl

theorem copy_point_limit (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m : ℕ) :
    Tendsto (family D h m).x atTop (𝓝 (LEmbedding.copyCenter m)) :=
  D.run_tendsto (sourceRun h) (point_in h) (run_point_limit h) m

theorem copy_matrix_limit (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m : ℕ) :
    Tendsto (family D h m).H atTop (𝓝 0) := run_matrix_limit h

theorem copy_value_limit (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m : ℕ) :
    Tendsto (fun k => F ((family D h m).x k)) atTop (𝓝 ((scale m)^2*LEmbedding.offset)) :=
  D.run_values_tendsto (sourceRun h) (point_in h) (run_value_limit h) m

theorem copy_values_above_limit (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ) :
    (scale m)^2*LEmbedding.offset<F ((family D h m).x k) :=
  D.run_values_above_limit (sourceRun h) (point_in h) (run_value_positive h) m k

theorem copy_starts_tendsto (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) :
    Tendsto (fun m => (family D h m).x 0) atTop (𝓝 (0 : Vec 2)) :=
  D.starts_tendsto_zero (sourceRun h) (point_in h)

theorem copy_actual_search (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ) :
    DeterministicLineSearch.fromMetric F ((family D h m).x k) ((family D h m).H k) c₁ c₂ 5=
      (some ((family D h m).α k),trialHistory (phase k)) :=
  (D.search_transfer (sourceRun h) (point_in h) 5 (history_query_conditions h) m k).trans (run_search h k)

theorem copy_nonstrict_actual_search (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ) :
    NonStrictLineSearch.fromMetric F ((family D h m).x k) ((family D h m).H k) c₁ c₂ 5=
      (some ((family D h m).α k),trialHistory (phase k)) :=
  (D.nonstrict_search_transfer (sourceRun h) (point_in h) 5 (nonstrict_history_query_conditions h) m k).trans
    (nonstrict_run_search h k)

theorem copy_trial_hasGradient (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ)
    (q : Fin 9) (hq : trialPhase q=phase k) :
    HasFDerivAt F (gradientFunctional (scale m • coordinateGradient (LQuadraticSeed.objective LEmbedding.mu)
      ((sourceRun h).x k+trialLength q • bfgsStep ((sourceRun h).H k) ((sourceRun h).g k) 1)))
      ((family D h m).x k+trialLength q • bfgsStep ((family D h m).H k) ((family D h m).g k) 1) := by
  obtain ⟨hU,hd⟩ := run_query_conditions h k q hq
  exact D.query_hasGradient (sourceRun h) (point_in h) m k (trialLength q) hU hd

theorem copy_trial_value_positive (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ)
    (q : Fin 9) (hq : trialPhase q=phase k) :
    0<F ((family D h m).x k+trialLength q • bfgsStep ((family D h m).H k) ((family D h m).g k) 1) := by
  have hh := D.query_value (sourceRun h) (point_in h) m k (trialLength q) (run_query_conditions h k q hq).1
  unfold family
  rw [hh]
  have hp := (source.data h).all_trial_values_positive k q hq
  exact mul_pos (sq_pos_of_pos (scale_pos m)) (add_pos LEmbedding.offset_pos hp)

theorem copy_trials_limit (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m : ℕ)
    (q : ℕ → Fin 9) (hq : ∀ k, trialPhase (q k)=phase k) :
    Tendsto (fun k => (family D h m).x k+trialLength (q k) •
      bfgsStep ((family D h m).H k) ((family D h m).g k) 1) atTop (𝓝 (LEmbedding.copyCenter m)) :=
  D.queries_tendsto (sourceRun h) (point_in h) m (fun k => trialLength (q k)) (query_tendsto h q hq)

theorem copy_strict_accept (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ) :
    F ((family D h m).x (k+1))<F ((family D h m).x k)+
      c₁*dot ((family D h m).g k) (bfgsStep ((family D h m).H k) ((family D h m).g k) ((family D h m).α k)) ∧
    c₂*dot ((family D h m).g k) (bfgsStep ((family D h m).H k) ((family D h m).g k) ((family D h m).α k))<
      dot ((family D h m).g (k+1)) (bfgsStep ((family D h m).H k) ((family D h m).g k) ((family D h m).α k)) := by
  have hv (j : ℕ) : F ((family D h m).x j)=(scale m)^2*(LEmbedding.offset+
      LQuadraticSeed.objective LEmbedding.mu ((sourceRun h).x j)) :=
    D.run_value (sourceRun h) (point_in h) m j
  have hp (j : ℕ) : dot ((family D h m).g j)
      (bfgsStep ((family D h m).H k) ((family D h m).g k) ((family D h m).α k))=
      (scale m)^2*dot ((sourceRun h).g j)
        (bfgsStep ((sourceRun h).H k) ((sourceRun h).g k) ((sourceRun h).α k)) :=
    TranslatedRun.scaled_pairing (sourceRun h) (scale m) j k
  obtain ⟨ha,hw⟩ := (source.data h).strict_accept k
  rw [hv,hv,hp,hp]
  constructor
  · have hh := mul_lt_mul_of_pos_left ha (sq_pos_of_pos (scale_pos m))
    change (scale m)^2*LQuadraticSeed.objective LEmbedding.mu ((sourceRun h).x (k+1))<
      (scale m)^2*(LQuadraticSeed.objective LEmbedding.mu ((sourceRun h).x k)+
        c₁*dot ((sourceRun h).g k) (bfgsStep ((sourceRun h).H k) ((sourceRun h).g k) ((sourceRun h).α k))) at hh
    nlinarith
  · have hh := mul_lt_mul_of_pos_left hw (sq_pos_of_pos (scale_pos m))
    change (scale m)^2*(c₂*dot ((sourceRun h).g k)
      (bfgsStep ((sourceRun h).H k) ((sourceRun h).g k) ((sourceRun h).α k)))<
      (scale m)^2*dot ((sourceRun h).g (k+1))
        (bfgsStep ((sourceRun h).H k) ((sourceRun h).g k) ((sourceRun h).α k)) at hh
    nlinarith

theorem copy_point_norm_bound (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ) :
    ‖(family D h m).x k‖≤LActualCopies.uniformBound m := by
  rw [family_x]
  have hh := norm_add_le (scale m • LEmbedding.center) (scale m • source.x k)
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (scale_pos m)] at hh
  have hb := mul_le_mul_of_nonneg_left (source_spec.2.1 k).1.le (scale_pos m).le
  change ‖scale m • LEmbedding.center+scale m • source.x k‖≤scale m*(‖LEmbedding.center‖+1)
  nlinarith

theorem copy_trial_norm_bound (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ)
    (q : Fin 9) (hq : trialPhase q=phase k) :
    ‖(family D h m).x k+trialLength q • bfgsStep ((family D h m).H k) ((family D h m).g k) 1‖≤
      LActualCopies.uniformBound m :=
  D.query_norm_bound (sourceRun h) (point_in h) m k (trialLength q) 1
    (run_query_conditions h k q hq).1.1.le

theorem copy_uniform_locality (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂)
    (U : Set (Vec 2)) (hU : U∈𝓝 (0 : Vec 2)) :
    ∃ N : ℕ, ∀ m≥N, ∀ k, (family D h m).x k∈U ∧ ∀ q : Fin 9, trialPhase q=phase k →
      (family D h m).x k+trialLength q • bfgsStep ((family D h m).H k) ((family D h m).g k) 1∈U := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  have he : ∀ᶠ m in atTop, LActualCopies.uniformBound m<ε :=
    LActualCopies.uniformBound_tendsto.eventually (gt_mem_nhds hε)
  obtain ⟨N,hN⟩ := eventually_atTop.1 he
  refine ⟨N,?_⟩
  intro m hm k
  constructor
  · apply hball
    simpa only [Metric.mem_ball,dist_zero_right] using (copy_point_norm_bound D h m k).trans_lt (hN m hm)
  · intro q hq
    apply hball
    simpa only [Metric.mem_ball,dist_zero_right] using (copy_trial_norm_bound D h m k q hq).trans_lt (hN m hm)

/-! ## One fixed whitening -/

section Whitening
open AffineWhitening AffineProjection

/-- The common initial matrix of every copy, for every admissible pair. -/
def initialMetric : Mat 2 := source.H 0

theorem initialMetric_posDef : initialMetric.PosDef := source.initial_posDef

def coordinateMatrix : Mat 2 := squareRoot initialMetric initialMetric_posDef

theorem coordinateMatrix_square : coordinateMatrix*coordinateMatrix=initialMetric :=
  squareRoot_square _ _
theorem coordinateMatrix_transpose : coordinateMatrixᵀ=coordinateMatrix := squareRoot_transpose _ _
theorem coordinateMatrix_invertible : coordinateMatrix.det≠0 := squareRoot_det_ne_zero _ _

def lowerConstant : ℝ := LEmbedding.mu*minEigenvalue initialMetric initialMetric_posDef.1
def upperConstant : ℝ := 512*maxEigenvalue initialMetric initialMetric_posDef.1

theorem lowerConstant_pos : 0<lowerConstant :=
  mul_pos LEmbedding.mu_pos (minEigenvalue_pos initialMetric initialMetric_posDef)
theorem upperConstant_pos : 0<upperConstant :=
  mul_pos (by norm_num) (maxEigenvalue_pos initialMetric initialMetric_posDef)

theorem constants_order : lowerConstant≤upperConstant := by
  have hm := (minEigenvalue_le initialMetric initialMetric_posDef.1 0).trans
    (le_maxEigenvalue initialMetric initialMetric_posDef.1 0)
  have hM := maxEigenvalue_pos initialMetric initialMetric_posDef
  dsimp [lowerConstant,upperConstant,LEmbedding.mu]
  nlinarith

/-- The one fixed objective of the uniform theorem. -/
def smoothObjective : Vec 2 → ℝ := AffineWhitening.objective coordinateMatrix LEmbedding.objective
def smoothBranch (i : Fin 4) : Vec 2 → ℝ := AffineWhitening.objective coordinateMatrix (LEmbedding.branch i)
def smoothGradient (i : Fin 4) (z : Vec 2) : Vec 2 :=
  gradient coordinateMatrix (LEmbedding.branchGradient i (coordinateMatrix.mulVec z))

theorem smooth_branch_regular (i : Fin 4) :
    ContDiff ℝ 1 (smoothBranch i) ∧
    FixedNormal.EuclideanStrongConvexOn univ lowerConstant (smoothBranch i) ∧
    (∀ z, HasFDerivAt (smoothBranch i) (gradientFunctional (smoothGradient i z)) z) ∧
    ∀ x y, sqNorm (smoothGradient i x-smoothGradient i y)≤upperConstant^2*sqNorm (x-y) := by
  refine ⟨contDiff_whitening _ (LEmbedding.branch_contDiff i),
    strongConvex_whitening _ initialMetric_posDef LEmbedding.mu_pos.le (LEmbedding.branch_strongConvex i),?_,?_⟩
  · intro z
    exact hasGradient_comp coordinateMatrix (LEmbedding.branch i) z _ (LEmbedding.branch_hasGradient i _)
  · exact gradient_bound_whitening initialMetric initialMetric_posDef
      (LEmbedding.branchGradient i) 512 (LEmbedding.branch_gradient_bound i)

theorem smooth_objective_eq_max (z : Vec 2) :
    smoothObjective z=Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 4 => smoothBranch i z) :=
  LEmbedding.objective_eq_max _

theorem smooth_strongConvex : FixedNormal.EuclideanStrongConvexOn univ lowerConstant smoothObjective :=
  strongConvex_whitening _ initialMetric_posDef LEmbedding.mu_pos.le LEmbedding.objective_strongConvex

theorem smooth_zero : smoothObjective 0=0 := by
  simpa [smoothObjective,AffineWhitening.objective] using LEmbedding.objective_zero

theorem smooth_unique_zero {z : Vec 2} (hz : smoothObjective z=0) : z=0 :=
  zero_unique_whitening coordinateMatrix coordinateMatrix_invertible
    (fun _ => LEmbedding.objective_unique_zero) hz

theorem smooth_compact_sublevel (a : ℝ) : IsCompact {z | smoothObjective z≤a} :=
  sublevels_compact_whitening coordinateMatrix coordinateMatrix_invertible
    LEmbedding.objective_sublevels_compact a

theorem smooth_coercive : Tendsto smoothObjective (cocompact (Vec 2)) atTop :=
  coercive_of_compact_sublevels smooth_compact_sublevel

theorem smooth_lower (z : Vec 2) : lowerConstant/2*sqNorm z≤smoothObjective z := by
  have hs := mul_le_mul_of_nonneg_left (squareRoot_norm_bounds initialMetric initialMetric_posDef z).1
    (div_nonneg LEmbedding.mu_pos.le (by norm_num : (0 : ℝ)≤2))
  have hb := LEmbedding.objective_lower (coordinateMatrix.mulVec z)
  change LEmbedding.mu/2*(minEigenvalue initialMetric initialMetric_posDef.1*sqNorm z)≤
    LEmbedding.mu/2*sqNorm (coordinateMatrix.mulVec z) at hs
  change (LEmbedding.mu*minEigenvalue initialMetric initialMetric_posDef.1)/2*sqNorm z≤
    LEmbedding.objective (coordinateMatrix.mulVec z)
  nlinarith

theorem smooth_nonsmooth_origin : ¬DifferentiableAt ℝ smoothObjective (0 : Vec 2) := by
  have he := differentiableAt_equiv coordinateMatrix coordinateMatrix_invertible LEmbedding.objective 0
  simpa only [AffineWhitening.point,Matrix.mulVec_zero,smoothObjective] using
    mt he.mp LEmbedding.objective_not_differentiable_zero

theorem smooth_localFiniteMax (x : Vec 2) :
    ConvexSubdifferential.LocalFiniteMax smoothObjective smoothBranch x :=
  Eventually.of_forall (fun z => LEmbedding.objective_isGreatest (coordinateMatrix.mulVec z))

/-- The three ridge branches keep their failure of second differentiability at the
minimizer after the fixed whitening. -/
theorem branch_not_twice_differentiable_zero (i : Fin 3) :
    ¬ DifferentiableAt ℝ (fderiv ℝ (smoothBranch i.castSucc)) (0 : Vec 2) := by
  intro hd
  have h := (AffineWhitening.second_differentiableAt_iff coordinateMatrix coordinateMatrix_invertible
    (LEmbedding.branch i.castSucc) (0 : Vec 2)).mp hd
  exact ArticleBranchRegularity.branch_not_twice_differentiable_zero i
    (by simpa only [Matrix.mulVec_zero] using h)

/-! ## The identity-initialized family -/

def failureFamily (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m : ℕ) :
    AdmissibleBFGSRun 2 (AffineWhitening.objective coordinateMatrix F) :=
  AffineWhitening.run coordinateMatrix coordinateMatrix_invertible (family D h m)

def failureCenter (m : ℕ) : Vec 2 := point coordinateMatrix (LEmbedding.copyCenter m)

theorem failure_centers_tendsto : Tendsto failureCenter atTop (𝓝 (0 : Vec 2)) := by
  simpa only [AffineWhitening.point,Matrix.mulVec_zero] using
    AffineWhitening.point_limit coordinateMatrix LEmbedding.copyCenter_tendsto

theorem failure_initial (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m : ℕ) :
    (failureFamily D h m).H 0=1 :=
  fixed_initial_whitening initialMetric initialMetric_posDef (family D h m) rfl

theorem failure_point_limit (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m : ℕ) :
    Tendsto (failureFamily D h m).x atTop (𝓝 (failureCenter m)) :=
  AffineWhitening.point_limit coordinateMatrix (copy_point_limit D h m)

theorem failure_matrix_limit (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m : ℕ) :
    Tendsto (failureFamily D h m).H atTop (𝓝 0) :=
  metric_limit_zero coordinateMatrix (copy_matrix_limit D h m)

theorem failure_value_limit (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m : ℕ) :
    Tendsto (fun k => AffineWhitening.objective coordinateMatrix F ((failureFamily D h m).x k))
      atTop (𝓝 ((scale m)^2*LEmbedding.offset)) := by
  simpa only [failureFamily,run_value] using copy_value_limit D h m

theorem failure_values_above (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ) :
    (scale m)^2*LEmbedding.offset<AffineWhitening.objective coordinateMatrix F ((failureFamily D h m).x k) := by
  simpa only [failureFamily,run_value] using copy_values_above_limit D h m k

theorem failure_starts (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) :
    Tendsto (fun m => (failureFamily D h m).x 0) atTop (𝓝 (0 : Vec 2)) :=
  starts_limit_zero coordinateMatrix coordinateMatrix_invertible (family D h) (copy_starts_tendsto D h)

theorem failure_centers_nonstationary (D : LActualCopies.CopyData F) (hF0 : F 0=0) (m : ℕ) :
    (0 : Vec 2)∉ConvexSubdifferential.subdifferential (AffineWhitening.objective coordinateMatrix F)
      (failureCenter m) :=
  nonstationary_whitening coordinateMatrix coordinateMatrix_invertible _
    (LActualCopies.centers_nonstationary D hF0 m)

theorem failure_search (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ) :
    DeterministicLineSearch.fromMetric (AffineWhitening.objective coordinateMatrix F)
      ((failureFamily D h m).x k) ((failureFamily D h m).H k) c₁ c₂ 5=
      (some ((failureFamily D h m).α k),trialHistory (phase k)) := by
  change DeterministicLineSearch.fromMetric (AffineWhitening.objective coordinateMatrix F)
    (point coordinateMatrix ((family D h m).x k)) (metric coordinateMatrix ((family D h m).H k)) _ _ _=_
  rw [fromMetric_equiv _ coordinateMatrix_invertible]
  exact copy_actual_search D h m k

theorem nonstrict_failure_search (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ) :
    NonStrictLineSearch.fromMetric (AffineWhitening.objective coordinateMatrix F)
      ((failureFamily D h m).x k) ((failureFamily D h m).H k) c₁ c₂ 5=
      (some ((failureFamily D h m).α k),trialHistory (phase k)) := by
  change NonStrictLineSearch.fromMetric (AffineWhitening.objective coordinateMatrix F)
    (point coordinateMatrix ((family D h m).x k)) (metric coordinateMatrix ((family D h m).H k)) _ _ _=_
  rw [nonstrict_fromMetric_equiv _ coordinateMatrix_invertible]
  exact copy_nonstrict_actual_search D h m k

theorem failure_strict_accept (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ) :
    AffineWhitening.objective coordinateMatrix F ((failureFamily D h m).x (k+1))<
      AffineWhitening.objective coordinateMatrix F ((failureFamily D h m).x k)+
      c₁*dot ((failureFamily D h m).g k)
        (bfgsStep ((failureFamily D h m).H k) ((failureFamily D h m).g k) ((failureFamily D h m).α k)) ∧
    c₂*dot ((failureFamily D h m).g k)
      (bfgsStep ((failureFamily D h m).H k) ((failureFamily D h m).g k) ((failureFamily D h m).α k))<
      dot ((failureFamily D h m).g (k+1))
        (bfgsStep ((failureFamily D h m).H k) ((failureFamily D h m).g k) ((failureFamily D h m).α k)) :=
  (strict_accept_equiv coordinateMatrix coordinateMatrix_invertible (family D h m) k).mpr
    (copy_strict_accept D h m k)

theorem failure_trial (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m k : ℕ) (q : Fin 9)
    (hq : trialPhase q=phase k) :
    DifferentiableAt ℝ (AffineWhitening.objective coordinateMatrix F)
      ((failureFamily D h m).x k+trialLength q •
        bfgsStep ((failureFamily D h m).H k) ((failureFamily D h m).g k) 1) ∧
    0<AffineWhitening.objective coordinateMatrix F
      ((failureFamily D h m).x k+trialLength q •
        bfgsStep ((failureFamily D h m).H k) ((failureFamily D h m).g k) 1) := by
  change DifferentiableAt ℝ (AffineWhitening.objective coordinateMatrix F)
    (point coordinateMatrix ((family D h m).x k)+trialLength q •
      bfgsStep (metric coordinateMatrix ((family D h m).H k))
        (gradient coordinateMatrix ((family D h m).g k)) 1) ∧ _
  rw [query_equiv _ coordinateMatrix_invertible]
  constructor
  · exact (differentiableAt_equiv coordinateMatrix coordinateMatrix_invertible F _).mpr
      (copy_trial_hasGradient D h m k q hq).differentiableAt
  · simpa only [failureFamily,run_x,run_H,run_g,query_equiv _ coordinateMatrix_invertible,
      AffineWhitening.objective,map_point _ coordinateMatrix_invertible] using
      copy_trial_value_positive D h m k q hq

theorem failure_trials_limit (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂) (m : ℕ)
    (q : ℕ → Fin 9) (hq : ∀ k, trialPhase (q k)=phase k) :
    Tendsto (fun k => (failureFamily D h m).x k+trialLength (q k) •
      bfgsStep ((failureFamily D h m).H k) ((failureFamily D h m).g k) 1) atTop (𝓝 (failureCenter m)) :=
  queries_limit coordinateMatrix coordinateMatrix_invertible _ _ _ _ _ (copy_trials_limit D h m q hq)

theorem failure_uniform_locality (D : LActualCopies.CopyData F) (h : Admissible c₁ c₂)
    (U : Set (Vec 2)) (hU : U∈𝓝 (0 : Vec 2)) :
    ∃ N : ℕ, ∀ m≥N, ∀ k, (failureFamily D h m).x k∈U ∧ ∀ q : Fin 9, trialPhase q=phase k →
      (failureFamily D h m).x k+trialLength q •
        bfgsStep ((failureFamily D h m).H k) ((failureFamily D h m).g k) 1∈U :=
  AffineWhitening.uniform_locality coordinateMatrix coordinateMatrix_invertible (family D h)
    trialLength (fun k q => trialPhase q=phase k) (copy_uniform_locality D h) U hU

theorem smooth_convex : ConvexOn ℝ univ smoothObjective :=
  (failureFamily LActualCopies.smoothData sourcePair 0).convex

theorem smooth_actual_hessian {x : Vec 2}
    (hfirst : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ smoothObjective z)
    (hsecond : DifferentiableAt ℝ (fderiv ℝ smoothObjective) x) :
    (RadialHessian.matrix smoothObjective x).IsSymm ∧ ∀ v,
      lowerConstant*sqNorm v≤dot v ((RadialHessian.matrix smoothObjective x).mulVec v) ∧
      dot v ((RadialHessian.matrix smoothObjective x).mulVec v)≤upperConstant*sqNorm v :=
  FiniteMaxHessian.finiteMax_actual_hessian_bounds upperConstant_pos.le smooth_convex smooth_strongConvex
    (smooth_localFiniteMax x) (fun i => (smooth_branch_regular i).2.2.1)
    (fun i => (smooth_branch_regular i).2.2.2) hfirst hsecond

end Whitening

/-! ## Targets -/

/-- The objective geometry of `LWhitening.ObjectiveGeometryTarget`, with the
strong-convexity constant as a parameter. -/
def ObjectiveGeometry (κ : ℝ) (F : Vec 2 → ℝ) : Prop :=
  ConvexOn ℝ univ F ∧ FixedNormal.EuclideanStrongConvexOn univ κ F ∧
    F 0=0 ∧ (∀ x, κ/2*sqNorm x≤F x) ∧ (∀ x, F x=0→x=0) ∧
    (∀ a, IsCompact {x | F x≤a}) ∧ Tendsto F (cocompact (Vec 2)) atTop ∧
    ¬DifferentiableAt ℝ F (0 : Vec 2)

theorem smooth_objective_geometry : ObjectiveGeometry lowerConstant smoothObjective :=
  ⟨smooth_convex,smooth_strongConvex,smooth_zero,smooth_lower,fun _ => smooth_unique_zero,
    smooth_compact_sublevel,smooth_coercive,smooth_nonsmooth_origin⟩

/-- The per-run clauses of the library's `FixedMetricFailureTarget` and
`IdentityFailureTarget`, for the constants `c₁`, `c₂`, with the non-strict and the
strict trace. -/
def FailureRun (F : Vec 2 → ℝ) (center : Vec 2) (limit c₁ c₂ : ℝ) (R : AdmissibleBFGSRun 2 F) : Prop :=
  R.c₁=c₁ ∧ R.c₂=c₂ ∧
    Tendsto R.x atTop (𝓝 center) ∧ Tendsto R.H atTop (𝓝 0) ∧
    Tendsto (fun k => F (R.x k)) atTop (𝓝 limit) ∧ 0<limit ∧
    (0 : Vec 2)∉ConvexSubdifferential.subdifferential F center ∧
    (∀ k, limit<F (R.x k) ∧ F (R.x (k+1))<F (R.x k) ∧ R.α k=length (phase k) ∧
      NonStrictLineSearch.fromMetric F (R.x k) (R.H k) c₁ c₂ 5=(some (R.α k),trialHistory (phase k)) ∧
      DeterministicLineSearch.fromMetric F (R.x k) (R.H k) c₁ c₂ 5=(some (R.α k),trialHistory (phase k)) ∧
      F (R.x (k+1))<F (R.x k)+c₁*dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) ∧
      c₂*dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k))<dot (R.g (k+1)) (bfgsStep (R.H k) (R.g k) (R.α k))) ∧
    (∀ k q, trialPhase q=phase k →
      DifferentiableAt ℝ F (R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1) ∧
      0<F (R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1)) ∧
    ∀ q : ℕ → Fin 9, (∀ k, trialPhase (q k)=phase k) →
      Tendsto (fun k => R.x k+trialLength (q k) • bfgsStep (R.H k) (R.g k) 1) atTop (𝓝 center)

/-- All accepted points and all queries of the `m`th run lie in any given neighbourhood
of the origin once `m` is large. -/
def UniformlyLocal {F : Vec 2 → ℝ} (R : ℕ → AdmissibleBFGSRun 2 F) : Prop :=
  ∀ U : Set (Vec 2), U∈𝓝 (0 : Vec 2) → ∃ N : ℕ, ∀ m≥N, ∀ k, (R m).x k∈U ∧
    ∀ q : Fin 9, trialPhase q=phase k →
      (R m).x k+trialLength q • bfgsStep ((R m).H k) ((R m).g k) 1∈U

/-- One family of starts, iterates, matrices and gradients, fixed before the constants,
consists of actual failing runs for every admissible pair `0<c₁≤1/3`, `c₁<c₂<1`. -/
def UniformFailureTarget (F : Vec 2 → ℝ) (B : Mat 2) (center : ℕ → Vec 2) : Prop :=
  ∃ x : ℕ → ℕ → Vec 2, ∃ H : ℕ → ℕ → Mat 2, ∃ g : ℕ → ℕ → Vec 2,
    (∀ m, H m 0=B) ∧ Tendsto (fun m => x m 0) atTop (𝓝 (0 : Vec 2)) ∧
    ∀ c₁ c₂ : ℝ, 0<c₁ → c₁≤1/3 → c₁<c₂ → c₂<1 →
      ∃ R : ℕ → AdmissibleBFGSRun 2 F,
        (∀ m, (R m).x=x m ∧ (R m).H=H m ∧ (R m).g=g m ∧
          FailureRun F (center m) ((scale m)^2*LEmbedding.offset) c₁ c₂ (R m)) ∧
        UniformlyLocal R

/-- Equation `art:lower_local_model` copies with one fixed SPD matrix, uniform in the
line-search constants. -/
theorem uniform_fixed_metric_failure (D : LActualCopies.CopyData F) (hF0 : F 0=0) :
    ∃ B : Mat 2, B.PosDef ∧ UniformFailureTarget F B LEmbedding.copyCenter := by
  refine ⟨initialMetric,initialMetric_posDef,fun m => (family D sourcePair m).x,
    fun m => (family D sourcePair m).H,fun m => (family D sourcePair m).g,fun _ => rfl,
    copy_starts_tendsto D sourcePair,?_⟩
  intro c₁ c₂ hc₁ hc₁' hc hc₂
  have h : Admissible c₁ c₂ := ⟨hc₁,hc₁',hc,hc₂⟩
  refine ⟨family D h,fun m => ⟨rfl,rfl,rfl,?_⟩,copy_uniform_locality D h⟩
  exact ⟨rfl,rfl,copy_point_limit D h m,copy_matrix_limit D h m,copy_value_limit D h m,
    mul_pos (sq_pos_of_pos (scale_pos m)) LEmbedding.offset_pos,LActualCopies.centers_nonstationary D hF0 m,
    fun k => ⟨copy_values_above_limit D h m k,(family D h m).objective_strict_decrease k,rfl,
      copy_nonstrict_actual_search D h m k,copy_actual_search D h m k,
      (copy_strict_accept D h m k).1,(copy_strict_accept D h m k).2⟩,
    fun k q hq => ⟨(copy_trial_hasGradient D h m k q hq).differentiableAt,copy_trial_value_positive D h m k q hq⟩,
    copy_trials_limit D h m⟩

/-- Identity-initialized copies after the one fixed whitening, uniform in the
line-search constants. -/
theorem uniform_identity_failure (D : LActualCopies.CopyData F) (hF0 : F 0=0) :
    UniformFailureTarget (AffineWhitening.objective coordinateMatrix F) 1 failureCenter := by
  refine ⟨fun m => (failureFamily D sourcePair m).x,fun m => (failureFamily D sourcePair m).H,
    fun m => (failureFamily D sourcePair m).g,failure_initial D sourcePair,failure_starts D sourcePair,?_⟩
  intro c₁ c₂ hc₁ hc₁' hc hc₂
  have h : Admissible c₁ c₂ := ⟨hc₁,hc₁',hc,hc₂⟩
  refine ⟨failureFamily D h,fun m => ⟨rfl,rfl,rfl,?_⟩,failure_uniform_locality D h⟩
  exact ⟨rfl,rfl,failure_point_limit D h m,failure_matrix_limit D h m,failure_value_limit D h m,
    mul_pos (sq_pos_of_pos (scale_pos m)) LEmbedding.offset_pos,failure_centers_nonstationary D hF0 m,
    fun k => ⟨failure_values_above D h m k,(failureFamily D h m).objective_strict_decrease k,rfl,
      nonstrict_failure_search D h m k,failure_search D h m k,
      (failure_strict_accept D h m k).1,(failure_strict_accept D h m k).2⟩,
    failure_trial D h m,failure_trials_limit D h m⟩

/-- Theorem `art:local-failure-lower` for every `0<c₁≤1/3`, `c₁<c₂<1` at once: one
objective (a maximum of four uniformly strongly convex `C^{1,1}` branches, the first
three not twice differentiable at the minimizer), one family of starts with `H₀=I`,
and actual failing runs for every admissible pair along the same iterates. -/
def UniformSmoothLocalFailureTarget : Prop :=
  0<lowerConstant ∧ lowerConstant≤upperConstant ∧ ObjectiveGeometry lowerConstant smoothObjective ∧
    (∀ i : Fin 4, ContDiff ℝ 1 (smoothBranch i) ∧
      FixedNormal.EuclideanStrongConvexOn univ lowerConstant (smoothBranch i) ∧
      (∀ z, HasFDerivAt (smoothBranch i) (gradientFunctional (smoothGradient i z)) z) ∧
      ∀ x y, sqNorm (smoothGradient i x-smoothGradient i y)≤upperConstant^2*sqNorm (x-y)) ∧
    (∀ x, smoothObjective x=Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 4 => smoothBranch i x)) ∧
    (∀ x : Vec 2, (∀ᶠ z in 𝓝 x, DifferentiableAt ℝ smoothObjective z) →
      DifferentiableAt ℝ (fderiv ℝ smoothObjective) x →
      (RadialHessian.matrix smoothObjective x).IsSymm ∧ ∀ v,
        lowerConstant*sqNorm v≤dot v ((RadialHessian.matrix smoothObjective x).mulVec v) ∧
        dot v ((RadialHessian.matrix smoothObjective x).mulVec v)≤upperConstant*sqNorm v) ∧
    (∀ i : Fin 3, ¬ DifferentiableAt ℝ (fderiv ℝ (smoothBranch i.castSucc)) (0 : Vec 2)) ∧
    UniformFailureTarget smoothObjective 1 failureCenter ∧ Tendsto failureCenter atTop (𝓝 (0 : Vec 2))

theorem uniformSmoothLocalFailure : UniformSmoothLocalFailureTarget :=
  ⟨lowerConstant_pos,constants_order,smooth_objective_geometry,smooth_branch_regular,
    smooth_objective_eq_max,fun _ => smooth_actual_hessian,branch_not_twice_differentiable_zero,
    uniform_identity_failure LActualCopies.smoothData LEmbedding.objective_zero,failure_centers_tendsto⟩

end BfgsVerification.LUniform
