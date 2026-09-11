import BfgsVerification.LIdentityTargets

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.LWhitening
open AffineWhitening AffineProjection EnergyIdentities

theorem constants_order : lowerConstant≤upperConstant := by
  have hm := (minEigenvalue_le initialMetric initialMetric_posDef.1 0).trans
    (le_maxEigenvalue initialMetric initialMetric_posDef.1 0)
  have hM := maxEigenvalue_pos initialMetric initialMetric_posDef
  dsimp [lowerConstant,upperConstant,LEmbedding.mu]
  nlinarith

theorem failure_centers_tendsto : Tendsto failureCenter atTop (𝓝 (0 : Vec 2)) := by
  simpa only [point,Matrix.mulVec_zero] using point_limit coordinateMatrix LEmbedding.copyCenter_tendsto

theorem smooth_convex : ConvexOn ℝ univ smoothObjective :=
  (failureFamily LActualCopies.smoothData 0).convex

theorem step_convex : ConvexOn ℝ univ stepObjective :=
  (failureFamily LActualCopies.stepData 0).convex

theorem smooth_localFiniteMax (x : Vec 2) :
    ConvexSubdifferential.LocalFiniteMax smoothObjective smoothBranch x :=
  Eventually.of_forall (fun z => LEmbedding.objective_isGreatest (coordinateMatrix.mulVec z))

theorem smooth_actual_hessian {x : Vec 2}
    (hfirst : ∀ᶠ z in 𝓝 x,DifferentiableAt ℝ smoothObjective z)
    (hsecond : DifferentiableAt ℝ (fderiv ℝ smoothObjective) x) :
    (RadialHessian.matrix smoothObjective x).IsSymm ∧ ∀v,
      lowerConstant*sqNorm v≤dot v ((RadialHessian.matrix smoothObjective x).mulVec v) ∧
      dot v ((RadialHessian.matrix smoothObjective x).mulVec v)≤upperConstant*sqNorm v :=
  FiniteMaxHessian.finiteMax_actual_hessian_bounds upperConstant_pos.le smooth_convex smooth_strongConvex
    (smooth_localFiniteMax x) (fun i => (smooth_branch_regular i).2.2.1)
    (fun i => (smooth_branch_regular i).2.2.2) hfirst hsecond

def fixedHessian : Mat 2 := LEmbedding.mu • initialMetric

theorem fixedHessian_posDef : fixedHessian.PosDef :=
  LNormalizedOracle.positive_smul_posDef initialMetric_posDef LEmbedding.mu_pos

theorem step_actual_hessian_bounds {x : Vec 2} (hd : DifferentiableAt ℝ stepObjective x) :
    DifferentiableAt ℝ (fderiv ℝ stepObjective) x ∧
    RadialHessian.matrix stepObjective x=fixedHessian ∧ ∀v,
      lowerConstant*sqNorm v≤dot v ((RadialHessian.matrix stepObjective x).mulVec v) ∧
      dot v ((RadialHessian.matrix stepObjective x).mulVec v)≤upperConstant*sqNorm v := by
  obtain ⟨hsecond,hmat⟩ := step_actual_hessian hd
  refine ⟨hsecond,hmat,?_⟩
  intro v
  have hb := actual_extreme_metric_bounds initialMetric initialMetric_posDef.1 v
  have hM := maxEigenvalue_pos initialMetric initialMetric_posDef
  have hn := sqNorm_nonneg v
  rw [hmat]
  change lowerConstant*sqNorm v≤ metricEnergy (LEmbedding.mu • initialMetric) v ∧
    metricEnergy (LEmbedding.mu • initialMetric) v≤upperConstant*sqNorm v
  rw [energy_smul_matrix]
  dsimp [lowerConstant,upperConstant,LEmbedding.mu]
  constructor <;> nlinarith [mul_nonneg hM.le hn]

def stepResidual (x : Vec 2) : ℝ := LStepEmbedding.residual (coordinateMatrix.mulVec x)
def stepAffine (j : LStepEmbedding.CountableIndex) : Vec 2 →L[ℝ] ℝ :=
  (LStepEmbedding.countableLinear j).comp (matrixCLM coordinateMatrix)

theorem step_residual_countable_max (x : Vec 2) :
    IsGreatest (range (fun j => stepAffine j x+LStepEmbedding.countableOffset j)) (stepResidual x) :=
  LStepEmbedding.residual_countable_max (coordinateMatrix.mulVec x)

theorem step_decomposition (x : Vec 2) :
    stepObjective x=metricEnergy fixedHessian x/2+stepResidual x := by
  change LEmbedding.mu/2*sqNorm (coordinateMatrix.mulVec x)+stepResidual x=_
  rw [fixedHessian,energy_smul_matrix]
  change LEmbedding.mu/2*sqNorm ((squareRoot initialMetric initialMetric_posDef).mulVec x)+_=_
  rw [squareRoot_sqNorm]
  ring

def ObjectiveGeometryTarget (F : Vec 2 → ℝ) : Prop :=
  ConvexOn ℝ univ F ∧ FixedNormal.EuclideanStrongConvexOn univ lowerConstant F ∧
    F 0=0 ∧ (∀x,lowerConstant/2*sqNorm x≤F x) ∧ (∀x,F x=0→x=0) ∧
    (∀a,IsCompact {x | F x≤a}) ∧ Tendsto F (cocompact (Vec 2)) atTop ∧
    ¬DifferentiableAt ℝ F (0 : Vec 2)

theorem smooth_objective_geometry : ObjectiveGeometryTarget smoothObjective :=
  ⟨smooth_convex,smooth_strongConvex,smooth_zero,smooth_lower,fun _ => smooth_unique_zero,
    smooth_compact_sublevel,smooth_coercive,smooth_nonsmooth_origin⟩

theorem step_objective_geometry : ObjectiveGeometryTarget stepObjective :=
  ⟨step_convex,step_strongConvex,step_zero,step_lower,fun _ => step_unique_zero,
    step_compact_sublevel,step_coercive,step_nonsmooth_origin⟩

def SmoothLocalFailureTarget : Prop :=
  0<lowerConstant ∧ lowerConstant≤upperConstant ∧ ObjectiveGeometryTarget smoothObjective ∧
    (∀i : Fin 4,ContDiff ℝ 1 (smoothBranch i) ∧
      FixedNormal.EuclideanStrongConvexOn univ lowerConstant (smoothBranch i) ∧
      (∀z,HasFDerivAt (smoothBranch i) (gradientFunctional (smoothGradient i z)) z) ∧
      ∀x y,sqNorm (smoothGradient i x-smoothGradient i y)≤upperConstant^2*sqNorm (x-y)) ∧
    (∀x,smoothObjective x=Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 4 => smoothBranch i x)) ∧
    (∀x : Vec 2,(∀ᶠ z in 𝓝 x,DifferentiableAt ℝ smoothObjective z) →
      DifferentiableAt ℝ (fderiv ℝ smoothObjective) x →
      (RadialHessian.matrix smoothObjective x).IsSymm ∧ ∀v,
        lowerConstant*sqNorm v≤dot v ((RadialHessian.matrix smoothObjective x).mulVec v) ∧
        dot v ((RadialHessian.matrix smoothObjective x).mulVec v)≤upperConstant*sqNorm v) ∧
    IdentityFailureTarget smoothObjective ∧ Tendsto failureCenter atTop (𝓝 (0 : Vec 2))

theorem smoothLocalFailure : SmoothLocalFailureTarget :=
  ⟨lowerConstant_pos,constants_order,smooth_objective_geometry,smooth_branch_regular,
    smooth_objective_eq_max,fun _ => smooth_actual_hessian,smoothIdentityFailure,failure_centers_tendsto⟩

def StepLocalFailureTarget : Prop :=
  0<lowerConstant ∧ lowerConstant≤upperConstant ∧ ObjectiveGeometryTarget stepObjective ∧
    fixedHessian.PosDef ∧
    (∀x : Vec 2,DifferentiableAt ℝ stepObjective x →
      DifferentiableAt ℝ (fderiv ℝ stepObjective) x ∧
      RadialHessian.matrix stepObjective x=fixedHessian ∧ ∀v,
        lowerConstant*sqNorm v≤dot v ((RadialHessian.matrix stepObjective x).mulVec v) ∧
        dot v ((RadialHessian.matrix stepObjective x).mulVec v)≤upperConstant*sqNorm v) ∧
    Countable LStepEmbedding.CountableIndex ∧
    (∀x,IsGreatest (range (fun j => stepAffine j x+LStepEmbedding.countableOffset j)) (stepResidual x)) ∧
    (∀x,stepObjective x=metricEnergy fixedHessian x/2+stepResidual x) ∧
    IdentityFailureTarget stepObjective ∧ Tendsto failureCenter atTop (𝓝 (0 : Vec 2))

theorem stepLocalFailure : StepLocalFailureTarget :=
  ⟨lowerConstant_pos,constants_order,step_objective_geometry,fixedHessian_posDef,
    fun _ => step_actual_hessian_bounds,LStepEmbedding.countable_index,step_residual_countable_max,
    step_decomposition,stepIdentityFailure,failure_centers_tendsto⟩

end BfgsVerification.LWhitening
