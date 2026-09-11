import BfgsVerification.AffineWhiteningHessian
import BfgsVerification.LActualCopyTargets

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.LWhitening
open AffineWhitening AffineProjection

/-- This is the same one actual source initial matrix for every scale and both
literal embeddings. No new matrix is selected between starts. -/
def initialMetric : Mat 2 := LSeedCopies.run.H 0

theorem initialMetric_posDef : initialMetric.PosDef := LSeedCopies.run.initial_posDef

def coordinateMatrix : Mat 2 := squareRoot initialMetric initialMetric_posDef

theorem coordinateMatrix_square : coordinateMatrix*coordinateMatrix=initialMetric :=
  squareRoot_square _ _
theorem coordinateMatrix_transpose : coordinateMatrixᵀ=coordinateMatrix := squareRoot_transpose _ _
theorem coordinateMatrix_invertible : coordinateMatrix.det≠0 := squareRoot_det_ne_zero _ _

def lowerConstant : ℝ := LEmbedding.mu*minEigenvalue initialMetric initialMetric_posDef.1
def upperConstant : ℝ := 512*maxEigenvalue initialMetric initialMetric_posDef.1

theorem lowerConstant_pos : 0<lowerConstant := mul_pos LEmbedding.mu_pos (minEigenvalue_pos initialMetric initialMetric_posDef)
theorem upperConstant_pos : 0<upperConstant := mul_pos (by norm_num) (maxEigenvalue_pos initialMetric initialMetric_posDef)

def smoothObjective : Vec 2 → ℝ := objective coordinateMatrix LEmbedding.objective
def stepObjective : Vec 2 → ℝ := objective coordinateMatrix LStepEmbedding.objective
def smoothBranch (i : Fin 4) : Vec 2 → ℝ := objective coordinateMatrix (LEmbedding.branch i)
def smoothGradient (i : Fin 4) (z : Vec 2) : Vec 2 :=
  gradient coordinateMatrix (LEmbedding.branchGradient i (coordinateMatrix.mulVec z))

theorem smooth_branch_regular (i : Fin 4) :
    ContDiff ℝ 1 (smoothBranch i) ∧
    FixedNormal.EuclideanStrongConvexOn univ lowerConstant (smoothBranch i) ∧
    (∀z,HasFDerivAt (smoothBranch i) (gradientFunctional (smoothGradient i z)) z) ∧
    ∀x y,sqNorm (smoothGradient i x-smoothGradient i y) ≤ upperConstant^2*sqNorm (x-y) := by
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

theorem step_strongConvex : FixedNormal.EuclideanStrongConvexOn univ lowerConstant stepObjective :=
  strongConvex_whitening _ initialMetric_posDef LEmbedding.mu_pos.le LStepEmbedding.objective_strongConvex

theorem smooth_zero : smoothObjective 0=0 := by simpa [smoothObjective,objective] using LEmbedding.objective_zero
theorem step_zero : stepObjective 0=0 := by simpa [stepObjective,objective] using LStepEmbedding.objective_zero

theorem smooth_unique_zero {z : Vec 2} (hz : smoothObjective z=0) : z=0 :=
  zero_unique_whitening coordinateMatrix coordinateMatrix_invertible
    (fun _ => LEmbedding.objective_unique_zero) hz

theorem step_unique_zero {z : Vec 2} (hz : stepObjective z=0) : z=0 :=
  zero_unique_whitening coordinateMatrix coordinateMatrix_invertible
    (fun _ => LStepEmbedding.objective_unique_zero) hz

theorem smooth_compact_sublevel (a : ℝ) : IsCompact {z | smoothObjective z ≤ a} :=
  sublevels_compact_whitening coordinateMatrix coordinateMatrix_invertible LEmbedding.objective_sublevels_compact a

theorem step_compact_sublevel (a : ℝ) : IsCompact {z | stepObjective z ≤ a} :=
  sublevels_compact_whitening coordinateMatrix coordinateMatrix_invertible LStepEmbedding.objective_sublevels_compact a

theorem smooth_coercive : Tendsto smoothObjective (cocompact (Vec 2)) atTop :=
  coercive_of_compact_sublevels smooth_compact_sublevel

theorem step_coercive : Tendsto stepObjective (cocompact (Vec 2)) atTop :=
  coercive_of_compact_sublevels step_compact_sublevel

theorem smooth_lower (z : Vec 2) : lowerConstant/2*sqNorm z ≤ smoothObjective z := by
  have hs := mul_le_mul_of_nonneg_left (squareRoot_norm_bounds initialMetric initialMetric_posDef z).1
    (div_nonneg LEmbedding.mu_pos.le (by norm_num : (0 : ℝ) ≤ 2))
  have hb := LEmbedding.objective_lower (coordinateMatrix.mulVec z)
  change LEmbedding.mu/2*(minEigenvalue initialMetric initialMetric_posDef.1*sqNorm z) ≤
    LEmbedding.mu/2*sqNorm (coordinateMatrix.mulVec z) at hs
  change (LEmbedding.mu*minEigenvalue initialMetric initialMetric_posDef.1)/2*sqNorm z ≤
    LEmbedding.objective (coordinateMatrix.mulVec z)
  nlinarith

theorem step_lower (z : Vec 2) : lowerConstant/2*sqNorm z ≤ stepObjective z := by
  have hs := mul_le_mul_of_nonneg_left (squareRoot_norm_bounds initialMetric initialMetric_posDef z).1
    (div_nonneg LEmbedding.mu_pos.le (by norm_num : (0 : ℝ) ≤ 2))
  have hb := LStepEmbedding.objective_lower (coordinateMatrix.mulVec z)
  change LEmbedding.mu/2*(minEigenvalue initialMetric initialMetric_posDef.1*sqNorm z) ≤
    LEmbedding.mu/2*sqNorm (coordinateMatrix.mulVec z) at hs
  change (LEmbedding.mu*minEigenvalue initialMetric initialMetric_posDef.1)/2*sqNorm z ≤
    LStepEmbedding.objective (coordinateMatrix.mulVec z)
  nlinarith

theorem smooth_nonsmooth_origin : ¬DifferentiableAt ℝ smoothObjective (0 : Vec 2) := by
  have he := differentiableAt_equiv coordinateMatrix coordinateMatrix_invertible LEmbedding.objective 0
  simpa only [point,Matrix.mulVec_zero,smoothObjective] using
    mt he.mp LEmbedding.objective_not_differentiable_zero

theorem step_nonsmooth_origin : ¬DifferentiableAt ℝ stepObjective (0 : Vec 2) := by
  have he := differentiableAt_equiv coordinateMatrix coordinateMatrix_invertible LStepEmbedding.objective 0
  simpa only [point,Matrix.mulVec_zero,stepObjective] using
    mt he.mp LStepEmbedding.objective_not_differentiable_zero

/-- The actual Hessian exists at every differentiability point of the literal
step embedding after whitening and is the fixed matrix mu times H0. -/
theorem step_actual_hessian {z : Vec 2} (hd : DifferentiableAt ℝ stepObjective z) :
    DifferentiableAt ℝ (fderiv ℝ stepObjective) z ∧
    RadialHessian.matrix stepObjective z=LEmbedding.mu • initialMetric := by
  have hF : DifferentiableAt ℝ LStepEmbedding.objective (coordinateMatrix.mulVec z) :=
    (linearEquiv coordinateMatrix coordinateMatrix_invertible).comp_right_differentiableAt_iff.mp hd
  obtain ⟨hsecond,hM⟩ := LStepEmbedding.objective_actual_hessian hF
  refine ⟨(second_hasFDerivAt coordinateMatrix coordinateMatrix_invertible _ z _ hsecond).differentiableAt,?_⟩
  rw [stepObjective,hessian_formula _ coordinateMatrix_invertible _ z hsecond.differentiableAt,hM,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,coordinateMatrix_transpose,coordinateMatrix_square]

end BfgsVerification.LWhitening
