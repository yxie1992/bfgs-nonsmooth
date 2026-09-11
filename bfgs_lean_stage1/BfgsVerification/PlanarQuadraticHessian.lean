import BfgsVerification.PlanarQuadraticModel

/-! Actual second Fréchet derivatives of C's printed branches. -/
noncomputable section
open scoped BigOperators
open Matrix
namespace BfgsVerification.PlanarQuadraticExample

def hessianFunctional (i : Fin 3) : Vec 2 →L[ℝ] Vec 2 →L[ℝ] ℝ :=
  ∑ j : Fin 2, (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ).smulRight
    (hessianDiagonal i j • ContinuousLinearMap.proj j)

theorem hessianFunctional_apply (i : Fin 3) (x : Vec 2) :
    hessianFunctional i x=gradientFunctional ((hessian i).mulVec x) := by
  ext z
  simp only [hessianFunctional,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,
    gradientFunctional_apply,hessian,Matrix.mulVec_diagonal,dot]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem branch_second_hasFDerivAt (i : Fin 3) (x : Vec 2) :
    HasFDerivAt (fderiv ℝ (branch i)) (hessianFunctional i) x := by
  have he : fderiv ℝ (branch i)=fun z => hessianFunctional i z+gradientFunctional (linearPart i) := by
    funext z
    rw [(branch_hasGradient i z).fderiv]
    ext v
    simp only [hessianFunctional_apply,gradientFunctional_apply,ContinuousLinearMap.add_apply,
      gradient,dot,Pi.add_apply,add_mul,Finset.sum_add_distrib]
    ring
  rw [he]
  exact (hessianFunctional i).hasFDerivAt.add_const _

theorem branch_actual_hessian (i : Fin 3) (x : Vec 2) :
    RadialHessian.matrix (branch i) x=hessian i := by
  rw [RadialHessian.matrix,(branch_second_hasFDerivAt i x).fderiv]
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [RadialHessian.bilinearMatrix,hessianFunctional_apply,gradientFunctional_apply,
      hessian,Matrix.mulVec_diagonal,dot,Fin.sum_univ_two]

theorem branch_actual_hessian_bounds (i : Fin 3) (x : Vec 2) :
    (RadialHessian.matrix (branch i) x-1).PosSemidef ∧
      ((3 : ℝ) • (1 : Mat 2)-RadialHessian.matrix (branch i) x).PosSemidef := by
  rw [branch_actual_hessian]
  exact hessian_bounds i

end BfgsVerification.PlanarQuadraticExample
