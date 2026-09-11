import BfgsVerification.LReturnParameter
import BfgsVerification.LReturnOrbitCore

noncomputable section
open Matrix
namespace BfgsVerification.LReturnParameterBlock
open SeedOrbit LNormalizedReturn LReturnParameter LShapeDerivative LBlockSplitting

def Cleft : Vec 2 := ![(fderiv ℝ (returnMap 1) seed) shapeZero 0,
  (fderiv ℝ (returnMap 1) seed) shapeZero 1]
def Cright : Vec 2 := ![(fderiv ℝ (returnMap 1) seed) shapeOne 0,
  (fderiv ℝ (returnMap 1) seed) shapeOne 1]
def upperScale : Vec 2 := ![(fderiv ℝ (returnMap 1) seed) scaleUnit 0,
  (fderiv ℝ (returnMap 1) seed) scaleUnit 1]
def middleScale : Vec 2 := ![(fderiv ℝ (returnMap 1) seed) scaleUnit 2,
  (fderiv ℝ (returnMap 1) seed) scaleUnit 3]

theorem shape_zero_column (μ : ℝ) (i : Fin 5) (hi : i.val<4) :
    (fderiv ℝ (returnMap μ) seed) shapeZero i=(fderiv ℝ (returnMap 1) seed) shapeZero i := by
  simpa only [shapeZero_single] using derivative_horizontal_entries μ i 2 hi (by decide)

theorem shape_one_column (μ : ℝ) (i : Fin 5) (hi : i.val<4) :
    (fderiv ℝ (returnMap μ) seed) shapeOne i=(fderiv ℝ (returnMap 1) seed) shapeOne i := by
  simpa only [shapeOne_single] using derivative_horizontal_entries μ i 3 hi (by decide)

theorem scale_column (μ : ℝ) (i : Fin 5) (hi : i.val<4) :
    (fderiv ℝ (returnMap μ) seed) scaleUnit i=μ*(fderiv ℝ (returnMap 1) seed) scaleUnit i := by
  have he : scaleUnit=(Pi.single 4 1 : LNormalizedReturn.State) := by ext j; fin_cases j <;> simp [scaleUnit,Pi.single_apply]
  simpa only [he] using derivative_tau_column μ i hi

/-- The source's complete parameter-dependent block formula, with fixed
finite C/a/b blocks chosen at mu=1. -/
theorem actual_parameter_block (μ : ℝ) :
    BlockForm (fderiv ℝ (returnMap μ) seed) seedRatio⁻¹ seedRatio
      (jacobian seedC seedD 0 0) (jacobian seedC seedD 0 1)
      (jacobian seedC seedD 1 0) (jacobian seedC seedD 1 1)
      Cleft Cright (μ • upperScale) (μ • middleScale) := by
  have h := LReturnOrbitCore.actual_block μ
  rw [shape_zero_column μ 0 (by decide),shape_zero_column μ 1 (by decide),
    shape_one_column μ 0 (by decide),shape_one_column μ 1 (by decide),
    scale_column μ 0 (by decide),scale_column μ 1 (by decide),
    scale_column μ 2 (by decide),scale_column μ 3 (by decide)] at h
  exact h

end BfgsVerification.LReturnParameterBlock
