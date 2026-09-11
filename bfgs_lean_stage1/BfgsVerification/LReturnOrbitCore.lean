import BfgsVerification.LShapeDerivative
import BfgsVerification.LBlockStableOrbit
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.LReturnOrbitCore
open SeedOrbit LNormalizedReturn LShapeDerivative

@[simp] theorem pointLift_zero : pointLift ![1,0]=LBlockSplitting.pointZero := by
  ext i
  fin_cases i <;> rfl
@[simp] theorem pointLift_one : pointLift ![0,1]=LBlockSplitting.pointOne := by
  ext i
  fin_cases i <;> rfl

theorem shapeLift_zero : shapeLift (Pi.single 0 1 : Vec 2)=LBlockSplitting.shapeZero := by
  rw [shapeLift_single,LBlockSplitting.shapeZero_single]
  rfl
theorem shapeLift_one : shapeLift (Pi.single 1 1 : Vec 2)=LBlockSplitting.shapeOne := by
  rw [shapeLift_single,LBlockSplitting.shapeOne_single]
  rfl

theorem actual_block (μ : ℝ) :
    LBlockSplitting.BlockForm (fderiv ℝ (returnMap μ) seed) seedRatio⁻¹ seedRatio
      (jacobian seedC seedD 0 0) (jacobian seedC seedD 0 1)
      (jacobian seedC seedD 1 0) (jacobian seedC seedD 1 1)
      ![(fderiv ℝ (returnMap μ) seed) LBlockSplitting.shapeZero 0,
        (fderiv ℝ (returnMap μ) seed) LBlockSplitting.shapeZero 1]
      ![(fderiv ℝ (returnMap μ) seed) LBlockSplitting.shapeOne 0,
        (fderiv ℝ (returnMap μ) seed) LBlockSplitting.shapeOne 1]
      ![(fderiv ℝ (returnMap μ) seed) LBlockSplitting.scaleUnit 0,
        (fderiv ℝ (returnMap μ) seed) LBlockSplitting.scaleUnit 1]
      ![(fderiv ℝ (returnMap μ) seed) LBlockSplitting.scaleUnit 2,
        (fderiv ℝ (returnMap μ) seed) LBlockSplitting.scaleUnit 3] := by
  have h0 := return_derivative_point_columns μ ![1,0]
  have h1 := return_derivative_point_columns μ ![0,1]
  rw [pointLift_zero] at h0
  rw [pointLift_one] at h1
  have hb := LBlockSplitting.blockForm_of_columns h0 h1 (return_derivative_last_row μ)
  have hj00 : (fderiv ℝ (returnMap μ) seed) LBlockSplitting.shapeZero 2=jacobian seedC seedD 0 0 := by
    rw [← shapeLift_zero]
    exact actual_shape_derivative μ 0 0
  have hj01 : (fderiv ℝ (returnMap μ) seed) LBlockSplitting.shapeOne 2=jacobian seedC seedD 0 1 := by
    rw [← shapeLift_one]
    exact actual_shape_derivative μ 0 1
  have hj10 : (fderiv ℝ (returnMap μ) seed) LBlockSplitting.shapeZero 3=jacobian seedC seedD 1 0 := by
    rw [← shapeLift_zero]
    exact actual_shape_derivative μ 1 0
  have hj11 : (fderiv ℝ (returnMap μ) seed) LBlockSplitting.shapeOne 3=jacobian seedC seedD 1 1 := by
    rw [← shapeLift_one]
    exact actual_shape_derivative μ 1 1
  rwa [hj00,hj01,hj10,hj11] at hb

theorem return_hasStrictFDerivAt (μ : ℝ) :
    HasStrictFDerivAt (returnMap μ) (fderiv ℝ (returnMap μ) seed) seed :=
  ((analytic_returnMap_seed μ).contDiffAt (n := 1)).hasStrictFDerivAt le_rfl

/-- The remaining explicit spectral premises are discharged by the independent
kernel interval certificate; no orbit or invariant manifold is assumed. -/
theorem positive_orbit_of_shape_roots (μ : ℝ) {ls lu : ℝ}
    (hs0 : 0 < ls) (hsr : ls < seedRatio) (hu1 : 1 < lu) (hua : lu < seedRatio⁻¹)
    (hb : jacobian seedC seedD 0 1 ≠ 0)
    (hs : (ls-jacobian seedC seedD 0 0)*(ls-jacobian seedC seedD 1 1)=
      jacobian seedC seedD 0 1*jacobian seedC seedD 1 0)
    (hu : (lu-jacobian seedC seedD 0 0)*(lu-jacobian seedC seedD 1 1)=
      jacobian seedC seedD 0 1*jacobian seedC seedD 1 0)
    (V : Set State) (hV : V∈𝓝 seed) :
    ∃ w : ℕ → State, (∀ n, w n∈V) ∧ Tendsto w atTop (𝓝 seed) ∧ 0<scale (w 0) ∧
      ∀ n, w (n+1)=returnMap μ (w n) :=
  LBlockSplitting.positive_orbit_of_block (seed_fixed μ) (return_hasStrictFDerivAt μ)
    (seed_scale) (actual_block μ) source_ratio_pos_lt_one.1 source_ratio_pos_lt_one.2
    hs0 hsr hu1 hua hb hs hu V hV

end BfgsVerification.LReturnOrbitCore
