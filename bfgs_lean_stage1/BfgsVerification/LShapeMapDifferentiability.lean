import BfgsVerification.LShapeDerivative

noncomputable section
open scoped BigOperators Topology
open Matrix
namespace BfgsVerification.LShapeMapDifferentiability
open SeedOrbit LNormalizedReturn LShapeDerivative

def shapeProjection : State →L[ℝ] Vec 2 :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 2,ContinuousLinearMap.proj 3]

def jacobianMap (J : Mat 2) : Vec 2 →L[ℝ] Vec 2 :=
  ContinuousLinearMap.pi (fun i => gradientFunctional (J i))

theorem jacobianMap_apply (J : Mat 2) (v : Vec 2) : jacobianMap J v=J.mulVec v := by
  ext i
  simp [jacobianMap,gradientFunctional_apply,BfgsVerification.dot,Matrix.mulVec,dotProduct]

theorem boundary_affine (x : Vec 2) : boundary x=seed+shapeLift (x-center) := by
  ext i
  fin_cases i <;> simp [boundary,center,shapeLift,seed,LNormalizedReturn.seed,Matrix.cons_val]
  all_goals rfl

theorem boundary_hasFDerivAt (x : Vec 2) : HasFDerivAt boundary shapeLift x := by
  have h := (hasFDerivAt_const seed x).add
    (shapeLift.hasFDerivAt (x := x-center) |>.comp x ((hasFDerivAt_id x).sub_const center))
  simp only [zero_add,ContinuousLinearMap.comp_id] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall boundary_affine)

theorem shapeMap_hasFDerivAt :
    HasFDerivAt (shapeMap seedC seedD) (jacobianMap (jacobian seedC seedD)) center := by
  have hm := (analytic_returnMap_seed (0 : ℝ)).differentiableAt.hasFDerivAt
  have hm' : HasFDerivAt (returnMap (0 : ℝ)) (fderiv ℝ (returnMap 0) seed) (boundary center) := by
    rw [boundary_center]
    exact hm
  have h := (shapeProjection.hasFDerivAt (x := returnMap 0 (boundary center))).comp center
    (hm'.comp center (boundary_hasFDerivAt center))
  have he : (fun x => shapeProjection (returnMap 0 (boundary x)))=shapeMap seedC seedD := by
    funext x
    rw [shapeMap_eq_returnMap 0]
    ext i
    fin_cases i <;> rfl
  change HasFDerivAt (fun x => shapeProjection (returnMap 0 (boundary x))) _ center at h
  rw [he] at h
  convert h using 1
  ext v i
  have hv : v=v 0 • (Pi.single 0 1 : Vec 2)+v 1 • (Pi.single 1 1 : Vec 2) := by
    ext j
    fin_cases j <;> simp
  rw [hv]
  simp only [map_add,map_smul,ContinuousLinearMap.comp_apply,shapeProjection,jacobianMap,
    ContinuousLinearMap.pi_apply,ContinuousLinearMap.proj_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  fin_cases i
  · change _=v 0*(fderiv ℝ (returnMap 0) seed (shapeLift (Pi.single 0 1 : Vec 2))) 2+
      v 1*(fderiv ℝ (returnMap 0) seed (shapeLift (Pi.single 1 1 : Vec 2))) 2
    have h0 : (fderiv ℝ (returnMap 0) seed (shapeLift (Pi.single 0 1 : Vec 2))) 2=jacobian seedC seedD 0 0 := actual_shape_derivative 0 0 0
    have h1 : (fderiv ℝ (returnMap 0) seed (shapeLift (Pi.single 1 1 : Vec 2))) 2=jacobian seedC seedD 0 1 := actual_shape_derivative 0 0 1
    rw [h0,h1]
    simp [gradientFunctional_apply,BfgsVerification.dot,Fin.sum_univ_two]
  · change _=v 0*(fderiv ℝ (returnMap 0) seed (shapeLift (Pi.single 0 1 : Vec 2))) 3+
      v 1*(fderiv ℝ (returnMap 0) seed (shapeLift (Pi.single 1 1 : Vec 2))) 3
    have h0 : (fderiv ℝ (returnMap 0) seed (shapeLift (Pi.single 0 1 : Vec 2))) 3=jacobian seedC seedD 1 0 := actual_shape_derivative 0 1 0
    have h1 : (fderiv ℝ (returnMap 0) seed (shapeLift (Pi.single 1 1 : Vec 2))) 3=jacobian seedC seedD 1 1 := actual_shape_derivative 0 1 1
    rw [h0,h1]
    simp [gradientFunctional_apply,BfgsVerification.dot,Fin.sum_univ_two]

end BfgsVerification.LShapeMapDifferentiability
