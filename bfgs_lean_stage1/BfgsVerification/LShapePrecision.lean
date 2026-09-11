import BfgsVerification.LShapeFineCertificate
import BfgsVerification.LShapeMapDifferentiability
import BfgsVerification.LShapeSpectrum

noncomputable section
open Matrix
namespace BfgsVerification.LShapePrecision
open SeedOrbit LShapeDerivative IntervalBounds LShapeMapDifferentiability

theorem fine_box_of_original_ball {x : Vec 2}
    (hx : ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius) :
    Bounds (318481427627118630646451312501/10^30) (x 0)
      (318481427627118630646451312504/10^30) ∧
    Bounds (-1025232119675748725481350870015/10^30) (x 1)
      (-1025232119675748725481350870012/10^30) := by
  have hc : |x 0-AlgebraicSeed.center 0|≤AlgebraicSeed.radius :=
    (show |x 0-AlgebraicSeed.center 0|≤‖x-AlgebraicSeed.center‖ from
      norm_le_pi_norm (x-AlgebraicSeed.center) 0).trans hx
  have hd : |x 1-AlgebraicSeed.center 1|≤AlgebraicSeed.radius :=
    (show |x 1-AlgebraicSeed.center 1|≤‖x-AlgebraicSeed.center‖ from
      norm_le_pi_norm (x-AlgebraicSeed.center) 1).trans hx
  obtain ⟨hc0,hc1⟩ := abs_le.mp hc
  obtain ⟨hd0,hd1⟩ := abs_le.mp hd
  norm_num [AlgebraicSeed.center,AlgebraicSeed.radius] at hc0 hc1 hd0 hd1
  unfold Bounds
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> linarith

def display20 : Mat 2 :=
  !![111239862507328953465/10^20,64597010273159772922/10^20;
     75150157042749849873/10^20,49051368858317536674/10^20]

def originalDisplay15 : Mat 2 :=
  !![1112398625073290/10^15,645970102731598/10^15;
     751501570427499/10^15,490513688583175/10^15]

def correctedDisplay15 : Mat 2 :=
  !![1112398625073290/10^15,645970102731598/10^15;
     751501570427498/10^15,490513688583175/10^15]

def actualEntry (i j : Fin 2) : ℝ :=
  (fderiv ℝ (shapeMap seedC seedD) LShapeDerivative.center) (Pi.single j 1) i

theorem actualEntry_eq_jacobian (i j : Fin 2) : actualEntry i j=jacobian seedC seedD i j := by
  unfold actualEntry
  rw [shapeMap_hasFDerivAt.fderiv,jacobianMap_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.single_apply]

theorem jacobian_precision_on_original_ball {x : Vec 2}
    (hx : ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius) (i j : Fin 2) :
    |jacobian (x 0) (x 1) i j-display20 i j|≤1/(2*10^20) := by
  obtain ⟨hc,hd⟩ := fine_box_of_original_ball hx
  have hc' : Bounds (318481427627118630646451312501/1000000000000000000000000000000) (x 0)
      (39810178453389828830806414063/125000000000000000000000000000) := by
    convert hc using 1 <;> norm_num
  have hd' : Bounds (-205046423935149745096270174003/200000000000000000000000000000) (x 1)
      (-256308029918937181370337717503/250000000000000000000000000000) := by
    convert hd using 1 <;> norm_num
  obtain ⟨⟨h00l,h00u⟩,⟨h01l,h01u⟩,⟨h10l,h10u⟩,⟨h11l,h11u⟩⟩ :=
    LShapeFineCertificate.jacobian_bounds hc' hd'
  rw [abs_le]
  fin_cases i <;> fin_cases j <;>
    norm_num [display20] at * <;> constructor <;> linarith

theorem actual_precision (i j : Fin 2) :
    |actualEntry i j-display20 i j|≤1/(2*10^20) := by
  rw [actualEntry_eq_jacobian]
  exact jacobian_precision_on_original_ball AlgebraicSeed.root_spec.1 i j

theorem corrected_display_error (i j : Fin 2) :
    |actualEntry i j-correctedDisplay15 i j|<1/(2*10^15) := by
  have hp := abs_le.mp (actual_precision i j)
  rw [abs_lt]
  fin_cases i <;> fin_cases j <;>
    norm_num [display20,correctedDisplay15] at * <;> constructor <;> linarith

theorem original_display_error (i j : Fin 2) :
    |actualEntry i j-originalDisplay15 i j|<1/10^15 := by
  have hp := abs_le.mp (actual_precision i j)
  rw [abs_lt]
  fin_cases i <;> fin_cases j <;>
    norm_num [display20,originalDisplay15] at * <;> constructor <;> linarith

theorem original_lower_left_exceeds_half_unit :
    1/(2*10^15)<originalDisplay15 1 0-actualEntry 1 0 := by
  have hp := abs_le.mp (actual_precision 1 0)
  norm_num [display20,originalDisplay15] at *
  linarith

/-- Literal display scope: actual derivative entries, a uniform original-box
enclosure, corrected fifteen-decimal entries, and the printed lower-left error. -/
def ActualJacobianPrecisionTarget : Prop :=
  (∀x : Vec 2, ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius → ∀i j : Fin 2,
    |jacobian (x 0) (x 1) i j-display20 i j|≤1/(2*10^20)) ∧
  (∀i j : Fin 2,|actualEntry i j-display20 i j|≤1/(2*10^20)) ∧
  (∀i j : Fin 2,|actualEntry i j-correctedDisplay15 i j|<1/(2*10^15)) ∧
  (∀i j : Fin 2,|actualEntry i j-originalDisplay15 i j|<1/10^15) ∧
  1/(2*10^15)<originalDisplay15 1 0-actualEntry 1 0

theorem actualJacobianPrecision : ActualJacobianPrecisionTarget :=
  ⟨fun _ hx => jacobian_precision_on_original_ball hx,actual_precision,
    corrected_display_error,original_display_error,original_lower_left_exceeds_half_unit⟩

end BfgsVerification.LShapePrecision
