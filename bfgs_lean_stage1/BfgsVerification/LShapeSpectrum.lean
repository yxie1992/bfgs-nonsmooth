import BfgsVerification.LShapeIntervalCertificate
import BfgsVerification.LShapeSpectralAlgebra

noncomputable section
open scoped BigOperators Topology
open Matrix
namespace BfgsVerification.LShapeSpectrum
open SeedOrbit LNormalizedReturn LShapeDerivative LShapeSpectralAlgebra IntervalBounds

theorem box_of_original_ball {x : Vec 2} (hx : ‖x-AlgebraicSeed.center‖ ≤ AlgebraicSeed.radius) :
    Bounds (318481427627118/10^15) (x 0) (318481427627119/10^15) ∧
      Bounds (-1025232119675749/10^15) (x 1) (-1025232119675748/10^15) := by
  have hc : |(x 0)-AlgebraicSeed.center 0| ≤ AlgebraicSeed.radius :=
    (show |(x 0)-AlgebraicSeed.center 0| ≤ ‖x-AlgebraicSeed.center‖ from
      norm_le_pi_norm (x-AlgebraicSeed.center) 0).trans hx
  have hd : |(x 1)-AlgebraicSeed.center 1| ≤ AlgebraicSeed.radius :=
    (show |(x 1)-AlgebraicSeed.center 1| ≤ ‖x-AlgebraicSeed.center‖ from
      norm_le_pi_norm (x-AlgebraicSeed.center) 1).trans hx
  have hc' := abs_le.mp hc
  have hd' := abs_le.mp hd
  norm_num [AlgebraicSeed.center,AlgebraicSeed.radius] at hc' hd'
  unfold Bounds
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> linarith [hc'.1,hc'.2,hd'.1,hd'.2]

theorem source_box :
    Bounds (318481427627118/10^15) seedC (318481427627119/10^15) ∧
      Bounds (-1025232119675749/10^15) seedD (-1025232119675748/10^15) :=
  box_of_original_ball AlgebraicSeed.root_spec.1

theorem source_jacobian_bounds :
    Bounds (11123986249/10^10) (jacobian seedC seedD 0 0) (11123986253/10^10) ∧
    Bounds (6459701025/10^10) (jacobian seedC seedD 0 1) (6459701029/10^10) ∧
    Bounds (7515015701/10^10) (jacobian seedC seedD 1 0) (7515015708/10^10) ∧
    Bounds (4905136882/10^10) (jacobian seedC seedD 1 1) (4905136890/10^10) :=
  LShapeIntervalCertificate.jacobian_bounds source_box.1 source_box.2

theorem source_jacobian_offdiag_positive : 0 < jacobian seedC seedD 0 1 := by
  have h := source_jacobian_bounds.2.1.1
  linarith

theorem source_characteristic_signs :
    0 < characteristic (jacobian seedC seedD) (38/1000) ∧
    characteristic (jacobian seedC seedD) (39/1000) < 0 ∧
    characteristic (jacobian seedC seedD) (1564/1000) < 0 ∧
    0 < characteristic (jacobian seedC seedD) (1565/1000) :=
  signs_of_entry_bounds source_jacobian_bounds.1 source_jacobian_bounds.2.1
    source_jacobian_bounds.2.2.1 source_jacobian_bounds.2.2.2

theorem source_shape_roots :
    ∃ ls lu : ℝ, (38/1000 < ls ∧ ls < 39/1000) ∧
      (1564/1000 < lu ∧ lu < 1565/1000) ∧
      characteristic (jacobian seedC seedD) ls=0 ∧
      characteristic (jacobian seedC seedD) lu=0 ∧
      ∀ lam, characteristic (jacobian seedC seedD) lam=(lam-ls)*(lam-lu) :=
  two_roots_of_signs source_characteristic_signs.1 source_characteristic_signs.2.1
    source_characteristic_signs.2.2.1 source_characteristic_signs.2.2.2

theorem actual_middle_block (μ : ℝ) (i j : Fin 2) :
    (fderiv ℝ (returnMap μ) seed (Pi.single (shapeCoord j) 1 : State)) (shapeCoord i)=
      jacobian seedC seedD i j := by
  rw [← shapeLift_single]
  exact actual_shape_derivative μ i j

end BfgsVerification.LShapeSpectrum
