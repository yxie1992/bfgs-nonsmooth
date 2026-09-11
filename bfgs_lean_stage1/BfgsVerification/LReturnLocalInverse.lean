import BfgsVerification.LShapeSpectrum
import BfgsVerification.LReturnOrbitCore
import BfgsVerification.LBlockInvertibility

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.LReturnLocalInverse
open SeedOrbit LNormalizedReturn LShapeDerivative LShapeSpectrum LShapeSpectralAlgebra

theorem source_shape_determinant_positive :
    0 < jacobian seedC seedD 0 0*jacobian seedC seedD 1 1-
      jacobian seedC seedD 0 1*jacobian seedC seedD 1 0 := by
  obtain ⟨ls,lu,hs,hu,hsr,hur,hf⟩ := source_shape_roots
  have he := hf 0
  dsimp [characteristic] at he
  have hp : 0 < ls*lu := mul_pos (by linarith [hs.1]) (by linarith [hu.1])
  nlinarith

theorem actual_derivative_equiv (μ : ℝ) :
    ∃ E : State ≃L[ℝ] State, E.toContinuousLinearMap=fderiv ℝ (returnMap μ) seed :=
  LBlockInvertibility.continuousLinearEquiv_of_block (LReturnOrbitCore.actual_block μ)
    (inv_ne_zero source_ratio_pos_lt_one.1.ne') source_ratio_pos_lt_one.1.ne'
    source_shape_determinant_positive.ne'

/-- The literal actual return map has a smooth local two-sided inverse. This
assertion is independent of the constructive stable-orbit replacement. -/
theorem actual_local_inverse (μ : ℝ) :
    ∃ S : State → State, ContDiffAt ℝ ⊤ S seed ∧ S seed=seed ∧
      (∀ᶠ x in 𝓝 seed, S (returnMap μ x)=x) ∧
      (∀ᶠ y in 𝓝 seed, returnMap μ (S y)=y) := by
  have h := LBlockInvertibility.local_smooth_inverse_of_block
    (analytic_returnMap_seed μ).contDiffAt (analytic_returnMap_seed μ).differentiableAt.hasFDerivAt
    (LReturnOrbitCore.actual_block μ) (inv_ne_zero source_ratio_pos_lt_one.1.ne')
    source_ratio_pos_lt_one.1.ne' source_shape_determinant_positive.ne'
  rwa [seed_fixed μ] at h

end BfgsVerification.LReturnLocalInverse
