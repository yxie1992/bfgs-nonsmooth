import BfgsVerification.FoundationTargets
import BfgsVerification.ResidualSourceForm

/-! Exact inhabitants of the remaining Module M target propositions. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter

namespace BfgsVerification

theorem hessianInvariants : HessianInvariantTarget := by
  intro n F R k
  refine ⟨R.hessian_update k, R.annihilated_hessian_posSemidef k,
    R.annihilated_hessian_mul_displacement k, ?_⟩
  rw [R.update k]
  exact inverseBFGS_step_det_beta (R.positive_definite k) (R.gradient_nonzero k) _
    (R.alpha_pos k) (R.curvature_pos k)

theorem localization : LocalizationTarget := by
  intro n F hF xstar hmin huniq
  exact ⟨Localization.sublevel_compact hF xstar hmin huniq,
    fun _ hU => Localization.neighborhood_basin hF xstar hmin huniq hU⟩

theorem strictContourSteps : StrictContourTarget := by
  intro n F R hK ℓ hlim hlower hcontour
  exact R.steps_tendsto_zero_of_strict_contour hK ℓ hlim hlower hcontour

theorem referenceEnergy : ReferenceEnergyTarget := by
  intro n F R xstar
  exact ⟨R.fixed_reference_energy xstar, R.fixed_reference_energy_bound xstar⟩

theorem quadraticCorrectionConvergence : QuadraticCorrectionTarget := by
  intro n F R xstar hmin huniq C hcor
  exact R.convergence_of_quadratic_corrections_unique_minimizer xstar hmin huniq C hcor

theorem movingFrameCriterion : MovingFrameCriterionTarget := by
  rintro n F R G hG hg hd ⟨C⟩
  exact R.moving_frame_tail_criterion C.J C.V C.T C.P C.b C.invertible C.product
    C.transport C.m C.K C.L C.C C.m_pos C.K_pos C.L_nonneg C.visible C.correction
    C.product_bound C.inverse_bound G hG hg hd

theorem residualFrameCriterion : ResidualFrameCriterionTarget := by
  rintro n F R G hG hg hs ⟨C⟩
  exact R.residual_frames_on_tail_incompatible_source C.J G hG hg hs C.U C.orthonormal
    C.L C.m C.C₀ C.C_T C.C_R C.m_pos C.smooth C.V C.Z C.T C.b C.visible C.correction
    C.transport C.operator_bound C.residual_range C.residual_size

end BfgsVerification
