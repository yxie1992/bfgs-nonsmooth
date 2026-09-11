import BfgsVerification.ReportAnalyticTargets

noncomputable section
namespace BfgsVerification

theorem actualFiniteMaxSubdifferential : ActualFiniteMaxSubdifferentialTarget := @ConvexSubdifferential.subdifferential_eq_active_convexHull

theorem localAffineCorrectness : LocalAffineCorrectnessTarget := @ConvexSubdifferential.local_affine_critical_correctness_original_family

theorem finiteMaxRadialBasin : FiniteMaxRadialBasinTarget := @FiniteMaxRadial.local_finite_max_basin

theorem euclideanResidualBasin : EuclideanResidualBasinTarget := @EuclideanResidual.local_matrix_euclidean_residual_basin

theorem finiteRayStep : FiniteRayStepTarget := @FiniteRayLineSearch.fullBFGS_step_exists

theorem unexcitedMetric : UnexcitedMetricTarget := @UnexcitedMetric.run_limits

theorem parabolicRadialBoundary : ParabolicRadialBoundaryTarget := @ParabolicRadialBoundary.converges_without_radial_secant

theorem algebraicSeedRoot : AlgebraicSeedRootTarget := @AlgebraicSeed.exact_closed_box

theorem algebraicSeedBounds : AlgebraicSeedBoundsTarget := @AlgebraicSeed.box_denominators_and_ratio

theorem affineRankLoss : AffineRankLossTarget :=
  ⟨AffineRankLoss.globally_affine_correct,AffineRankLoss.actual_origin_distance,
    fun _ h => AffineRankLoss.actual_vertical_distance h,
    AffineRankLoss.vertical_distance_tendsto_zero,AffineRankLoss.vertical_positive_gap_limit⟩

theorem algebraicJacobianCertificate : AlgebraicJacobianCertificateTarget :=
  ⟨AlgebraicSeed.actual_Jacobian,AlgebraicSeed.M_eq_J_inverse,
    AlgebraicSeed.source_inverse_Jacobian,AlgebraicSeed.source_residual,
    AlgebraicSeed.source_Jacobian_sup_bound⟩

theorem nuclearBoundary : NuclearBoundaryTarget := @NuclearSymmetric2.not_radial_secant_on_neighborhood

end BfgsVerification
