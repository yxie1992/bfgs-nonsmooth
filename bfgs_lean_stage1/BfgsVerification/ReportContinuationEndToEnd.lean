import BfgsVerification.ReportContinuationTargets

namespace BfgsVerification

theorem radialInwardEquivalence : RadialInwardEquivalenceTarget := @BfgsVerification.RadialCertificate.radial_iff_inward_on_compact_sublevel

theorem localRadialCentralEquivalence : LocalRadialCentralEquivalenceTarget := @BfgsVerification.RadialCertificate.local_radial_iff_nested_central

theorem linearImageLifting : LinearImageLiftingTarget := @BfgsVerification.AffineProjection.projectRun_limit_lift

theorem nonuniqueSolutionBasin : NonuniqueSolutionBasinTarget := @BfgsVerification.TransportedCertificate.local_transported_certificate_basin_of_compact_solution_set

theorem linearCorrectionRate : LinearCorrectionRateTarget := @BfgsVerification.AdmissibleBFGSRun.compact_value_rate_of_linear_corrections

theorem eligiblePairRealizability : EligiblePairRealizabilityTarget := @BfgsVerification.TransportedCertificate.eligible_pair_realizable

theorem finiteSampleFeasibility : FiniteSampleFeasibilityTarget := @BfgsVerification.TransportedCertificate.positive_band_finite_sample_feasible
theorem homogeneousRates : HomogeneousRatesTarget := by
  intro n F R hF L hL
  exact ⟨fun N hN => R.homogeneous_sqrt_bound_of_lower_bound hF L hL hN,
    R.homogeneous_value_rate hF L hL, R.homogeneous_coercive_norm_rate hF⟩

theorem scalarGlobalCertificateNonnecessity : ScalarGlobalCertificateNonnecessityTarget := by
  exact ⟨ScalarCounterexamples.shiftedAbs_strongConvex,
    ScalarCounterexamples.shiftedAbs_minimum, ScalarCounterexamples.shiftedAbs_unique,
    ScalarCounterexamples.shifted_no_band_certificates,
    ScalarCounterexamples.shifted_scalar_run_converges,
    ScalarCounterexamples.shifted_actual_bfgs_converges⟩

theorem scalarLocalCertificateNonnecessity : ScalarLocalCertificateNonnecessityTarget := by
  exact ⟨AccumulatingKinks.objective_strongConvex, AccumulatingKinks.objective_coercive,
    AccumulatingKinks.objective_convex, AccumulatingKinks.objective_minimum,
    AccumulatingKinks.objective_unique, AccumulatingKinks.objective_sublevel_compact,
    fun _ hK => AccumulatingKinks.every_neighborhood_no_certificates hK,
    AccumulatingKinks.scalar_run_converges, AccumulatingKinks.actual_bfgs_converges⟩

end BfgsVerification
