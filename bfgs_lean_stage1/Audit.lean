import BfgsVerification

/- Enumerate the compiled environment, rather than trusting a hand-maintained
list to cover every theorem. This is audit tooling, not a mathematical premise.
`collectAxioms` traverses proof dependencies, exactly as `#print axioms` does. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants.toList do
    if (`BfgsVerification).isPrefixOf name && info.isTheorem then
      let deps ← collectAxioms name
      let signature ← liftTermElabM do
        return (← Meta.ppExpr info.type).pretty
      let report := Json.mkObj [
        ("theorem", toJson name.toString),
        ("axioms", toJson (deps.map Name.toString)),
        ("signature", toJson signature)]
      logInfo m!"BFGS_AUDIT {report.compress}"
      count := count + 1
  logInfo m!"BFGS_AUDIT_COUNT {count}"

#print axioms BfgsVerification.CompressionAlgebra.gram_numerator_identity
#print axioms BfgsVerification.CompressionAlgebra.compression_scalar_identity
#print axioms BfgsVerification.CompressionAlgebra.compression_from_gram_relations
#print axioms BfgsVerification.CompressionAlgebra.compression_upper_bound
#print axioms BfgsVerification.CompressionAlgebra.rank_one_increment_upper_bound
#print axioms BfgsVerification.CompressionAlgebra.compressed_update_bound
#print axioms BfgsVerification.CompressionAlgebra.sum_compressed_bounds
#print axioms BfgsVerification.ScalarHierarchy.shift_identity
#print axioms BfgsVerification.ScalarHierarchy.weighted_nonneg
#print axioms BfgsVerification.ScalarHierarchy.first_le_weighted
#print axioms BfgsVerification.ScalarHierarchy.weighted_step
#print axioms BfgsVerification.ScalarHierarchy.hierarchy_tail_potentials
#print axioms BfgsVerification.ReciprocalGrowth.sum_prefix_tail
#print axioms BfgsVerification.ReciprocalGrowth.log_potential_telescope
#print axioms BfgsVerification.ReciprocalGrowth.tail_log_product_upper
#print axioms BfgsVerification.ReciprocalGrowth.global_log_product_upper
#print axioms BfgsVerification.ReciprocalGrowth.tail_potentials_force_log_growth
#print axioms BfgsVerification.ReciprocalGrowth.geometricMean_eq_exp_logMean
#print axioms BfgsVerification.ReciprocalGrowth.logMean_le_arithmeticMean
#print axioms BfgsVerification.ReciprocalGrowth.hierarchy_reciprocal_growth

-- Print the complete signature so the conditional premise remains visible.
#check @BfgsVerification.ReciprocalGrowth.hierarchy_reciprocal_growth

-- These are proposition DEFINITIONS, not exported theorem proofs.
#print BfgsVerification.PrincipalMinorHierarchyTarget
#print BfgsVerification.ReciprocalGrowthTarget
#print BfgsVerification.SuperquadraticReciprocalTarget
#print BfgsVerification.FullBFGSRun
#print BfgsVerification.principalSum
#print BfgsVerification.inverseBFGS
#print BfgsVerification.FullBFGSRun.q
#print BfgsVerification.FullBFGSRun.d
#print BfgsVerification.FullBFGSRun.beta

-- These terms must inhabit the exact original targets, with no extra premises.
example : BfgsVerification.PrincipalMinorHierarchyTarget := BfgsVerification.principalMinorHierarchy
example : BfgsVerification.ReciprocalGrowthTarget := BfgsVerification.reciprocalGrowth
example : BfgsVerification.SuperquadraticReciprocalTarget := BfgsVerification.superquadraticReciprocalGrowth
#check @BfgsVerification.finiteHorizon
#check @BfgsVerification.fullBFGS_normalizedHierarchy

-- Objective-level hypotheses and conclusions are printed for statement review.
#print BfgsVerification.gradientFunctional
#print BfgsVerification.AdmissibleBFGSRun
#print BfgsVerification.AdmissibleBFGSRun.q
#print BfgsVerification.AdmissibleBFGSRun.d
#print BfgsVerification.AdmissibleBFGSRun.beta
#print BfgsVerification.AdmissibleBFGSRun.initialSublevel
#print BfgsVerification.ObjectiveReciprocalGrowthTarget
#print BfgsVerification.ObjectiveLowerBoundGrowthTarget
#print BfgsVerification.CompactObjectiveGrowthTarget
#print BfgsVerification.ObjectiveFiniteHorizonBound
#print BfgsVerification.CompactObjectiveFiniteHorizonTarget

example : BfgsVerification.ObjectiveReciprocalGrowthTarget := BfgsVerification.objectiveReciprocalGrowth
example : BfgsVerification.ObjectiveLowerBoundGrowthTarget := BfgsVerification.objectiveLowerBoundGrowth
example : BfgsVerification.CompactObjectiveGrowthTarget := BfgsVerification.compactObjectiveGrowth
example : BfgsVerification.CompactObjectiveFiniteHorizonTarget := BfgsVerification.compactObjectiveFiniteHorizon
#check @BfgsVerification.fullBFGS_positive_invariants
#check @BfgsVerification.AdmissibleBFGSRun.toFullBFGSRun
#check @BfgsVerification.convex_gradient_bound_on_compact
#check @BfgsVerification.AdmissibleBFGSRun.summable_predicted_decreases_of_lower_bound
#check @BfgsVerification.objectiveFiniteHorizon_of_lower_bound
#check @BfgsVerification.objectiveGrowth_of_value_limit

-- Actual Hessian/energy definitions and exact frame hypotheses remain visible.
#print BfgsVerification.AdmissibleBFGSRun.hessian
#print BfgsVerification.AdmissibleBFGSRun.displacement
#print BfgsVerification.AdmissibleBFGSRun.gradientChange
#print BfgsVerification.AdmissibleBFGSRun.curvature
#print BfgsVerification.AdmissibleBFGSRun.referenceEnergy
#print BfgsVerification.AdmissibleBFGSRun.referencePairing
#print BfgsVerification.AdmissibleBFGSRun.referenceCorrection
#print BfgsVerification.EnergyIdentities.rectOuter
#print BfgsVerification.FrameBounds.OperatorSqBound
#print BfgsVerification.FrameNorms.euclideanOpNorm
#print BfgsVerification.SmoothSubspace.frobSq
#print BfgsVerification.ExactFrameCertificate
#print BfgsVerification.ResidualFrameCertificate
#print BfgsVerification.HessianInvariantTarget
#print BfgsVerification.LocalizationTarget
#print BfgsVerification.StrictContourTarget
#print BfgsVerification.ReferenceEnergyTarget
#print BfgsVerification.QuadraticCorrectionTarget
#print BfgsVerification.MovingFrameCriterionTarget
#print BfgsVerification.ResidualFrameCriterionTarget

example : BfgsVerification.HessianInvariantTarget := BfgsVerification.hessianInvariants
example : BfgsVerification.LocalizationTarget := BfgsVerification.localization
example : BfgsVerification.StrictContourTarget := BfgsVerification.strictContourSteps
example : BfgsVerification.ReferenceEnergyTarget := BfgsVerification.referenceEnergy
example : BfgsVerification.QuadraticCorrectionTarget := BfgsVerification.quadraticCorrectionConvergence
example : BfgsVerification.MovingFrameCriterionTarget := BfgsVerification.movingFrameCriterion
example : BfgsVerification.ResidualFrameCriterionTarget := BfgsVerification.residualFrameCriterion
#check @BfgsVerification.Localization.sphere_gap
#check @BfgsVerification.Localization.radial_lower_bound
#check @BfgsVerification.AdmissibleBFGSRun.objective_tendsto_min_of_negligible_corrections
#check @BfgsVerification.AdmissibleBFGSRun.objective_tendsto_min_of_quadratic_corrections
#check @BfgsVerification.AdmissibleBFGSRun.moving_frame_energy
#check @BfgsVerification.AdmissibleBFGSRun.moving_frame_tail_criterion
#check @BfgsVerification.AdmissibleBFGSRun.residual_frames_on_tail_incompatible_source
#check @BfgsVerification.FrameNorms.operatorSqBound_iff_opNorm_sq
#check @BfgsVerification.FrameNorms.orthonormal_matrix_for_subspace

-- First entire-report tranche: exact objective hypotheses and source conclusions.
#print BfgsVerification.argmin
#print BfgsVerification.euclideanVector
#print BfgsVerification.euclideanSolutionDistance
#print BfgsVerification.TransportedCertificate.EligiblePair
#print BfgsVerification.TransportedCertificate.stepProjector
#print BfgsVerification.TransportedCertificate.BandCertificate
#print BfgsVerification.TransportedCertificate.HasBandCertificates
#print BfgsVerification.Homogeneous.PositiveDegreeOne
#print BfgsVerification.ScalarMetricRun
#print BfgsVerification.RadialCertificate.HasRadialSecantBounds
#print BfgsVerification.TransportedCertificateTarget
#print BfgsVerification.HomogeneousDichotomyTarget
#print BfgsVerification.ScalarMetricConvergenceTarget
#print BfgsVerification.ScalarBFGSConvergenceTarget
#print BfgsVerification.RadialCertificateConvergenceTarget
example : BfgsVerification.TransportedCertificateTarget := BfgsVerification.transportedCertificateConvergence
example : BfgsVerification.HomogeneousDichotomyTarget := BfgsVerification.homogeneousDichotomy
example : BfgsVerification.ScalarMetricConvergenceTarget := BfgsVerification.scalarMetricConvergence
example : BfgsVerification.ScalarBFGSConvergenceTarget := BfgsVerification.scalarBFGSConvergence
example : BfgsVerification.RadialCertificateConvergenceTarget := BfgsVerification.radialCertificateConvergence
#check @BfgsVerification.AdmissibleBFGSRun.accepted_pair_eligible
#check @BfgsVerification.AdmissibleBFGSRun.certificate_trace_step
#check @BfgsVerification.AdmissibleBFGSRun.homogeneous_global_gradient_bound
#check @BfgsVerification.AdmissibleBFGSRun.homogeneous_coercive_iterates_zero
#check @BfgsVerification.AdmissibleBFGSRun.toScalarMetricRun
#check @BfgsVerification.AdmissibleBFGSRun.radial_correction_bound
#check @BfgsVerification.global_minimum_of_zero_gradient

-- Second report tranche: objective geometry and equivalences.
#print BfgsVerification.Homogeneous.finiteMaxLinear
#print BfgsVerification.Homogeneous.recurrentValues
#print BfgsVerification.Homogeneous.commonTilt
#print BfgsVerification.TransportedCertificate.VisibilitySecantCertificate
#print BfgsVerification.TransportedCertificate.PotentialBandCertificate
#print BfgsVerification.TransportedCertificate.ScalarQuotientBound
#print BfgsVerification.TransportedCertificate.ScalarEligibleLipschitz
#print BfgsVerification.TransportedCertificate.HasShellCertificates
#print BfgsVerification.RadialCertificate.HasInterceptBounds
#print BfgsVerification.RadialCertificate.HasInwardTaylorBounds
#print BfgsVerification.CertificateNormalizationTarget
#print BfgsVerification.RecurrentAffineHullTarget
#print BfgsVerification.MaxLinearAffineEscapeTarget
#print BfgsVerification.RadialInterceptEquivalenceTarget
#print BfgsVerification.InwardCertificateConvergenceTarget
#print BfgsVerification.IncomingJumpObstructionTarget
#print BfgsVerification.ScalarCertificateCharacterizationTarget
example : BfgsVerification.CertificateNormalizationTarget := BfgsVerification.certificateNormalization
example : BfgsVerification.RecurrentAffineHullTarget := BfgsVerification.recurrentAffineHull
example : BfgsVerification.MaxLinearAffineEscapeTarget := BfgsVerification.maxLinearAffineEscape
example : BfgsVerification.RadialInterceptEquivalenceTarget := BfgsVerification.radialInterceptEquivalence
example : BfgsVerification.InwardCertificateConvergenceTarget := BfgsVerification.inwardCertificateConvergence
example : BfgsVerification.IncomingJumpObstructionTarget := BfgsVerification.incomingJumpObstruction
example : BfgsVerification.ScalarCertificateCharacterizationTarget := BfgsVerification.scalarCertificateCharacterization
#check @BfgsVerification.TransportedCertificate.BandCertificate.normalize_field
#check @BfgsVerification.TransportedCertificate.BandCertificate.normalize_budget
#check @BfgsVerification.TransportedCertificate.PotentialBandCertificate.absorb_constants
#check @BfgsVerification.TransportedCertificate.local_transported_certificate_basin
#check @BfgsVerification.AdmissibleBFGSRun.transported_shell_certificate_convergence_on_sublevel
#check @BfgsVerification.TransportedCertificate.projected_transport_iff_perpendicular
#check @BfgsVerification.AdmissibleBFGSRun.commonTilt_value_escape
#check @BfgsVerification.AdmissibleBFGSRun.maxLinear_recurrent_gradient_cardinality
#check @BfgsVerification.TransportedCertificate.basis_limit_no_visibility_secant
#check @BfgsVerification.RadialCertificate.inward_error_le_of_pair_radial
#check @BfgsVerification.convex_gradients_tendsto_at_differentiable

-- Third report tranche: radial equivalences, lifting, rates and explicit examples.
#print BfgsVerification.RadialCertificate.HasNestedCentralBounds
#print BfgsVerification.AffineProjection.FullRowRank
#print BfgsVerification.AffineProjection.compress
#print BfgsVerification.AffineProjection.lift
#print BfgsVerification.AffineProjection.fiberPoint
#print BfgsVerification.AffineProjection.projectRun
#print BfgsVerification.AdmissibleBFGSRun.valueCorrectionBudget
#print BfgsVerification.TransportedCertificate.realizingMetric
#print BfgsVerification.ScalarCounterexamples.shiftedAbs
#print BfgsVerification.AccumulatingKinks.knot
#print BfgsVerification.AccumulatingKinks.kinkSum
#print BfgsVerification.AccumulatingKinks.objective
#print BfgsVerification.RadialInwardEquivalenceTarget
example : BfgsVerification.RadialInwardEquivalenceTarget := BfgsVerification.radialInwardEquivalence
#print BfgsVerification.LocalRadialCentralEquivalenceTarget
example : BfgsVerification.LocalRadialCentralEquivalenceTarget := BfgsVerification.localRadialCentralEquivalence
#print BfgsVerification.LinearImageLiftingTarget
example : BfgsVerification.LinearImageLiftingTarget := BfgsVerification.linearImageLifting
#print BfgsVerification.NonuniqueSolutionBasinTarget
example : BfgsVerification.NonuniqueSolutionBasinTarget := BfgsVerification.nonuniqueSolutionBasin
#print BfgsVerification.LinearCorrectionRateTarget
example : BfgsVerification.LinearCorrectionRateTarget := BfgsVerification.linearCorrectionRate
#print BfgsVerification.HomogeneousRatesTarget
example : BfgsVerification.HomogeneousRatesTarget := BfgsVerification.homogeneousRates
#print BfgsVerification.ScalarGlobalCertificateNonnecessityTarget
example : BfgsVerification.ScalarGlobalCertificateNonnecessityTarget := BfgsVerification.scalarGlobalCertificateNonnecessity
#print BfgsVerification.ScalarLocalCertificateNonnecessityTarget
example : BfgsVerification.ScalarLocalCertificateNonnecessityTarget := BfgsVerification.scalarLocalCertificateNonnecessity
#print BfgsVerification.EligiblePairRealizabilityTarget
example : BfgsVerification.EligiblePairRealizabilityTarget := BfgsVerification.eligiblePairRealizability
#print BfgsVerification.FiniteSampleFeasibilityTarget
example : BfgsVerification.FiniteSampleFeasibilityTarget := BfgsVerification.finiteSampleFeasibility
#check @BfgsVerification.RadialCertificate.inward_iff_intercept_on_compact_sublevel
#check @BfgsVerification.RadialCertificate.central_of_radial_on_sublevel
#check @BfgsVerification.RadialCertificate.radial_of_central_on_smaller_sublevel
#check @BfgsVerification.AffineProjection.matrix_lift_invariant
#check @BfgsVerification.AffineProjection.fiberPoint_minimizer_unique
#check @BfgsVerification.AdmissibleBFGSRun.homogeneous_weighted_sum_bound
#check @BfgsVerification.Homogeneous.coercive_euclidean_lower_bound
#check @BfgsVerification.AdmissibleBFGSRun.compact_value_log_orders_of_correction_bound
#check @BfgsVerification.HarmonicRates.self_budget_value_log_orders
#check @BfgsVerification.ScalarCounterexamples.crossing_quotient_tendsto
#check @BfgsVerification.AccumulatingKinks.crossing_quotient_tendsto
#check @BfgsVerification.AccumulatingKinks.series_uniform_on_compact
#check @BfgsVerification.AccumulatingKinks.objective_coercive
