import BfgsVerification

open Lean Elab Command

run_elab do
  for name in [`BfgsVerification.AdmissibleBFGSRun.positive_invariants,
    `BfgsVerification.AdmissibleBFGSRun.predicted_decrease_bounds,
    `BfgsVerification.AdmissibleBFGSRun.summable_predicted_decreases_of_lower_bound,
    `BfgsVerification.convex_supporting_bound_on_compact,
    `BfgsVerification.hessianUpdate,
    `BfgsVerification.annihilatedMatrix_posSemidef,
    `BfgsVerification.annihilatedMatrix_mul_step,
    `BfgsVerification.Localization.sphere_gap,
    `BfgsVerification.Localization.radial_lower_bound,
    `BfgsVerification.Localization.sublevel_compact,
    `BfgsVerification.localization,
    `BfgsVerification.AdmissibleBFGSRun.steps_tendsto_zero_of_strict_contour,
    `BfgsVerification.principalSum_one,
    `BfgsVerification.principalSum_top,
    `BfgsVerification.principalSum_diagonal,
    `BfgsVerification.PrincipalInvariance.principalSum_orthogonal_conjugate,
    `BfgsVerification.CompressionDeterminant.compression_det,
    `BfgsVerification.metricGram_det_append_one,
    `BfgsVerification.metricGram_det_append_two,
    `BfgsVerification.CompressionDeterminant.compression_add_rank_one_det,
    `BfgsVerification.compressed_energy_le,
    `BfgsVerification.BFGSCompression.compressed_inverseBFGS_bound,
    `BfgsVerification.principalMinorHierarchy,
    `BfgsVerification.inverseBFGS_step_det_beta,
    `BfgsVerification.principalGramSumIdentity,
    `BfgsVerification.fullBFGS_normalizedHierarchy,
    `BfgsVerification.ScalarHierarchy.weighted_step,
    `BfgsVerification.ReciprocalGrowth.tail_log_product_upper,
    `BfgsVerification.reciprocalGrowth,
    `BfgsVerification.finiteHorizon,
    `BfgsVerification.superquadraticReciprocalGrowth,
    `BfgsVerification.QuantitativeGrowth.hierarchy_fixed_tail_lower_eventually,
    `BfgsVerification.sharpPrincipalPotential,
    `BfgsVerification.AdmissibleBFGSRun.fixed_reference_energy,
    `BfgsVerification.AdmissibleBFGSRun.fixed_reference_energy_bound,
    `BfgsVerification.AdmissibleBFGSRun.objective_tendsto_min_of_negligible_corrections,
    `BfgsVerification.AdmissibleBFGSRun.objective_tendsto_min_of_quadratic_corrections,
    `BfgsVerification.AdmissibleBFGSRun.moving_frame_energy,
    `BfgsVerification.AdmissibleBFGSRun.normalized_frame_trace_recurrence,
    `BfgsVerification.AdmissibleBFGSRun.moving_frame_reciprocal_sum_bound,
    `BfgsVerification.AdmissibleBFGSRun.moving_frame_tail_criterion,
    `BfgsVerification.AdmissibleBFGSRun.smooth_subspace_projection_trace_update,
    `BfgsVerification.AdmissibleBFGSRun.smooth_subspace_projection_trace_bound,
    `BfgsVerification.AdmissibleBFGSRun.smooth_subspace_residual_energy_le,
    `BfgsVerification.AdmissibleBFGSRun.smooth_subspace_residual_budget,
    `BfgsVerification.FrameBounds.gram_trace_square,
    `BfgsVerification.FrameBounds.gram_trace_add_le,
    `BfgsVerification.FrameBounds.gram_trace_transport_le,
    `BfgsVerification.AdmissibleBFGSRun.residual_frame_step,
    `BfgsVerification.ResidualBudget.residual_reciprocal_sum_le,
    `BfgsVerification.AdmissibleBFGSRun.residual_frames_on_tail_incompatible_source,
    `BfgsVerification.FrameNorms.operatorSqBound_iff_opNorm_sq,
    `BfgsVerification.FrameNorms.orthonormal_matrix_for_subspace] do
    let info ← getConstInfo name
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .quotInfo _ => "quotient"
      | .ctorInfo _ => "constructor"
      | .inductInfo _ => "inductive"
      | .recInfo _ => "recursor"
    logInfo m!"M_SOURCE_KIND {name} {kind}"

#print axioms BfgsVerification.hessianUpdate
