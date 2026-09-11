import BfgsVerification.PlanarAllEndpointTargets

#check BfgsVerification.PlanarAllPairs.eligible_step_ne_zero
#print axioms BfgsVerification.PlanarAllPairs.eligible_step_ne_zero
#check BfgsVerification.PlanarAllPairs.eligible_normalized_descent
#print axioms BfgsVerification.PlanarAllPairs.eligible_normalized_descent
#check BfgsVerification.PlanarAllPairs.eligible_normalized_wolfe
#print axioms BfgsVerification.PlanarAllPairs.eligible_normalized_wolfe
#check BfgsVerification.PlanarAllPairs.compact_pair_transversality
#print axioms BfgsVerification.PlanarAllPairs.compact_pair_transversality
#check BfgsVerification.PlanarAllPairs.compact_pair_transversality_length
#print axioms BfgsVerification.PlanarAllPairs.compact_pair_transversality_length
#check BfgsVerification.PlanarAllPairs.common_pairing_neighborhood
#print axioms BfgsVerification.PlanarAllPairs.common_pairing_neighborhood
#check BfgsVerification.PlanarAllPairs.exists_pairwise_structured_field
#print axioms BfgsVerification.PlanarAllPairs.exists_pairwise_structured_field
#check BfgsVerification.PlanarAllPairs.structured_all_pair_transport
#print axioms BfgsVerification.PlanarAllPairs.structured_all_pair_transport
#check BfgsVerification.PlanarAllPairs.square_bound_of_log_bound
#print axioms BfgsVerification.PlanarAllPairs.square_bound_of_log_bound
#check BfgsVerification.PlanarAllPairs.source_all_pair_transport
#print axioms BfgsVerification.PlanarAllPairs.source_all_pair_transport
#check BfgsVerification.PlanarAllPairs.SourceAllPairTransportTarget
#print axioms BfgsVerification.PlanarAllPairs.SourceAllPairTransportTarget
#check BfgsVerification.PlanarAllPairs.sourceAllPairTransport
#print axioms BfgsVerification.PlanarAllPairs.sourceAllPairTransport
#check BfgsVerification.PlanarAllPairs.exists_all_endpoint_field
#print axioms BfgsVerification.PlanarAllPairs.exists_all_endpoint_field
#check BfgsVerification.PlanarAllPairs.source_all_endpoint_estimates
#print axioms BfgsVerification.PlanarAllPairs.source_all_endpoint_estimates
#check BfgsVerification.PlanarAllPairs.SourceAllEndpointEstimatesTarget
#print axioms BfgsVerification.PlanarAllPairs.SourceAllEndpointEstimatesTarget
#check BfgsVerification.PlanarAllPairs.sourceAllEndpointEstimates
#print axioms BfgsVerification.PlanarAllPairs.sourceAllEndpointEstimates

open Lean Elab Command in
run_cmd do
  for (decl,target) in [
      (`BfgsVerification.PlanarAllPairs.source_all_pair_transport,`BfgsVerification.PlanarAllPairs.SourceAllPairTransportTarget),
      (`BfgsVerification.PlanarAllPairs.sourceAllPairTransport,`BfgsVerification.PlanarAllPairs.SourceAllPairTransportTarget),
      (`BfgsVerification.PlanarAllPairs.source_all_endpoint_estimates,`BfgsVerification.PlanarAllPairs.SourceAllEndpointEstimatesTarget),
      (`BfgsVerification.PlanarAllPairs.sourceAllEndpointEstimates,`BfgsVerification.PlanarAllPairs.SourceAllEndpointEstimatesTarget)] do
    let info ← getConstInfo decl
    let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst target)
    unless ok do throwError "target mismatch: {decl}"
    logInfo m!"EXACT_TARGET_OK {decl}"
