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
