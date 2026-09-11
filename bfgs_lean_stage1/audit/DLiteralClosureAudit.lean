import BfgsVerification.NonStrictLineSearch
import BfgsVerification.DLiteralIdentities
import BfgsVerification.DNonStrictPredicates
import BfgsVerification.DNonStrictSearch
import BfgsVerification.DNonStrictObjectives
import BfgsVerification.DLiteralTargets
set_option pp.universes true
#check BfgsVerification.NonStrictLineSearch.Armijo
#print axioms BfgsVerification.NonStrictLineSearch.Armijo
#check BfgsVerification.NonStrictLineSearch.Wolfe
#print axioms BfgsVerification.NonStrictLineSearch.Wolfe
#check BfgsVerification.NonStrictLineSearch.nextTrial
#print axioms BfgsVerification.NonStrictLineSearch.nextTrial
#check BfgsVerification.NonStrictLineSearch.search
#print axioms BfgsVerification.NonStrictLineSearch.search
#check BfgsVerification.NonStrictLineSearch.fromMetric
#print axioms BfgsVerification.NonStrictLineSearch.fromMetric
#check BfgsVerification.NonStrictLineSearch.search_accept
#print axioms BfgsVerification.NonStrictLineSearch.search_accept
#check BfgsVerification.NonStrictLineSearch.search_armijo_reject
#print axioms BfgsVerification.NonStrictLineSearch.search_armijo_reject
#check BfgsVerification.DLiteralIdentities.beta_quarter_iff
#print axioms BfgsVerification.DLiteralIdentities.beta_quarter_iff
#check BfgsVerification.DLiteralIdentities.gamma_sixteenth_iff
#print axioms BfgsVerification.DLiteralIdentities.gamma_sixteenth_iff
#check BfgsVerification.DLiteralIdentities.original_box_polynomial_iff
#print axioms BfgsVerification.DLiteralIdentities.original_box_polynomial_iff
#check BfgsVerification.DLiteralIdentities.gradient_support_zero
#print axioms BfgsVerification.DLiteralIdentities.gradient_support_zero
#check BfgsVerification.DLiteralIdentities.zero_not_mem_gradient_hull
#print axioms BfgsVerification.DLiteralIdentities.zero_not_mem_gradient_hull
#check BfgsVerification.DLiteralIdentities.coercive_exact_affine_combination
#print axioms BfgsVerification.DLiteralIdentities.coercive_exact_affine_combination
#check BfgsVerification.DLiteralIdentities.coercive_weights_convex
#print axioms BfgsVerification.DLiteralIdentities.coercive_weights_convex
#check BfgsVerification.SeedEmbedding.NonStrict.trial_accept
#print axioms BfgsVerification.SeedEmbedding.NonStrict.trial_accept
#check BfgsVerification.SeedEmbedding.NonStrict.trial_reject
#print axioms BfgsVerification.SeedEmbedding.NonStrict.trial_reject
#check BfgsVerification.SeedEmbedding.NonStrict.search_zero
#print axioms BfgsVerification.SeedEmbedding.NonStrict.search_zero
#check BfgsVerification.SeedEmbedding.NonStrict.search_one
#print axioms BfgsVerification.SeedEmbedding.NonStrict.search_one
#check BfgsVerification.SeedEmbedding.NonStrict.search_two
#print axioms BfgsVerification.SeedEmbedding.NonStrict.search_two
#check BfgsVerification.SeedEmbedding.NonStrict.search_all_phases
#print axioms BfgsVerification.SeedEmbedding.NonStrict.search_all_phases
#check BfgsVerification.SeedEmbedding.NonStrict.fromMetric_exact
#print axioms BfgsVerification.SeedEmbedding.NonStrict.fromMetric_exact
#check BfgsVerification.DNonStrictObjectives.seedOracleData
#print axioms BfgsVerification.DNonStrictObjectives.seedOracleData
#check BfgsVerification.DNonStrictObjectives.coerciveOracleData
#print axioms BfgsVerification.DNonStrictObjectives.coerciveOracleData
#check BfgsVerification.DNonStrictObjectives.seed_fromMetric
#print axioms BfgsVerification.DNonStrictObjectives.seed_fromMetric
#check BfgsVerification.DNonStrictObjectives.coercive_fromMetric
#print axioms BfgsVerification.DNonStrictObjectives.coercive_fromMetric
#check BfgsVerification.DNonStrictObjectives.embedding_fromMetric
#print axioms BfgsVerification.DNonStrictObjectives.embedding_fromMetric
#check BfgsVerification.DNonStrictObjectives.embedding_same_search
#print axioms BfgsVerification.DNonStrictObjectives.embedding_same_search
#check BfgsVerification.DLiteralTargets.LiteralIdentitiesTarget
#print axioms BfgsVerification.DLiteralTargets.LiteralIdentitiesTarget
#check BfgsVerification.DLiteralTargets.literalIdentities
#print axioms BfgsVerification.DLiteralTargets.literalIdentities
#check BfgsVerification.DLiteralTargets.NonStrictRunTarget
#print axioms BfgsVerification.DLiteralTargets.NonStrictRunTarget
#check BfgsVerification.DLiteralTargets.nonStrictRun
#print axioms BfgsVerification.DLiteralTargets.nonStrictRun


open Lean Elab Command in
run_cmd do
  let decl := `BfgsVerification.DLiteralTargets.literalIdentities
  let target := `BfgsVerification.DLiteralTargets.LiteralIdentitiesTarget
  let info ← getConstInfo decl
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst target)
  unless ok do throwError "D source contract mismatch"
  logInfo m!"EXACT_TARGET_OK {decl}"

open Lean Elab Command in
run_cmd do
  let decl := `BfgsVerification.DLiteralTargets.nonStrictRun
  let target := `BfgsVerification.DLiteralTargets.NonStrictRunTarget
  let info ← getConstInfo decl
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst target)
  unless ok do throwError "D source contract mismatch"
  logInfo m!"EXACT_TARGET_OK {decl}"
