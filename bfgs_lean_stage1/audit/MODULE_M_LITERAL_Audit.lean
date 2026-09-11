import PrincipalCombinatorialIdentity
import Lean
open Lean Elab Command Meta
#check @BfgsVerification.insert_product_sum_eq
#print axioms BfgsVerification.insert_product_sum_eq
#check @BfgsVerification.principal_product_augmented_sum_eq
#print axioms BfgsVerification.principal_product_augmented_sum_eq
#check @BfgsVerification.diagonal_coordinate_gram_sum_eq
#print axioms BfgsVerification.diagonal_coordinate_gram_sum_eq
#check @BfgsVerification.orthogonal_coordinate_gram_sum_eq
#print axioms BfgsVerification.orthogonal_coordinate_gram_sum_eq
#check @BfgsVerification.PrincipalGramSumIdentityTarget
#print axioms BfgsVerification.PrincipalGramSumIdentityTarget
#check @BfgsVerification.principalGramSumIdentity
#print axioms BfgsVerification.principalGramSumIdentity
#print BfgsVerification.PrincipalGramSumIdentityTarget
run_cmd do
  let info ← getConstInfo `BfgsVerification.principalGramSumIdentity
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.PrincipalGramSumIdentityTarget)
  unless ok do throwError "principal Gram identity target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.principalGramSumIdentity"
