import PrincipalCombinatorialIdentity
import Lean

open Lean Elab Command Meta
open scoped BigOperators
open Matrix BfgsVerification
noncomputable section

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

def PeerExpectedPrincipalGramSum : Prop := ∀ {n : ℕ} (H : Mat n), H.PosDef →
  ∃ (U : Mat n) (lam : Vec n), Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
    Uᵀ * H * U = Matrix.diagonal lam ∧ (∀ i, 0 < lam i) ∧
    ∀ (y : Vec n) (j : ℕ),
      (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        (metricGram H (Matrix.fromCols (Matrix.replicateCol Unit y)
          (U * coordinateMatrix I))).det) =
      ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard (j+1),
        (∏ i ∈ J, lam i) * ∑ k ∈ J, (Uᵀ.mulVec y) k ^ 2

example : PeerExpectedPrincipalGramSum := principalGramSumIdentity

run_elab do
  let info ← getConstInfo `BfgsVerification.principalGramSumIdentity
  unless ← isDefEq info.type (mkConst `PeerExpectedPrincipalGramSum) do
    throwError "actual matrix/eigenbasis/Gram identity differs from independently restated source"
  logInfo "PEER_EXACT_TARGET_OK actual_source_identity"
  unless ← isDefEq (mkConst `BfgsVerification.PrincipalGramSumIdentityTarget)
      (mkConst `PeerExpectedPrincipalGramSum) do
    throwError "target definition differs from independent source contract"
  logInfo "PEER_EXACT_TARGET_OK target_definition"

example {n : ℕ} (lam : Fin n → ℝ) (y : Vec n) (j : ℕ) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
      (∏ i ∈ I, lam i) * ∑ k ∈ Finset.univ \ I, lam k * y k ^ 2) =
    ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard (j+1),
      (∏ i ∈ J, lam i) * ∑ k ∈ J, y k ^ 2 :=
  principal_product_augmented_sum_eq lam y j
