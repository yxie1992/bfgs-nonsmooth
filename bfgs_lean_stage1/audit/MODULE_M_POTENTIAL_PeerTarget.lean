import SharpPotentialTargets
import Lean

noncomputable section
open scoped BigOperators Topology
open Filter Lean Elab Command Meta
open BfgsVerification BfgsVerification.ScalarHierarchy

def ReviewedPotentialContract : Prop :=
  ∀ (n : ℕ) (R : FullBFGSRun n) (G c : ℝ), 0 < c → Summable R.d →
    ∀ J : ℕ, ∃ P : Polynomial ℝ,
      P.natDegree ≤ n - 1 ∧
      (∀ m : ℕ, 2 ≤ m →
        weightedPotential n
          ((4 * G ^ 2 / c ^ 2) / ((∑' i : ℕ, R.d (J + i)) / (c * ((m : ℝ) - 1))))
          (principalSum (R.H J)) = P.eval ((m : ℝ) - 1) ∧
        weightedPotential n
          ((4 * G ^ 2 / c ^ 2) / ((∑' i : ℕ, R.d (J + i)) / (c * ((m : ℝ) - 1))))
          (principalSum (R.H J)) ≤
        weightedPotential n
          ((4 * G ^ 2 / c ^ 2) / ((∑' i : ℕ, R.d (J + i)) / c))
          (principalSum (R.H J)) * ((m : ℝ) - 1) ^ (n - 1)) ∧
      Tendsto (fun m : ℕ =>
        (weightedPotential n
          ((4 * G ^ 2 / c ^ 2) / ((∑' i : ℕ, R.d (J + i)) / (c * ((m : ℝ) - 1))))
          (principalSum (R.H J))) ^ (1 / (m : ℝ))) atTop (𝓝 1)

run_cmd do
  let info ← getConstInfo `BfgsVerification.sharpPrincipalPotential
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `ReviewedPotentialContract)
  unless ok do throwError "literal actual-run potential contract mismatch"
  logInfo "INDEPENDENT_CONTRACT_OK theorem"
  let ok ← liftTermElabM <| Meta.isDefEq
    (mkConst `BfgsVerification.SharpPrincipalPotentialTarget) (mkConst `ReviewedPotentialContract)
  unless ok do throwError "literal target definition mismatch"
  logInfo "INDEPENDENT_CONTRACT_OK definition"

example (n : ℕ) (r : ℝ) (e : ℕ → ℝ) :
    (SharpPotentialDegree.potentialPolynomial n r e).natDegree ≤ n - 1 :=
  SharpPotentialDegree.potentialPolynomial_natDegree n r e

end
