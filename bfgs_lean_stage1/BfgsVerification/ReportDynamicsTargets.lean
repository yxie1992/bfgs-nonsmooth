import BfgsVerification.AlgebraicSeedDeterministicTrace
import BfgsVerification.FixedNormalCompositeEndToEnd
noncomputable section
open scoped Topology
namespace BfgsVerification
open AlgebraicSeed SeedCycle SeedOrbit

/-- D's actual exact three-update identity, with intermediate SPD matrices. -/
def ExactSeedCycleTarget : Prop :=
  update (update (update 1 g0 g1 1) g1 (g2 (root 0) (root 1)) (1/4))
    (g2 (root 0) (root 1)) g0 (1/16)=ratio (root 0) (root 1) • (1 : Mat 2) ∧
  ∀ j : Fin 3, (metric (root 0) (root 1) j).PosDef

/-- The actual deterministic seed counterexample. This is the homogeneous seed
subtheorem of D, not D's later coercive/local C2 embedding theorem. -/
def DeterministicSeedFailureTarget : Prop :=
  ∀ (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (hc₂ : c₂ < 1),
    let R := SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂
    R.H 0=1 ∧ Filter.Tendsto R.x Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun k => objective seedC seedD (R.x k)) Filter.atTop (𝓝 0) ∧
      (∀ k, 0 < objective seedC seedD (R.x k)) ∧
      (∀ k, objective seedC seedD (R.x (k+1)) < objective seedC seedD (R.x k)) ∧
      (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential (objective seedC seedD) 0 ∧
      (∀ k, DeterministicLineSearch.fromMetric (objective seedC seedD) (R.x k) (R.H k) c₁ c₂ 5 =
        (some (R.α k),trialHistory (phase k)))

/-- Every actual trial in each phase, not just its accepted endpoint. -/
def AllSeedTrialsTarget : Prop :=
  ∀ (k : ℕ) (q : Fin 9), trialPhase q=phase k →
    DifferentiableAt ℝ (objective seedC seedD)
      (orbitPoint k+trialLength q • bfgsStep (orbitMetric k) (orbitGradient k) 1) ∧
    PointCertificate seedC seedD
      (orbitPoint k+trialLength q • bfgsStep (orbitMetric k) (orbitGradient k) 1) (trialActive q)

end BfgsVerification
