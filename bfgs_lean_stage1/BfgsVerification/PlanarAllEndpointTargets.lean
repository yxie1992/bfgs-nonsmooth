import BfgsVerification.PlanarAllEndpoints
import BfgsVerification.PlanarAllPairTargets

noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter Matrix Metric
namespace BfgsVerification.PlanarAllPairs
open PlanarCornerCharts PlanarObjectiveField ConvexSubdifferential AffineCriticalObjective
open TransportedCertificate HomogeneousPlanar

/-- All three source endpoint estimates for one actual field and all pairs. -/
def SourceAllEndpointEstimatesTarget : Prop := ∀ {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {K : Set (Vec 2)} {ℓ : ℝ}
    (hK : IsCompact K) (hlevel : ∀x∈K,F x=ℓ)
    (hstrict : ∀x y : Vec 2,segment ℝ x y ⊆ frontier {w | F w ≤ ℓ} → x=y)
    (hregular : ∀x∈K,ContDiffAt ℝ 2 F x ∨ ConvexTwoBranchRegularAt F x)
    (hnoncritical : ∀x∈K,¬IsAffineCritical F x)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : c₂ < 1),
    ∃m : ℕ,∃χ : Fin m → Vec 2 → ℝ,∃v : Fin m → ℝ → Vec 2,
      (∀i,ContDiff ℝ ∞ (χ i)) ∧ ∃U Q : Set (Vec 2),
      IsOpen U ∧ K⊆U ∧ closure U⊆Q ∧ IsCompact Q ∧
      ∃η κ δ C C' C₀ : ℝ,0 < η ∧ 0 < κ ∧ 0 < δ ∧ 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ C₀ ∧
      (∀x∈Q,∃L : ℝ≥0,∃V∈𝓝 x,LipschitzOnWith L (field hF χ v) V) ∧
      (∀x∈Q,∀g∈subdifferential F x,η ≤ dot g (field hF χ v x)) ∧
      (∀x∈Q,∀g∈subdifferential F x,∀h∈subdifferential F x,
        dot g (field hF χ v x)=dot h (field hF χ v x)) ∧
      ∀x∈U,∀z∈U,∀g h,EligiblePair F c₁ c₂ x z g h → ‖euclideanVector (z-x)‖ < δ →
        (∀θ∈Icc (0 : ℝ) 1,x+θ • (z-x)∈Q ∧
          κ*‖euclideanVector (z-x)‖ ≤ |pairDet (z-x) (field hF χ v (x+θ • (z-x)))|) ∧
        (dot (h-g) (field hF χ v z))^2 / pairCurvature x z g h ≤ C₀ ∧
        ∃lam β : ℝ,0 < lam ∧ field hF χ v z=lam • field hF χ v x+β • (z-x) ∧
          |Real.log lam| ≤ C*pairDecrease x z g ∧
          (pairDecrease x z g ≤ 1 → lam^2 ≤ 1+C'*pairDecrease x z g)

theorem sourceAllEndpointEstimates : SourceAllEndpointEstimatesTarget := @source_all_endpoint_estimates

end BfgsVerification.PlanarAllPairs
