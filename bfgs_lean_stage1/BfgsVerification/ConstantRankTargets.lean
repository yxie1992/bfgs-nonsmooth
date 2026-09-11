import BfgsVerification.RatePatchSecant
import BfgsVerification.AffineIndependentRank

noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter
namespace BfgsVerification.ConstantRankFields
open AffineCriticalObjective ConvexSubdifferential TransportedCertificate

/-- Every sufficiently close Armijo–weak-Wolfe eligible pair is covered by
one field and one set of constants, with positive curvature derived from c₂<1. -/
theorem source_eligible_common_rate {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : Fin m → Vec n → ℝ) {K : Set (Vec n)}
    (hK : IsCompact K) (hrep : ∀p∈K,LocalFiniteMax F f p)
    (hC2 : ∀p∈K,∀j,ContDiffAt ℝ 2 (f j) p)
    (hconv : ∀p∈K,∃V : Set (Vec n),IsOpen V ∧ p∈V ∧ ∀j,ConvexOn ℝ V (f j))
    (hnc : ∀p∈K,¬IsAffineCritical F p)
    (hrank : ∀p∈K,LocallyConstantActiveRank F f p)
    {c₁ c₂ : ℝ} (hc₂ : c₂<1) :
    ∃v : Vec n → Vec n,ContDiff ℝ 1 v ∧ ∃V Q : Set (Vec n),
      IsOpen V ∧ K⊆V ∧ closure V⊆Q ∧ IsCompact Q ∧
      ∃G δ C : ℝ,0<G ∧ 0<δ ∧ 0≤C ∧
      (∀x∈Q,sqNorm (v x)≤G^2) ∧
      (∀x∈Q,∀g∈subdifferential F x,dot g (v x)=1) ∧
      ∀x z g h : Vec n,x∈Q → z∈Q → ‖euclideanVector (z-x)‖<δ →
        EligiblePair F c₁ c₂ x z g h → (dot (h-g) (v z))^2 / pairCurvature x z g h ≤ C := by
  obtain ⟨v,hv,V,Q,hV,hKV,hVQ,hQ,G,δ,C,hG,hδ,hC,hbound,hpair,hsecant⟩ :=
    source_common_rate_and_secant hF f hK hrep hC2 hconv hnc hrank
  refine ⟨v,hv,V,Q,hV,hKV,hVQ,hQ,G,δ,C,hG,hδ,hC,hbound,hpair,?_⟩
  intro x z g h hx hz hstep hp
  exact hsecant x z g h hx hz hstep hp.gradient_x hp.gradient_z
    ((mul_pos (sub_pos.mpr hc₂) hp.decrease_pos).trans_le hp.curvature)

/-- Exact source contract: actual finite-dimensional constant rank supplies
visibility and bounded secant correction, without any BFGS matrix premise. -/
def SourceConstantRankTarget : Prop := ∀ {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : Fin m → Vec n → ℝ) {K : Set (Vec n)}
    (hK : IsCompact K) (hrep : ∀p∈K,LocalFiniteMax F f p)
    (hC2 : ∀p∈K,∀j,ContDiffAt ℝ 2 (f j) p)
    (hconv : ∀p∈K,∃V : Set (Vec n),IsOpen V ∧ p∈V ∧ ∀j,ConvexOn ℝ V (f j))
    (hnc : ∀p∈K,¬IsAffineCritical F p)
    (hrank : ∀p∈K,LocallyConstantActiveRank F f p),
    ∃v : Vec n → Vec n,ContDiff ℝ 1 v ∧ ∃V Q : Set (Vec n),
      IsOpen V ∧ K⊆V ∧ closure V⊆Q ∧ IsCompact Q ∧
      ∃G δ C : ℝ,0<G ∧ 0<δ ∧ 0≤C ∧
      (∀x∈Q,sqNorm (v x)≤G^2) ∧
      (∀x∈Q,∀g∈subdifferential F x,dot g (v x)=1) ∧
      ∀x z g h : Vec n,x∈Q → z∈Q → ‖euclideanVector (z-x)‖<δ →
        HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
        0<pairCurvature x z g h → (dot (h-g) (v z))^2 / pairCurvature x z g h ≤ C

theorem sourceConstantRank : SourceConstantRankTarget := @source_common_rate_and_secant

/-- Exact all-eligible-pair specialization of the same source construction. -/
def SourceConstantRankEligibleTarget : Prop := ∀ {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : Fin m → Vec n → ℝ) {K : Set (Vec n)}
    (hK : IsCompact K) (hrep : ∀p∈K,LocalFiniteMax F f p)
    (hC2 : ∀p∈K,∀j,ContDiffAt ℝ 2 (f j) p)
    (hconv : ∀p∈K,∃V : Set (Vec n),IsOpen V ∧ p∈V ∧ ∀j,ConvexOn ℝ V (f j))
    (hnc : ∀p∈K,¬IsAffineCritical F p)
    (hrank : ∀p∈K,LocallyConstantActiveRank F f p)
    {c₁ c₂ : ℝ} (hc₂ : c₂<1),
    ∃v : Vec n → Vec n,ContDiff ℝ 1 v ∧ ∃V Q : Set (Vec n),
      IsOpen V ∧ K⊆V ∧ closure V⊆Q ∧ IsCompact Q ∧
      ∃G δ C : ℝ,0<G ∧ 0<δ ∧ 0≤C ∧
      (∀x∈Q,sqNorm (v x)≤G^2) ∧
      (∀x∈Q,∀g∈subdifferential F x,dot g (v x)=1) ∧
      ∀x z g h : Vec n,x∈Q → z∈Q → ‖euclideanVector (z-x)‖<δ →
        EligiblePair F c₁ c₂ x z g h → (dot (h-g) (v z))^2 / pairCurvature x z g h ≤ C

theorem sourceConstantRankEligible : SourceConstantRankEligibleTarget := @source_eligible_common_rate

end BfgsVerification.ConstantRankFields
