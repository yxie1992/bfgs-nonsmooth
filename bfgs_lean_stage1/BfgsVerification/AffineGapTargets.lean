import BfgsVerification.AffineGapNeighborhood

/-! Exact actual-objective contract for Module A's local affine gap. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter
namespace BfgsVerification
open AffineDistance AffineCriticalObjective ConvexSubdifferential

def FiniteC1MaxAffineGapTarget : Prop :=
  ∀ n m : ℕ, ∀ F : Vec n → ℝ, ConvexOn ℝ univ F →
  ∀ f : Fin m → Vec n → ℝ, ∀ U : Set (Vec n), IsOpen U →
  ∀ star : Vec n, star∈U →
  (∀ i, ContDiffOn ℝ 1 (f i) U) → LocalFiniteMax F f star →
  AffineIndependent ℝ (fun i => coordinateGradient (f (activeIndexMap F f star i)) star) →
  ∀ w : Vec (activeIndices F f star).card, (∀ i, 0<w i) →
  (∑ i, w i)=1 → (∑ i, w i • coordinateGradient (f (activeIndexMap F f star i)) star)=0 →
  ∃ V : Set (Vec n), IsOpen V ∧ star∈V ∧
    (∀ p∈V, LowerSemicontinuousAt (objectiveDistance F) p ∧
      (IsAffineCritical F p ↔ ∀ z, F p≤F z)) ∧
    (∀ K : Set (Vec n), IsCompact K → K.Nonempty → K⊆V →
      (∀ p∈K, F star<F p) →
      ∃ p∈K, 0<objectiveDistance F p ∧ ∀ q∈K, objectiveDistance F p≤objectiveDistance F q)

theorem finiteC1MaxAffineGap : FiniteC1MaxAffineGapTarget := by
  intro n m F hF f U hU star hs hf hr hi w hw hsum hz
  exact finite_C1_max_neighborhood_gap hF hU star hs hf hr hi w hw hsum hz

end BfgsVerification
