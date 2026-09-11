import BfgsVerification.ContinuousSemialgebraicComponents
import BfgsVerification.SemialgebraicCriticalGeometry

noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry
open AffineCriticalObjective AffineSupportPath

/-- Module A's actual affine-critical semialgebraic path components. The path
relation includes arbitrary continuous semialgebraic witnesses; regularity and
finite covers are derived, and objective constancy uses actual finite values. -/
theorem affine_critical_continuous_semialgebraic_components {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (hSA : IsSemialgebraicObjective F) :
    (continuousSemialgebraicComponent {z | IsAffineCritical F z} ''
      {z | IsAffineCritical F z}).Finite ∧
    ∀ x, IsSemialgebraic (continuousSemialgebraicComponent {z | IsAffineCritical F z} x) ∧
      ContinuousSemialgebraicPathConnected
        (continuousSemialgebraicComponent {z | IsAffineCritical F z} x) ∧
      ∀ p ∈ continuousSemialgebraicComponent {z | IsAffineCritical F z} x,
        ∀ q ∈ continuousSemialgebraicComponent {z | IsAffineCritical F z} x, F p = F q := by
  have h := continuous_semialgebraic_components (affineCritical_set_semialgebraic hSA)
  refine ⟨h.1, fun x => ⟨(h.2 x).1, (h.2 x).2.1, ?_⟩⟩
  have hsub : continuousSemialgebraicComponent {z | IsAffineCritical F z} x ⊆
      {z | IsAffineCritical F z} := fun _ hp => hp.mem.2
  have hfinite := (semialgebraic_affine_critical_values hF hSA).subset (image_subset F hsub)
  have hc := image_subsingleton_of_preconnected_finite_image
    ((h.2 x).2.2.toPiecewiseSmoothConnected.isPreconnected)
    (convex_continuous hF).continuousOn hfinite
  exact fun p hp q hq => hc ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩

end RealAlgebraicGeometry
open RealAlgebraicGeometry AffineCriticalObjective

def AffineCriticalSemialgebraicPathComponentsTarget : Prop := ∀ {n : ℕ} {F : Vec n → ℝ},
    ConvexOn ℝ univ F → IsSemialgebraicObjective F →
    (continuousSemialgebraicComponent {z | IsAffineCritical F z} ''
      {z | IsAffineCritical F z}).Finite ∧
    ∀ x, IsSemialgebraic (continuousSemialgebraicComponent {z | IsAffineCritical F z} x) ∧
      ContinuousSemialgebraicPathConnected
        (continuousSemialgebraicComponent {z | IsAffineCritical F z} x) ∧
      ∀ p ∈ continuousSemialgebraicComponent {z | IsAffineCritical F z} x,
        ∀ q ∈ continuousSemialgebraicComponent {z | IsAffineCritical F z} x, F p = F q

theorem affineCriticalSemialgebraicPathComponents : AffineCriticalSemialgebraicPathComponentsTarget :=
  affine_critical_continuous_semialgebraic_components

end BfgsVerification
