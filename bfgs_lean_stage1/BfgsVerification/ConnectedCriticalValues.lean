import BfgsVerification.AffineCriticalPathCover
import Mathlib.Topology.Separation.Connected

noncomputable section
open Set
namespace BfgsVerification.AffineSupportPath
open AffineCriticalObjective

/-- Any finite cover by preconnected pieces bounds the actual component family.
The pieces need not be closed or disjoint, and may be empty. -/
theorem finite_components_of_finite_preconnected_cover {X : Type*} [TopologicalSpace X]
    {m : ℕ} {S : Set X} (C : Fin m → Set X) (hcover : S=⋃ i,C i)
    (hC : ∀ i, IsPreconnected (C i)) :
    (connectedComponentIn S '' S).Finite := by
  have hs : ∀ i, (connectedComponentIn S '' C i).Subsingleton := by
    intro i A hA B hB
    obtain ⟨x,hx,rfl⟩ := hA
    obtain ⟨y,hy,rfl⟩ := hB
    apply connectedComponentIn_eq
    apply (hC i).subset_connectedComponentIn hx _ hy
    intro z hz
    rw [hcover]
    exact mem_iUnion.mpr ⟨i,hz⟩
  have h := Set.finite_iUnion (fun i => (hs i).finite)
  rwa [← image_iUnion, ← hcover] at h

/-- A continuous function with finite image is constant on a preconnected set. -/
theorem image_subsingleton_of_preconnected_finite_image {X : Type*} [TopologicalSpace X]
    {S : Set X} {f : X → ℝ} (hS : IsPreconnected S) (hf : ContinuousOn f S)
    (hfinite : (f '' S).Finite) : (f '' S).Subsingleton := by
  by_contra h
  exact (hS.image f hf).infinite_of_nontrivial (Set.not_subsingleton_iff.mp h) hfinite

/-- Once the actual critical value set is proved finite, continuity gives
constancy on every actual connected component, without selecting a path. -/
theorem objective_eq_on_affineCritical_component_of_finite_values {n : ℕ}
    {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (hfinite : (F '' {p | IsAffineCritical F p}).Finite) {x p q : Vec n}
    (hp : p ∈ connectedComponentIn {z | IsAffineCritical F z} x)
    (hq : q ∈ connectedComponentIn {z | IsAffineCritical F z} x) : F p=F q := by
  have h := image_subsingleton_of_preconnected_finite_image
    isPreconnected_connectedComponentIn (convex_continuous hF).continuousOn
    (hfinite.subset (image_subset F (connectedComponentIn_subset _ x)))
  exact h ⟨p,hp,rfl⟩ ⟨q,hq,rfl⟩

end BfgsVerification.AffineSupportPath
