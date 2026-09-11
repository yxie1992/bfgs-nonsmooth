import BfgsVerification.SemialgebraicSyntax
import Mathlib.Topology.Connected.Basic

noncomputable section
open Set
open scoped Classical
namespace BfgsVerification.RealAlgebraicGeometry

/-- Every actual connected component is a union of whole pieces of a finite
preconnected cover. No relative openness, closedness or disjointness is needed. -/
theorem connectedComponentIn_eq_union_cover {X : Type*} [TopologicalSpace X]
    {m : ℕ} {S : Set X} (C : Fin m → Set X) (hcover : S = ⋃ i, C i)
    (hC : ∀ i, IsPreconnected (C i)) (x : X) :
    connectedComponentIn S x =
      ⋃ i ∈ Finset.univ.filter (fun i => (C i ∩ connectedComponentIn S x).Nonempty), C i := by
  classical
  have hsub : ∀ i, C i ⊆ S := by
    intro i y hy
    rw [hcover]
    exact mem_iUnion.mpr ⟨i,hy⟩
  ext y
  constructor
  · intro hy
    have hyS := connectedComponentIn_subset S x hy
    rw [hcover] at hyS
    obtain ⟨i,hi⟩ := mem_iUnion.mp hyS
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ i,⟨y,hi,hy⟩⟩,hi⟩⟩
  · intro hy
    obtain ⟨i,hy⟩ := mem_iUnion.mp hy
    obtain ⟨hi,hy⟩ := mem_iUnion.mp hy
    obtain ⟨z,hz,hzc⟩ := (Finset.mem_filter.mp hi).2
    have hz' := (hC i).subset_connectedComponentIn hz (hsub i) hy
    simpa only [← connectedComponentIn_eq hzc] using hz'

/-- A finite cover by semialgebraic preconnected pieces makes every actual
connected component semialgebraic, including the empty component off the set. -/
theorem connectedComponentIn_semialgebraic_of_finite_preconnected_cover
    {σ : Type*} [Finite σ] {m : ℕ} {S : Set (σ → ℝ)}
    (C : Fin m → Set (σ → ℝ)) (hcover : S = ⋃ i, C i)
    (hC : ∀ i, IsPreconnected (C i)) (hSA : ∀ i, IsSemialgebraic (C i))
    (x : σ → ℝ) : IsSemialgebraic (connectedComponentIn S x) := by
  classical
  rw [connectedComponentIn_eq_union_cover C hcover hC x]
  exact isSemialgebraic_finset_union _ C (fun i _ => hSA i)

end BfgsVerification.RealAlgebraicGeometry
