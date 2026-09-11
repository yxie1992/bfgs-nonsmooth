import BfgsVerification.SmoothObjectiveGraphPaths
import BfgsVerification.ConnectedCriticalValues
import BfgsVerification.SemialgebraicComponents
import Mathlib.Data.Fintype.EquivFin

noncomputable section
open Set
namespace BfgsVerification.RealAlgebraicGeometry
open AffineCriticalObjective AffineSupportPath

theorem finset_cover_enumeration {X : Type*} (C : Finset (Set X)) :
    ∃ m : ℕ, ∃ D : Fin m → Set X, (∀ i, D i ∈ C) ∧
      (⋃ T ∈ C, T) = ⋃ i, D i := by
  classical
  let D : Fin C.card → Set X := fun i => (C.equivFin.symm i).val
  refine ⟨C.card,D,fun i => (C.equivFin.symm i).property,?_⟩
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨T,hT,hx⟩
    refine ⟨C.equivFin ⟨T,hT⟩,?_⟩
    simpa only [D,Equiv.symm_apply_apply] using hx
  · rintro ⟨i,hi⟩
    exact ⟨D i,(C.equivFin.symm i).property,hi⟩

theorem critical_values_eq_graph_image {n : ℕ} (F : Vec n → ℝ) :
    F '' {x | IsAffineCritical F x} =
      (fun z : Option (Fin n) → ℝ => z none) '' affineCriticalGraph F := by
  ext v
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨objectiveLift F x,⟨rfl,hx⟩,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨fun i => z (some i),hz.2,hz.1.symm⟩

/-- This conditional assembly keeps the actual finite graph-cover premise
visible. The final semialgebraic application must derive it separately. -/
theorem finite_critical_values_of_smooth_graph_cover {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (C : Finset (Set (Option (Fin n) → ℝ)))
    (hC : ∀ T ∈ C, PiecewiseSmoothConnected T)
    (hcover : (⋃ T ∈ C, T) = affineCriticalGraph F) :
    (F '' {x | IsAffineCritical F x}).Finite := by
  obtain ⟨m,D,hD,he⟩ := finset_cover_enumeration C
  have hgraph : affineCriticalGraph F = ⋃ i, D i := hcover.symm.trans he
  have hsub : ∀ i, D i ⊆ affineCriticalGraph F := by
    intro i z hz
    rw [hgraph]
    exact mem_iUnion.mpr ⟨i,hz⟩
  have hi : ∀ i, ((fun z : Option (Fin n) → ℝ => z none) '' D i).Subsingleton := by
    intro i a ha b hb
    obtain ⟨u,hu,rfl⟩ := ha
    obtain ⟨v,hv,rfl⟩ := hb
    have hp := affineCriticalGraph_path_project ((hC (D i) (hD i) u hu v hv).mono (hsub i))
    have hv' := value_eq_of_affineCritical_path hF (fun _ hx => hx) hp
    exact (hsub i hu).1.trans (hv'.trans (hsub i hv).1.symm)
  rw [critical_values_eq_graph_image,hgraph,image_iUnion]
  exact Set.finite_iUnion (fun i => (hi i).finite)

theorem finite_semialgebraic_components_of_smooth_cover {σ : Type*} [Fintype σ]
    {S : Set (σ → ℝ)} (C : Finset (Set (σ → ℝ)))
    (hC : ∀ T ∈ C, IsSemialgebraic T ∧ PiecewiseSmoothConnected T)
    (hcover : (⋃ T ∈ C, T) = S) :
    (connectedComponentIn S '' S).Finite ∧
      ∀ x, IsSemialgebraic (connectedComponentIn S x) := by
  obtain ⟨m,D,hD,he⟩ := finset_cover_enumeration C
  have hS : S = ⋃ i, D i := hcover.symm.trans he
  have hpre : ∀ i, IsPreconnected (D i) := fun i => (hC (D i) (hD i)).2.isPreconnected
  exact ⟨finite_components_of_finite_preconnected_cover D hS hpre,
    fun x => connectedComponentIn_semialgebraic_of_finite_preconnected_cover D hS hpre
      (fun i => (hC (D i) (hD i)).1) x⟩

end BfgsVerification.RealAlgebraicGeometry
