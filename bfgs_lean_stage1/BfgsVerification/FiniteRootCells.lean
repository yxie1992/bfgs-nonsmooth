import BfgsVerification.UnivariateSignCells

/-! A constructed finite family of convex cells covering the real line, using
only an actual finite set of boundary points and their cut profiles. -/
noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

def rootFreeCell (B S : Finset ℝ) : Set ℝ :=
  {x | x ∉ B ∧ cutProfile B x = S}

theorem rootFreeCell_convex (B S : Finset ℝ) : Convex ℝ (rootFreeCell B S) := by
  apply Set.OrdConnected.convex
  rw [ordConnected_iff]
  intro x hx y hy hxy z hz
  have hp : cutProfile B x = cutProfile B y := hx.2.trans hy.2.symm
  refine ⟨gap_of_equal_cutProfile hxy hy.1 hp z hz,?_⟩
  have he : cutProfile B z = cutProfile B x := by
    ext b
    simp only [cutProfile,Finset.mem_filter]
    constructor
    · rintro ⟨hb,hbz⟩
      have hby : b < y := hbz.trans_le hz.2
      have hmem : b ∈ cutProfile B y := Finset.mem_filter.mpr ⟨hb,hby⟩
      rw [← hp] at hmem
      exact Finset.mem_filter.mp hmem
    · rintro ⟨hb,hbx⟩
      exact ⟨hb,hbx.trans_le hz.1⟩
  exact he.trans hx.2

def rootCells (B : Finset ℝ) : Finset (Set ℝ) := by
  classical
  exact (B.powerset.image (rootFreeCell B)) ∪ B.image (fun b => {b})

theorem rootCells_convex (B : Finset ℝ) (C : Set ℝ) (hC : C ∈ rootCells B) :
    Convex ℝ C := by
  classical
  rcases Finset.mem_union.mp hC with h | h
  · obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp h
    exact rootFreeCell_convex B S
  · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp h
    exact convex_singleton _

theorem rootCells_cover (B : Finset ℝ) : ⋃ C ∈ rootCells B, C = univ := by
  classical
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ B
  · exact mem_iUnion.mpr ⟨{x},mem_iUnion.mpr
      ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩),mem_singleton x⟩⟩
  · refine mem_iUnion.mpr ⟨rootFreeCell B (cutProfile B x),mem_iUnion.mpr ⟨?_,hx,rfl⟩⟩
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨cutProfile B x,Finset.mem_powerset.mpr ?_,rfl⟩
    exact Finset.filter_subset _ _

/-- The complete finite cover has convex pieces and no choices of root order
or missing unbounded intervals. Empty profile cells are harmless. -/
theorem exists_finite_convex_root_cover (B : Finset ℝ) :
    ∃ C : Finset (Set ℝ), (∀ s ∈ C, Convex ℝ s) ∧ ⋃ s ∈ C, s = univ :=
  ⟨rootCells B,rootCells_convex B,rootCells_cover B⟩

end RealAlgebraicGeometry
end BfgsVerification
