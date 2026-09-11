import BfgsVerification.UnivariateCellGeometry

/-! Exact contracts for genuine one-dimensional semialgebraic geometry.
These are proved infrastructure; no general parameter-dependent projection or
higher-dimensional path decomposition is claimed. -/
noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- A finite cover by nonempty convex semialgebraic cells, each open or a
singleton, is constructed from the actual roots of the actual formula. -/
theorem PolynomialFormula.finite_semialgebraic_cell_cover (f : PolynomialFormula Unit) :
    ∃ C : Finset (Set ℝ),
      (∀ s ∈ C, s.Nonempty ∧ Convex ℝ s ∧ IsSemialgebraic (univariateLift s) ∧
        (IsOpen s ∨ ∃ b : ℝ, s = {b})) ∧
      ⋃ s ∈ C, s = {x : ℝ | f.Holds (fun _ => x)} := by
  classical
  let B := rootBoundary f.univariatePolynomials
  let C := (rootCells B).filter (fun s => ∃ x ∈ s, f.Holds (fun _ => x))
  refine ⟨C,?_,?_⟩
  · intro s hs
    obtain ⟨hroot,x,hxs,hfx⟩ := Finset.mem_filter.mp hs
    exact ⟨⟨x,hxs⟩,rootCells_convex B s hroot,rootCells_semialgebraic B hroot,
      rootCells_open_or_singleton B hroot⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨s,hxs⟩ := mem_iUnion.mp hx
      obtain ⟨hs,hxs⟩ := mem_iUnion.mp hxs
      obtain ⟨y,hys,hy⟩ := (Finset.mem_filter.mp hs).2
      exact (f.holds_constant_on_rootCell (Finset.mem_filter.mp hs).1 hxs hys).mpr hy
    · intro hx
      have hxc : x ∈ ⋃ s ∈ rootCells B, s := by rw [rootCells_cover]; exact mem_univ _
      obtain ⟨s,hxs⟩ := mem_iUnion.mp hxc
      obtain ⟨hs,hxs⟩ := mem_iUnion.mp hxs
      exact mem_iUnion.mpr ⟨s,mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨hs,x,hxs,hx⟩,hxs⟩⟩

end RealAlgebraicGeometry
open RealAlgebraicGeometry

def UnivariateSignBoundaryTarget : Prop := ∀ f : PolynomialFormula Unit,
    ∃ B : Finset ℝ, ∀ x y : ℝ, x ∉ B → y ∉ B → cutProfile B x = cutProfile B y →
      (f.Holds (fun _ => x) ↔ f.Holds (fun _ => y))

theorem univariateSignBoundary : UnivariateSignBoundaryTarget :=
  PolynomialFormula.exists_finite_sign_boundary

def UnivariateConvexCoverTarget : Prop := ∀ S : Set (Unit → ℝ), IsSemialgebraic S →
    ∃ C : Finset (Set (Unit → ℝ)), (∀ s ∈ C, Convex ℝ s) ∧ ⋃ s ∈ C, s = S

theorem univariateConvexCover : UnivariateConvexCoverTarget := by
  intro S hS
  exact univariate_semialgebraic_finite_convex_cover hS

def UnivariateCellCoverTarget : Prop := ∀ f : PolynomialFormula Unit,
    ∃ C : Finset (Set ℝ),
      (∀ s ∈ C, s.Nonempty ∧ Convex ℝ s ∧ IsSemialgebraic (univariateLift s) ∧
        (IsOpen s ∨ ∃ b : ℝ, s = {b})) ∧
      ⋃ s ∈ C, s = {x : ℝ | f.Holds (fun _ => x)}

theorem univariateCellCover : UnivariateCellCoverTarget :=
  PolynomialFormula.finite_semialgebraic_cell_cover

end BfgsVerification
