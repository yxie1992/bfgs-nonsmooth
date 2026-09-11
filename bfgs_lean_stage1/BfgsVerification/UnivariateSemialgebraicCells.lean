import BfgsVerification.UnivariatePolynomialFormula
import BfgsVerification.FiniteRootCells

/-! A derived finite convex-cell cover of every genuine one-dimensional
semialgebraic set. This proves the fixed one-dimensional decomposition only,
not parameter-dependent projection or higher-dimensional decomposition. -/
noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- Every cell of the constructed finite root cover has constant actual Boolean
truth value, including all singleton boundary cells. -/
theorem PolynomialFormula.holds_constant_on_rootCell (f : PolynomialFormula Unit)
    {C : Set ℝ} (hC : C ∈ rootCells (rootBoundary f.univariatePolynomials))
    {x y : ℝ} (hx : x ∈ C) (hy : y ∈ C) :
    f.Holds (fun _ => x) ↔ f.Holds (fun _ => y) := by
  classical
  rcases Finset.mem_union.mp hC with h | h
  · obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp h
    exact f.holds_constant_on_profile (Finset.Subset.refl _) hx.1 hy.1
      (hx.2.trans hy.2.symm)
  · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp h
    have he : x = y := (mem_singleton_iff.mp hx).trans (mem_singleton_iff.mp hy).symm
    rw [he]

/-- The actual formula's truth set is a finite union of constructed convex
cells. No finiteness of connected components is supplied as an assumption. -/
theorem PolynomialFormula.finite_convex_cover (f : PolynomialFormula Unit) :
    ∃ C : Finset (Set ℝ), (∀ s ∈ C, Convex ℝ s) ∧
      ⋃ s ∈ C, s = {x : ℝ | f.Holds (fun _ => x)} := by
  classical
  let B := rootBoundary f.univariatePolynomials
  let C := (rootCells B).filter (fun s => ∃ x ∈ s, f.Holds (fun _ => x))
  refine ⟨C,?_,?_⟩
  · intro s hs
    exact rootCells_convex B s (Finset.mem_filter.mp hs).1
  · ext x
    constructor
    · intro hx
      obtain ⟨s,hxs⟩ := mem_iUnion.mp hx
      obtain ⟨hs,hxs⟩ := mem_iUnion.mp hxs
      obtain ⟨y,hys,hy⟩ := (Finset.mem_filter.mp hs).2
      exact (f.holds_constant_on_rootCell (Finset.mem_filter.mp hs).1 hxs hys).mpr hy
    · intro hx
      have hcover := rootCells_cover B
      have hxc : x ∈ ⋃ s ∈ rootCells B, s := by rw [hcover]; exact mem_univ _
      obtain ⟨s,hxs⟩ := mem_iUnion.mp hxc
      obtain ⟨hs,hxs⟩ := mem_iUnion.mp hxs
      exact mem_iUnion.mpr ⟨s,mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨hs,x,hxs,hx⟩,hxs⟩⟩

/-- Literal finite-dimensional form using the existing semialgebraic predicate
on one real coordinate. The pieces are actual convex subsets of that space. -/
theorem univariate_semialgebraic_finite_convex_cover {S : Set (Unit → ℝ)}
    (hS : IsSemialgebraic S) :
    ∃ C : Finset (Set (Unit → ℝ)), (∀ s ∈ C, Convex ℝ s) ∧ ⋃ s ∈ C, s = S := by
  classical
  obtain ⟨f,hf⟩ := hS
  obtain ⟨C,hconv,hcover⟩ := f.finite_convex_cover
  let lift : Set ℝ → Set (Unit → ℝ) := fun s => (fun u => u ()) ⁻¹' s
  refine ⟨C.image lift,?_,?_⟩
  · intro s hs
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hs
    exact (hconv c hc).linear_preimage (LinearMap.proj () : (Unit → ℝ) →ₗ[ℝ] ℝ)
  · ext u
    have he : (fun _ : Unit => u ()) = u := by funext i; cases i; rfl
    have hset : u () ∈ ⋃ s ∈ C, s ↔ u ∈ S := by
      rw [hcover]
      simpa only [mem_setOf_eq,he] using (hf u).symm
    rw [← hset]
    simp only [mem_iUnion,Finset.mem_image]
    constructor
    · rintro ⟨s,⟨c,hc,rfl⟩,hu⟩
      exact ⟨c,hc,hu⟩
    · rintro ⟨c,hc,hu⟩
      exact ⟨lift c,⟨c,hc,rfl⟩,hu⟩

end RealAlgebraicGeometry
end BfgsVerification
