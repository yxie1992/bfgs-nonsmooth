import BfgsVerification.SemialgebraicPathFiniteCovers
import BfgsVerification.ActualCellFormulaCover

noncomputable section
open Set Polynomial
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {n m : ℕ}

/-- Entire sign-compatible coordinate cells, with certified path graphs, can
be selected without altering their internal path geometry. -/
theorem formula_semialgebraic_path_cover_from_signed_cells {ι : Type*} [Fintype ι]
    (f : PolynomialFormula (Option (Fin n))) (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (hP : ∀ p ∈ f.atomPolynomials, ∃ j, P j = p)
    (C : ι → Set (Option (Fin n) → ℝ)) (S : Set (Vec n))
    (hsa : ∀ i, IsSemialgebraic (C i))
    (hpath : ∀ i, SemialgebraicPiecewiseSmoothConnected (C i))
    (hcover : (⋃ i, C i) = {v : Option (Fin n) → ℝ | (fun j => v (some j)) ∈ S})
    (hsign : ∀ i, ∀ x ∈ C i, ∀ y ∈ C i, ∀ j,
      SignType.sign (MvPolynomial.eval x (P j)) = SignType.sign (MvPolynomial.eval y (P j))) :
    HasFiniteSemialgebraicPathCover {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ S ∧ f.Holds v} := by
  classical
  let D : Finset (Set (Option (Fin n) → ℝ)) := Finset.univ.image C
  have hD : ∀ T ∈ D, IsSemialgebraic T ∧ SemialgebraicPiecewiseSmoothConnected T := by
    intro T hT
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hT
    exact ⟨hsa i,hpath i⟩
  have hbase : ∀ i, ∀ v ∈ C i, (fun j => v (some j)) ∈ S := by
    intro i v hv
    have hm : v ∈ ⋃ i, C i := mem_iUnion.mpr ⟨i,hv⟩
    rwa [hcover] at hm
  apply finite_semialgebraic_path_cover_select D hD
  · intro v hv
    have hm : v ∈ ⋃ i, C i := by rw [hcover]; exact hv.1
    obtain ⟨i,hi⟩ := mem_iUnion.mp hm
    exact mem_iUnion.mpr ⟨C i,mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩,hi⟩⟩
  · intro T hT x hx y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hT
    change (_ ∈ S ∧ f.Holds x) ↔ (_ ∈ S ∧ f.Holds y)
    simp only [hbase i x hx,hbase i y hy,true_and]
    rw [f.holds_iff_signHolds,f.holds_iff_signHolds]
    apply f.signHolds_congr
    intro p hp
    obtain ⟨j,rfl⟩ := hP p hp
    exact hsign i x hx y hy j

end RealAlgebraicGeometry
end BfgsVerification
