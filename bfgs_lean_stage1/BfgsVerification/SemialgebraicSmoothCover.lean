import BfgsVerification.FiniteCoverOnSignature
import BfgsVerification.ReindexedSmoothCovers
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section
open Filter Set Polynomial
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n m : ℕ}

theorem formula_cover_on_zero_pattern (ih : SmoothCoverDimension n)
    (f : PolynomialFormula (Option (Fin n))) (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (hP : ∀ p ∈ f.atomPolynomials, ∃ j, P j = p) (Z : Finset (Fin m)) :
    HasFiniteSmoothSemialgebraicCover {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ zeroFiberPattern P Z ∧ f.Holds v} := by
  classical
  let p := survivingPolynomialProduct P Z
  let q := MvPolynomial.optionEquivLeft ℝ (Fin n) p
  obtain ⟨C,hsa,hcover⟩ := finite_rootSignature_cover q
  let B : C → Set (Vec n) := fun a => zeroFiberPattern P Z ∩ rootSignatureStratum q a
  have hB : ∀ a : C, HasFiniteSmoothSemialgebraicCover {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ B a ∧ f.Holds v} := by
    intro a
    exact formula_cover_on_root_signature ih f P hP Z a (B a)
      ((zeroFiberPattern_semialgebraic P Z).inter (hsa a a.2))
      inter_subset_left inter_subset_right
  have h := restricted_formula_cover_iUnion f B hB
  have he : (⋃ a, B a) = zeroFiberPattern P Z := by
    ext x
    constructor
    · intro hx
      obtain ⟨a,ha⟩ := mem_iUnion.mp hx
      exact ha.1
    · intro hx
      have hr : x ∈ ⋃ a ∈ C, rootSignatureStratum q a := by rw [hcover]; exact mem_univ x
      obtain ⟨a,hax⟩ := mem_iUnion.mp hr
      obtain ⟨ha,hxa⟩ := mem_iUnion.mp hax
      exact mem_iUnion.mpr ⟨⟨a,ha⟩,hx,hxa⟩
  simpa only [he] using h

theorem formula_cover_of_lower_dimension (ih : SmoothCoverDimension n)
    (f : PolynomialFormula (Option (Fin n))) :
    HasFiniteSmoothSemialgebraicCover {v : Option (Fin n) → ℝ | f.Holds v} := by
  classical
  let e := Fintype.equivFin f.atomPolynomials
  let P : Fin (Fintype.card f.atomPolynomials) → MvPolynomial (Option (Fin n)) ℝ :=
    fun j => (e.symm j).val
  have hP : ∀ p ∈ f.atomPolynomials, ∃ j, P j = p := by
    intro p hp
    refine ⟨e ⟨p,hp⟩,?_⟩
    exact congrArg Subtype.val (e.symm_apply_apply ⟨p,hp⟩)
  have h := restricted_formula_cover_iUnion f (zeroFiberPattern P)
    (fun Z => formula_cover_on_zero_pattern ih f P hP Z)
  simpa only [zeroFiberPatterns_cover,mem_univ,true_and] using h

theorem smoothCoverDimension_succ (ih : SmoothCoverDimension n) : SmoothCoverDimension (n+1) := by
  intro S hS
  let e := finSuccEquiv n
  have hT := hS.reindex e
  obtain ⟨f,hf⟩ := hT
  have h := formula_cover_of_lower_dimension ih f
  have he : {v : Option (Fin n) → ℝ | f.Holds v} =
      {v : Option (Fin n) → ℝ | (fun j => v (e j)) ∈ S} := by
    ext v
    exact (hf v).symm
  rw [he] at h
  have h' := h.reindex e.symm
  simpa only [mem_setOf_eq,Equiv.symm_apply_apply,Set.setOf_mem_eq] using h'

/-- Constructive finite smooth cover for every genuine semialgebraic set in
arbitrary finite real dimension. All polynomial projection, root counting,
root charts, finite refinements and the dimension induction are discharged. -/
theorem semialgebraic_finite_smooth_cover_fin (n : ℕ) : SmoothCoverDimension n := by
  induction n with
  | zero => exact fun S hS => finite_smooth_cover_dimension_zero hS
  | succ n ih => exact smoothCoverDimension_succ ih

theorem semialgebraic_finite_smooth_cover {σ : Type*} [Fintype σ]
    {S : Set (σ → ℝ)} (hS : IsSemialgebraic S) : HasFiniteSmoothSemialgebraicCover S := by
  let e := Fintype.equivFin σ
  have h := semialgebraic_finite_smooth_cover_fin (Fintype.card σ) _ (hS.reindex e)
  have h' := h.reindex e.symm
  simpa only [mem_setOf_eq,Equiv.symm_apply_apply,Set.setOf_mem_eq] using h'

end RealAlgebraicGeometry
end BfgsVerification
