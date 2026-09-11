import BfgsVerification.UnivariateSemialgebraicCells

/-! The constructed one-dimensional cells have the usual actual geometry:
root-free pieces are open and semialgebraic, and boundary pieces are singletons.
This is a derived fixed-dimensional decomposition, with no projection premise. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- Pull a subset of the real line back to the existing one-coordinate space. -/
def univariateLift (S : Set ℝ) : Set (Unit → ℝ) := {x | x () ∈ S}

theorem rootFreeCell_eq_inter {B S : Finset ℝ} (hS : S ⊆ B) :
    rootFreeCell B S = ⋂ b ∈ B, {x : ℝ | if b ∈ S then b < x else x < b} := by
  classical
  ext x
  simp only [mem_iInter,mem_setOf_eq]
  constructor
  · intro hx b hb
    have hm : b ∈ S ↔ b < x := by
      rw [← hx.2]
      simp only [cutProfile,Finset.mem_filter,and_iff_right hb]
    split_ifs with h
    · exact hm.mp h
    · have hbx : ¬b < x := fun hbx => h (hm.mpr hbx)
      exact lt_of_le_of_ne (le_of_not_gt hbx) (fun he => hx.1 (he.symm ▸ hb))
  · intro hx
    have hxb : x ∉ B := by
      intro hxb
      have h := hx x hxb
      split_ifs at h <;> exact lt_irrefl _ h
    refine ⟨hxb,?_⟩
    ext b
    simp only [cutProfile,Finset.mem_filter]
    constructor
    · rintro ⟨hb,hbx⟩
      by_contra hbS
      have h := hx b hb
      rw [if_neg hbS] at h
      exact (not_lt_of_ge h.le) hbx
    · intro hbS
      have h := hx b (hS hbS)
      rw [if_pos hbS] at h
      exact ⟨hS hbS,h⟩

theorem rootFreeCell_isOpen {B S : Finset ℝ} (hS : S ⊆ B) :
    IsOpen (rootFreeCell B S) := by
  classical
  rw [rootFreeCell_eq_inter hS]
  apply isOpen_biInter_finset
  intro b hb
  by_cases hbS : b ∈ S
  · simpa only [if_pos hbS] using (isOpen_lt continuous_const continuous_id : IsOpen {x : ℝ | b < x})
  · simpa only [if_neg hbS] using (isOpen_lt continuous_id continuous_const : IsOpen {x : ℝ | x < b})

theorem rootFreeCell_semialgebraic {B S : Finset ℝ} (hS : S ⊆ B) :
    IsSemialgebraic (univariateLift (rootFreeCell B S)) := by
  classical
  have h := isSemialgebraic_finset_inter B
    (fun b => {x : Unit → ℝ | if b ∈ S then b < x () else x () < b}) (fun b hb => ?_)
  · convert h using 1
    ext x
    simp only [univariateLift,mem_setOf_eq,rootFreeCell_eq_inter hS,mem_iInter]
  · by_cases hbS : b ∈ S
    · have h := isSemialgebraic_positive (X () - C b : MvPolynomial Unit ℝ)
      convert h using 1
      ext x
      simp only [mem_setOf_eq,if_pos hbS,MvPolynomial.eval_sub,MvPolynomial.eval_X,MvPolynomial.eval_C,sub_pos]
    · have h := isSemialgebraic_positive (C b - X () : MvPolynomial Unit ℝ)
      convert h using 1
      ext x
      simp only [mem_setOf_eq,if_neg hbS,MvPolynomial.eval_sub,MvPolynomial.eval_X,MvPolynomial.eval_C,sub_pos]

theorem rootCells_semialgebraic (B : Finset ℝ) {S : Set ℝ} (hS : S ∈ rootCells B) :
    IsSemialgebraic (univariateLift S) := by
  classical
  rcases Finset.mem_union.mp hS with h | h
  · obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp h
    exact rootFreeCell_semialgebraic (Finset.mem_powerset.mp hC)
  · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp h
    have h := isSemialgebraic_equal_zero (X () - C b : MvPolynomial Unit ℝ)
    convert h using 1
    ext x
    simp only [univariateLift,mem_setOf_eq,mem_singleton_iff,MvPolynomial.eval_sub,MvPolynomial.eval_X,MvPolynomial.eval_C,sub_eq_zero]

theorem rootCells_open_or_singleton (B : Finset ℝ) {S : Set ℝ} (hS : S ∈ rootCells B) :
    IsOpen S ∨ ∃ b : ℝ, S = {b} := by
  classical
  rcases Finset.mem_union.mp hS with h | h
  · obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp h
    exact Or.inl (rootFreeCell_isOpen (Finset.mem_powerset.mp hC))
  · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨b,rfl⟩

end RealAlgebraicGeometry
end BfgsVerification
