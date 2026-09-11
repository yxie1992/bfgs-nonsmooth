import BfgsVerification.ObjectiveDefinitions
import Mathlib.Data.Finset.Max

/-! Exact finite cylindrical graph/gap partition from actual strictly ordered
boundary values. This does not assume root delineability or cell decomposition. -/
noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {E : Type*} {r : ℕ}

def orderedGraphCell (S : Set E) (f : Fin r → E → ℝ) (i : Fin r) : Set (E × ℝ) :=
  {z | z.1 ∈ S ∧ z.2 = f i z.1}

def orderedGapCell (S : Set E) (f : Fin r → E → ℝ) (j : Fin (r+1)) : Set (E × ℝ) :=
  {z | z.1 ∈ S ∧ (∀ i : Fin r, i.val < j.val → f i z.1 < z.2) ∧
    (∀ i : Fin r, j.val ≤ i.val → z.2 < f i z.1)}

def orderedCylindricalCell (S : Set E) (f : Fin r → E → ℝ) :
    Fin r ⊕ Fin (r+1) → Set (E × ℝ)
  | .inl i => orderedGraphCell S f i
  | .inr j => orderedGapCell S f j

theorem ordered_gap_contains_nonboundary {f : Fin r → ℝ} (hf : StrictMono f) (t : ℝ)
    (hne : ∀ i, f i ≠ t) :
    ∃ j : Fin (r+1), (∀ i : Fin r, i.val < j.val → f i < t) ∧
      (∀ i : Fin r, j.val ≤ i.val → t < f i) := by
  classical
  let I := Finset.univ.filter (fun i : Fin r => t < f i)
  by_cases hI : I.Nonempty
  · let k : Fin r := I.min' hI
    have hk : t < f k := (Finset.mem_filter.mp (Finset.min'_mem I hI)).2
    refine ⟨⟨k.val, by omega⟩, ?_, ?_⟩
    · intro i hi
      change i.val < k.val at hi
      apply lt_of_le_of_ne ?_ (hne i)
      by_contra h
      have hiI : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩
      have hki : k ≤ i := Finset.min'_le I i hiI
      have hv : k.val ≤ i.val := hki
      omega
    · intro i hi
      change k.val ≤ i.val at hi
      exact hk.trans_le (hf.monotone (show k ≤ i from hi))
  · refine ⟨⟨r, by omega⟩, ?_, ?_⟩
    · intro i _
      have hle : f i ≤ t := le_of_not_gt (fun h => hI
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩)
      exact lt_of_le_of_ne hle (hne i)
    · intro i hi
      change r ≤ i.val at hi
      exact (False.elim (by have := i.isLt; omega))

theorem orderedCylindricalCell_cover (S : Set E) (f : Fin r → E → ℝ)
    (hf : ∀ x ∈ S, StrictMono (fun i => f i x)) :
    (⋃ i, orderedCylindricalCell S f i) = {z : E × ℝ | z.1 ∈ S} := by
  ext z
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, hz⟩
    cases i with
    | inl i => exact hz.1
    | inr j => exact hz.1
  · intro hz
    by_cases he : ∃ i, f i z.1 = z.2
    · obtain ⟨i, hi⟩ := he
      exact mem_iUnion.mpr ⟨.inl i, hz, hi.symm⟩
    · obtain ⟨j, hj⟩ := ordered_gap_contains_nonboundary (hf z.1 hz) z.2
        (fun i hi => he ⟨i, hi⟩)
      exact mem_iUnion.mpr ⟨.inr j, hz, hj⟩

theorem orderedGraphCell_disjoint_gap (S : Set E) (f : Fin r → E → ℝ)
    (i : Fin r) (j : Fin (r+1)) : Disjoint (orderedGraphCell S f i) (orderedGapCell S f j) := by
  apply Set.disjoint_left.mpr
  intro z hg hj
  by_cases hij : i.val < j.val
  · have h := hj.2.1 i hij
    rw [hg.2] at h
    exact lt_irrefl _ h
  · have h := hj.2.2 i (Nat.le_of_not_gt hij)
    rw [hg.2] at h
    exact lt_irrefl _ h

theorem orderedGapCell_disjoint (S : Set E) (f : Fin r → E → ℝ)
    {i j : Fin (r+1)} (hij : i < j) : Disjoint (orderedGapCell S f i) (orderedGapCell S f j) := by
  apply Set.disjoint_left.mpr
  intro z hi hj
  have hiv : i.val < j.val := hij
  let k : Fin r := ⟨i.val, by have := j.isLt; omega⟩
  exact lt_asymm (hi.2.2 k (by rfl)) (hj.2.1 k hiv)

theorem orderedCylindricalCell_pairwise_disjoint (S : Set E) (f : Fin r → E → ℝ)
    (hf : ∀ x ∈ S, StrictMono (fun i => f i x)) :
    Pairwise (fun i j => Disjoint (orderedCylindricalCell S f i) (orderedCylindricalCell S f j)) := by
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · apply Set.disjoint_left.mpr
    intro z hi hj
    apply hij
    congr 1
    exact (hf z.1 hi.1).injective (hi.2.symm.trans hj.2)
  · exact orderedGraphCell_disjoint_gap S f i j
  · exact (orderedGraphCell_disjoint_gap S f j i).symm
  · have hne : i ≠ j := fun h => hij (congrArg Sum.inr h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact orderedGapCell_disjoint S f h
    · exact (orderedGapCell_disjoint S f h).symm

end RealAlgebraicGeometry
end BfgsVerification
