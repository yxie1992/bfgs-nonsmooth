import BfgsVerification.OrderedCylindricalCover
import BfgsVerification.SmoothCylindricalConnectivity

noncomputable section
open Set
open scoped ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {E : Type*} {r : ℕ}

theorem orderedGapCell_empty (S : Set E) (f : Fin 0 → E → ℝ) (j : Fin 1) :
    orderedGapCell S f j = {z : E × ℝ | z.1 ∈ S} := by
  ext z
  simp [orderedGapCell]

theorem orderedGapCell_bottom (S : Set E) (f : Fin r → E → ℝ)
    (hf : ∀ x ∈ S, StrictMono (fun i => f i x)) (hr : 0 < r)
    (j : Fin (r+1)) (hj : j.val = 0) :
    orderedGapCell S f j = {z : E × ℝ | z.1 ∈ S ∧ z.2 < f ⟨0,hr⟩ z.1} := by
  ext z
  constructor
  · intro hz
    exact ⟨hz.1, hz.2.2 ⟨0,hr⟩ (by simp [hj])⟩
  · rintro ⟨hz, ht⟩
    refine ⟨hz, ?_, ?_⟩
    · intro i hi
      omega
    · intro i _
      exact ht.trans_le ((hf z.1 hz).monotone (show (⟨0,hr⟩ : Fin r) ≤ i from Nat.zero_le _))

theorem orderedGapCell_top (S : Set E) (f : Fin r → E → ℝ)
    (hf : ∀ x ∈ S, StrictMono (fun i => f i x)) (hr : 0 < r)
    (j : Fin (r+1)) (hj : j.val = r) :
    orderedGapCell S f j =
      {z : E × ℝ | z.1 ∈ S ∧ f ⟨r-1,by omega⟩ z.1 < z.2} := by
  ext z
  constructor
  · intro hz
    exact ⟨hz.1, hz.2.1 ⟨r-1,by omega⟩ (by simp only [hj]; omega)⟩
  · rintro ⟨hz, ht⟩
    refine ⟨hz, ?_, ?_⟩
    · intro i _
      apply lt_of_le_of_lt ((hf z.1 hz).monotone ?_) ht
      change i.val ≤ r-1
      have := i.isLt
      omega
    · intro i hi
      have := i.isLt
      omega

theorem orderedGapCell_middle (S : Set E) (f : Fin r → E → ℝ)
    (hf : ∀ x ∈ S, StrictMono (fun i => f i x))
    (j : Fin (r+1)) (hj : 0 < j.val) (hjr : j.val < r) :
    orderedGapCell S f j = {z : E × ℝ | z.1 ∈ S ∧
      f ⟨j.val-1,by omega⟩ z.1 < z.2 ∧ z.2 < f ⟨j.val,hjr⟩ z.1} := by
  ext z
  constructor
  · intro hz
    exact ⟨hz.1, hz.2.1 ⟨j.val-1,by omega⟩ (by dsimp; omega),
      hz.2.2 ⟨j.val,hjr⟩ (by rfl)⟩
  · rintro ⟨hz, hl, hu⟩
    refine ⟨hz, ?_, ?_⟩
    · intro i hi
      apply lt_of_le_of_lt ((hf z.1 hz).monotone ?_) hl
      change i.val ≤ j.val-1
      omega
    · intro i hi
      exact hu.trans_le ((hf z.1 hz).monotone (show (⟨j.val,hjr⟩ : Fin r) ≤ i from hi))

theorem orderedGapCell_piecewiseSmoothConnected [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (f : Fin r → E → ℝ) (hS : PiecewiseSmoothConnected S)
    (hsm : ∀ i, ContDiffOn ℝ ∞ (f i) S)
    (hf : ∀ x ∈ S, StrictMono (fun i => f i x)) (j : Fin (r+1)) :
    PiecewiseSmoothConnected (orderedGapCell S f j) := by
  by_cases hr : r = 0
  · subst r
    rw [orderedGapCell_empty]
    exact hS.full_cylinder
  have hrp : 0 < r := Nat.pos_of_ne_zero hr
  by_cases hj0 : j.val = 0
  · rw [orderedGapCell_bottom S f hf hrp j hj0]
    exact hS.lower_band (hsm _)
  by_cases hjr : j.val = r
  · rw [orderedGapCell_top S f hf hrp j hjr]
    exact hS.upper_band (hsm _)
  have hjp : 0 < j.val := Nat.pos_of_ne_zero hj0
  have hjlt : j.val < r := by have := j.isLt; omega
  rw [orderedGapCell_middle S f hf j hjp hjlt]
  apply hS.open_band (hsm _) (hsm _)
  intro x hx
  apply hf x hx
  change j.val-1 < j.val
  omega

theorem orderedCylindricalCell_piecewiseSmoothConnected [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (f : Fin r → E → ℝ) (hS : PiecewiseSmoothConnected S)
    (hsm : ∀ i, ContDiffOn ℝ ∞ (f i) S)
    (hf : ∀ x ∈ S, StrictMono (fun i => f i x))
    (i : Fin r ⊕ Fin (r+1)) : PiecewiseSmoothConnected (orderedCylindricalCell S f i) := by
  rcases i with i | j
  · exact hS.graph (hsm i)
  · exact orderedGapCell_piecewiseSmoothConnected S f hS hsm hf j

end RealAlgebraicGeometry
end BfgsVerification
