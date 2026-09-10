import BfgsVerification.Definitions

/-!
# Actual principal determinants: elementary matrix facts

These declarations concern the `principalSum` in `Definitions`, not an abstract
sequence. The full BFGS principal-minor hierarchy is a separate obligation.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace BfgsVerification

/-- Every determinant of a real positive semidefinite matrix is nonnegative,
including singular matrices and the empty matrix. -/
theorem det_nonneg_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.PosSemidef) : 0 ≤ H.det := by
  rw [hH.isHermitian.det_eq_prod_eigenvalues]
  exact Finset.prod_nonneg (fun i _ => hH.eigenvalues_nonneg i)

/-- All actual principal sums of a PSD matrix are nonnegative. -/
theorem principalSum_nonneg {n : ℕ} {H : Mat n} (hH : H.PosSemidef) (j : ℕ) :
    0 ≤ principalSum H j := by
  classical
  unfold principalSum
  exact Finset.sum_nonneg fun I _ => det_nonneg_of_posSemidef (hH.submatrix _)

/-- The terminal slot vanishes because there are no such coordinate subsets. -/
theorem principalSum_eq_zero_of_dimension_lt {n j : ℕ} (H : Mat n) (hj : n < j) :
    principalSum H j = 0 := by
  classical
  unfold principalSum
  have hempty : (Finset.univ : Finset (Fin n)).powersetCard j = ∅ := by
    apply Finset.powersetCard_eq_empty.mpr
    simpa using hj
  rw [hempty, Finset.sum_empty]

@[simp] theorem principalSum_terminal {n : ℕ} (H : Mat n) :
    principalSum H (n + 1) = 0 :=
  principalSum_eq_zero_of_dimension_lt H (Nat.lt_succ_self n)

/-- The actual degree-one principal sum is exactly the trace. -/
@[simp] theorem principalSum_one {n : ℕ} (H : Mat n) :
    principalSum H 1 = Matrix.trace H := by
  classical
  unfold principalSum
  rw [Finset.powersetCard_one, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  change (H.submatrix (fun x : ({i} : Finset (Fin n)) => (x : Fin n))
    (fun x : ({i} : Finset (Fin n)) => (x : Fin n))).det = H i i
  exact Matrix.det_eq_elem_of_card_eq_one (A := H.submatrix
    (fun x : ({i} : Finset (Fin n)) => (x : Fin n))
    (fun x : ({i} : Finset (Fin n)) => (x : Fin n))) (by simp) ⟨i, by simp⟩

/-- The top principal sum is exactly the determinant. -/
@[simp] theorem principalSum_top {n : ℕ} (H : Mat n) :
    principalSum H n = Matrix.det H := by
  classical
  unfold principalSum
  have hp : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [hp, Finset.sum_singleton]
  let e : (Finset.univ : Finset (Fin n)) ≃ Fin n :=
    ⟨Subtype.val, (fun i => ⟨i, Finset.mem_univ i⟩), (fun _ => rfl), (fun _ => rfl)⟩
  exact Matrix.det_submatrix_equiv_self e H

/-- Strictly positive diagonal entries are a consequence of positive definiteness. -/
theorem diagonal_pos_of_posDef {n : ℕ} {H : Mat n} (hH : H.PosDef) (i : Fin n) :
    0 < H i i := by
  have hi : (Pi.single i (1 : ℝ) : Vec n) ≠ 0 := by
    intro h
    have := congrFun h i
    simp at this
  simpa using hH.2 (Pi.single i 1) hi

/-- Positive dimension and SPD imply strictly positive trace. -/
theorem trace_pos_of_posDef {n : ℕ} {H : Mat n} (hH : H.PosDef) (hn : 0 < n) :
    0 < Matrix.trace H := by
  classical
  change 0 < ∑ i, H i i
  apply Finset.sum_pos'
  · intro i _
    exact (diagonal_pos_of_posDef hH i).le
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _, diagonal_pos_of_posDef hH _⟩

theorem principalSum_one_pos {n : ℕ} {H : Mat n} (hH : H.PosDef) (hn : 0 < n) :
    0 < principalSum H 1 := by
  rw [principalSum_one]
  exact trace_pos_of_posDef hH hn

end BfgsVerification
