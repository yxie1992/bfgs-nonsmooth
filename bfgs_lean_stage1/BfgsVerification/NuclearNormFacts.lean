import BfgsVerification.NuclearVariational

/-! Norm properties derived from the checked polar variational formula. -/
noncomputable section
open scoped BigOperators Matrix.L2OpNorm
open Matrix Set
namespace BfgsVerification.RectangularNuclear
variable {m n : ℕ}

theorem pairing_neg_right (A B : Matrix (Fin m) (Fin n) ℝ) :
    pairing A (-B)= -pairing A B := by
  simp only [pairing,Matrix.mul_neg,Matrix.trace_neg]

theorem pairing_neg_left (A B : Matrix (Fin m) (Fin n) ℝ) :
    pairing (-A) B= -pairing A B := by
  simp only [pairing,Matrix.transpose_neg,Matrix.neg_mul,Matrix.trace_neg]

theorem nuclear_zero (m n : ℕ) : nuclear (0 : Matrix (Fin m) (Fin n) ℝ)=0 := by
  rw [← pairing_polar]
  simp only [pairing,Matrix.transpose_zero,Matrix.zero_mul,Matrix.trace_zero]

theorem nuclear_add_le (A B : Matrix (Fin m) (Fin n) ℝ) :
    nuclear (A+B) ≤ nuclear A+nuclear B := by
  rw [← pairing_polar (A+B),pairing_add_left]
  exact add_le_add ((nuclear_variational A).1 _ (polar_opNorm_le_one (A+B)))
    ((nuclear_variational B).1 _ (polar_opNorm_le_one (A+B)))

theorem nuclear_smul_nonneg (t : ℝ) (ht : 0 ≤ t) (A : Matrix (Fin m) (Fin n) ℝ) :
    nuclear (t • A)=t*nuclear A := by
  apply le_antisymm
  · rw [← pairing_polar (t • A),pairing_smul_left]
    exact mul_le_mul_of_nonneg_left ((nuclear_variational A).1 _ (polar_opNorm_le_one (t • A))) ht
  · have h := (nuclear_variational (t • A)).1 (polar A) (polar_opNorm_le_one A)
    rwa [pairing_smul_left,pairing_polar] at h

theorem nuclear_neg (A : Matrix (Fin m) (Fin n) ℝ) : nuclear (-A)=nuclear A := by
  have h (B : Matrix (Fin m) (Fin n) ℝ) : nuclear (-B) ≤ nuclear B := by
    rw [← pairing_polar (-B),pairing_neg_left,← pairing_neg_right]
    exact (nuclear_variational B).1 _ (by simpa only [norm_neg] using polar_opNorm_le_one (-B))
  exact le_antisymm (h A) (by simpa only [neg_neg] using h (-A))

theorem nuclear_smul (t : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    nuclear (t • A)=‖t‖*nuclear A := by
  by_cases ht : 0 ≤ t
  · rw [nuclear_smul_nonneg t ht,Real.norm_of_nonneg ht]
  · have he : t • A = -((-t) • A) := by simp only [neg_smul,neg_neg]
    rw [he,nuclear_neg,nuclear_smul_nonneg (-t) (by linarith),Real.norm_of_nonpos (by linarith)]

/-- A bundled seminorm constructed from proved additivity bounds and exact
homogeneity of the literal singular-value sum. No norm structure is assumed. -/
def nuclearSeminorm (m n : ℕ) : Seminorm ℝ (Matrix (Fin m) (Fin n) ℝ) :=
  Seminorm.of nuclear nuclear_add_le nuclear_smul

theorem entry_sq_le_pairing_self (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    A i j^2 ≤ pairing A A := by
  rw [pairing_eq_sum]
  calc
    A i j^2 ≤ ∑ k : Fin m, A k j*A k j := by
      simpa only [pow_two] using Finset.single_le_sum
        (fun k (_ : k ∈ (Finset.univ : Finset (Fin m))) => mul_self_nonneg (A k j))
        (Finset.mem_univ i)
    _ ≤ ∑ l : Fin n, ∑ k : Fin m, A k l*A k l :=
      Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => mul_self_nonneg (A k l)))
        (Finset.mem_univ j)

theorem nuclear_eq_zero_iff (A : Matrix (Fin m) (Fin n) ℝ) : nuclear A=0 ↔ A=0 := by
  refine ⟨fun h => ?_,fun h => h ▸ nuclear_zero m n⟩
  have hh : pairing A A ≤ 0 := by
    simpa only [h,zero_mul] using pairing_le_nuclear_mul_opNorm A A
  ext i j
  exact sq_eq_zero_iff.mp (le_antisymm ((entry_sq_le_pairing_self A i j).trans hh) (sq_nonneg _))

theorem nuclear_convex (m n : ℕ) : ConvexOn ℝ univ (nuclear (m := m) (n := n)) :=
  (nuclearSeminorm m n).convexOn

/-- The spectral value on each finite rectangular matrix is literally the sum
of the nonnegative square roots of all Gram eigenvalues, with multiplicities. -/
theorem nuclear_eq_sum_singularValues (A : Matrix (Fin m) (Fin n) ℝ) :
    nuclear A = ∑ i : Fin n, Real.sqrt ((Matrix.isHermitian_transpose_mul_self A).eigenvalues i) := rfl

end BfgsVerification.RectangularNuclear
