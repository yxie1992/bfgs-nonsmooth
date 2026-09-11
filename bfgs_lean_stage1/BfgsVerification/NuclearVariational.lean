import BfgsVerification.NuclearGram

/-! Polar contraction and variational characterization of the literal nuclear norm. -/
noncomputable section
open scoped BigOperators Matrix.L2OpNorm InnerProductSpace
open Matrix
namespace BfgsVerification.RectangularNuclear
variable {m n : ℕ}

def column (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) : EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => A j i)

theorem column_norm_sq (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    ‖column A i‖^2=(Aᵀ*A) i i := by
  rw [FrameNorms.euclidean_norm_sq]
  change (∑ j, A j i^2) = ∑ j, A j i*A j i
  simp only [pow_two]

theorem column_inner (A B : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    (Aᵀ*B) i i=⟪column A i,column B i⟫_ℝ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct_comm]
  rfl

theorem column_mul_norm_le {l : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin l) ℝ) (i : Fin l) :
    ‖column (A*B) i‖ ≤ ‖A‖*‖column B i‖ := by
  exact Matrix.l2_opNorm_mulVec A (column B i)

theorem rightFrame_column_norm (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    ‖column (rightFrame A) i‖=1 := by
  have h := column_norm_sq (rightFrame A) i
  rw [rightFrame_transpose_mul,Matrix.one_apply_eq] at h
  nlinarith [norm_nonneg (column (rightFrame A) i)]

theorem spectral_column_norm (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    ‖column (A*rightFrame A) i‖=singularValues A i := by
  apply (sq_eq_sq₀ (norm_nonneg _) (singularValues_nonneg A i)).mp
  rw [column_norm_sq,rightFrame_gram,Matrix.diagonal_apply_eq,singularValues_sq]

/-- Every rectangular matrix pairs below the sum of singular values times the
actual Euclidean operator norm of its partner. -/
theorem pairing_le_nuclear_mul_opNorm (A B : Matrix (Fin m) (Fin n) ℝ) :
    pairing A B ≤ nuclear A*‖B‖ := by
  rw [← pairing_right_orthogonal A B (rightFrame A) (rightFrame_mul_transpose A)]
  unfold pairing nuclear Matrix.trace Matrix.diag
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [column_inner]
  calc
    ⟪column (A*rightFrame A) i,column (B*rightFrame A) i⟫_ℝ ≤
        ‖column (A*rightFrame A) i‖*‖column (B*rightFrame A) i‖ := real_inner_le_norm _ _
    _ ≤ singularValues A i*‖B‖ := by
      rw [spectral_column_norm]
      apply mul_le_mul_of_nonneg_left _ (singularValues_nonneg A i)
      simpa only [rightFrame_column_norm,mul_one] using column_mul_norm_le B (rightFrame A) i

/-- The polar partial isometry retains zero singular directions as zero. -/
def polar (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  normalizedColumns A*(rightFrame A)ᵀ

theorem polar_opNorm_le_one (A : Matrix (Fin m) (Fin n) ℝ) : ‖polar A‖ ≤ 1 := by
  calc
    ‖polar A‖ ≤ ‖normalizedColumns A‖*‖(rightFrame A)ᵀ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1*1 := mul_le_mul (normalizedColumns_opNorm_le_one A)
      (orthogonal_opNorm_le_one _ (by simpa only [transpose_transpose] using rightFrame_mul_transpose A))
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem polar_rightFrame (A : Matrix (Fin m) (Fin n) ℝ) :
    polar A*rightFrame A=normalizedColumns A := by
  simp only [polar,Matrix.mul_assoc,rightFrame_transpose_mul,Matrix.mul_one]

/-- The contraction attains the literal sum of Gram square-root eigenvalues. -/
theorem pairing_polar (A : Matrix (Fin m) (Fin n) ℝ) : pairing A (polar A)=nuclear A := by
  rw [← pairing_right_orthogonal A (polar A) (rightFrame A) (rightFrame_mul_transpose A),
    polar_rightFrame]
  unfold pairing normalizedColumns
  rw [← Matrix.mul_assoc,rightFrame_gram,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal]
  unfold nuclear
  apply Finset.sum_congr rfl
  intro i _
  rw [← singularValues_sq]
  by_cases h : singularValues A i=0
  · simp [h]
  · simp [pow_two,h,mul_assoc]

/-- Exact variational definition, with an actual attaining matrix and no
rank, nonzero dimension, or positive singular-value assumptions. -/
theorem nuclear_variational (A : Matrix (Fin m) (Fin n) ℝ) :
    (∀ B : Matrix (Fin m) (Fin n) ℝ, ‖B‖ ≤ 1 → pairing A B ≤ nuclear A) ∧
      ∃ B : Matrix (Fin m) (Fin n) ℝ, ‖B‖ ≤ 1 ∧ pairing A B=nuclear A := by
  refine ⟨fun B hB => (pairing_le_nuclear_mul_opNorm A B).trans ?_,
    ⟨polar A,polar_opNorm_le_one A,pairing_polar A⟩⟩
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hB (nuclear_nonneg A)

/-- The same literal norm is the trace of the canonical PSD Gram square root. -/
theorem nuclear_eq_trace_sqrt (A : Matrix (Fin m) (Fin n) ℝ) :
    nuclear A=Matrix.trace (Matrix.posSemidef_conjTranspose_mul_self A).sqrt := by
  unfold Matrix.PosSemidef.sqrt
  rw [Matrix.trace_mul_cycle,unitary.coe_star_mul_self,Matrix.one_mul,Matrix.trace_diagonal]
  rfl

end BfgsVerification.RectangularNuclear
