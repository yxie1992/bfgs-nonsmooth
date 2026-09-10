import BfgsVerification.GramSchur

/-! Coordinate changes used in summing actual compressed determinants. -/

noncomputable section
open Matrix

namespace BfgsVerification

theorem metricGram_mul {n : ℕ} {ι : Type*} (H U : Mat n) (X : Matrix (Fin n) ι ℝ) :
    metricGram H (U * X) = metricGram (Uᵀ * H * U) X := by
  simp only [metricGram, Matrix.transpose_mul, Matrix.mul_assoc]

theorem sqNorm_orthogonal_coordinates {n : ℕ} (U : Mat n)
    (hU : U * Uᵀ = 1) (y : Vec n) : sqNorm (Uᵀ *ᵥ y) = sqNorm y := by
  have hnorm (x : Vec n) : sqNorm x = x ⬝ᵥ x := by
    simp only [sqNorm, dotProduct, pow_two]
  rw [hnorm, hnorm, dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.transpose_transpose, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

theorem metricGram_append_orthogonal {n : ℕ} {ι : Type*} (H U : Mat n)
    (hU : U * Uᵀ = 1) (y : Vec n) (X : Matrix (Fin n) ι ℝ) :
    metricGram H (Matrix.fromCols (Matrix.replicateCol Unit y) (U * X)) =
      metricGram (Uᵀ * H * U)
        (Matrix.fromCols (Matrix.replicateCol Unit (Uᵀ *ᵥ y)) X) := by
  have hy : U * Matrix.replicateCol Unit (Uᵀ *ᵥ y) = Matrix.replicateCol Unit y := by
    rw [← Matrix.replicateCol_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  have hcols : Matrix.fromCols (Matrix.replicateCol Unit y) (U * X) =
      U * Matrix.fromCols (Matrix.replicateCol Unit (Uᵀ *ᵥ y)) X := by
    rw [Matrix.mul_fromCols, hy]
  rw [hcols]
  simp only [metricGram, Matrix.transpose_mul, Matrix.mul_assoc]

end BfgsVerification
