import BfgsVerification.GramSchur
import BfgsVerification.PrincipalCombinatorics

noncomputable section
open scoped BigOperators
open Matrix
namespace BfgsVerification

/-- Coordinate inclusion of the axes in a finite subset. -/
def coordinateMatrix {n : ℕ} (I : Finset (Fin n)) : Matrix (Fin n) I ℝ :=
  (1 : Mat n).submatrix id Subtype.val

@[simp] theorem coordinateMatrix_gram {n : ℕ} (H : Mat n) (I : Finset (Fin n)) :
    metricGram H (coordinateMatrix I) = H.submatrix Subtype.val Subtype.val := by
  classical
  ext i j
  simp [metricGram, coordinateMatrix, Matrix.mul_apply, Matrix.one_apply, mul_ite, ite_mul]

@[simp] theorem coordinateMatrix_transpose_mulVec {n : ℕ} (x : Vec n)
    (I : Finset (Fin n)) : (coordinateMatrix I)ᵀ *ᵥ x = fun i : I => x i := by
  classical
  ext i
  simp [coordinateMatrix, Matrix.mulVec, dotProduct, Matrix.one_apply, ite_mul]

@[simp] theorem coordinateMatrix_mulVec_at {n : ℕ} (I : Finset (Fin n))
    (x : I → ℝ) (i : I) : (coordinateMatrix I *ᵥ x) i = x i := by
  classical
  unfold coordinateMatrix Matrix.mulVec dotProduct
  change ∑ j : I, (if (i : Fin n) = j then (1 : ℝ) else 0) * x j = x i
  have heq (j : I) : ((i : Fin n) = (j : Fin n)) ↔ i = j := Subtype.val_inj
  simp only [heq, ite_mul, one_mul, zero_mul]
  simp [eq_comm]

theorem coordinateMatrix_injective {n : ℕ} (I : Finset (Fin n)) :
    Function.Injective (coordinateMatrix I).mulVec := by
  intro v w hvw
  funext i
  simpa using congrFun hvw (i : Fin n)

/-- The compression on a coordinate subset is the corresponding diagonal. -/
@[simp] theorem coordinateMatrix_gram_diagonal {n : ℕ} (lam : Fin n → ℝ)
    (I : Finset (Fin n)) :
    metricGram (Matrix.diagonal lam) (coordinateMatrix I) =
      Matrix.diagonal (fun i : I => lam i) := by
  classical
  rw [coordinateMatrix_gram]
  exact Matrix.submatrix_diagonal lam (fun i : I => (i : Fin n)) Subtype.val_injective

/-- Diagonal-metric Gram determinant with one appended vector, in coordinates. -/
theorem diagonal_coordinate_gram_det {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (y : Vec n) (I : Finset (Fin n)) :
    (metricGram (Matrix.diagonal lam)
      (Matrix.fromCols (Matrix.replicateCol Unit y) (coordinateMatrix I))).det =
      (∏ i ∈ I, lam i) * (∑ k ∈ Finset.univ \ I, lam k * y k ^ 2) := by
  classical
  rw [metricGram_det_append_one_generic (Matrix.PosDef.diagonal hlam) _ _
    (coordinateMatrix_injective I), coordinateMatrix_gram_diagonal,
    Matrix.det_diagonal]
  have hinvdiag : (Matrix.diagonal (fun i : I => lam i))⁻¹ =
      Matrix.diagonal (fun i : I => (lam i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    have hi : (fun i : I => lam i * (lam i)⁻¹) = fun _ => (1 : ℝ) := by
      funext i
      exact mul_inv_cancel₀ (ne_of_gt (hlam i))
    rw [hi, Matrix.diagonal_one]
  rw [hinvdiag]
  simp only [Matrix.mulVec_diagonal, coordinateMatrix_transpose_mulVec]
  unfold metricEnergy dot dotProduct
  simp only [Matrix.mulVec_diagonal]
  have hprod : (∏ i : I, lam i) = ∏ i ∈ I, lam i := by
    exact Finset.prod_coe_sort I lam
  rw [hprod]
  congr 1
  have hinv : (∑ i : I, (lam i * y i) * ((lam i)⁻¹ * (lam i * y i))) =
      ∑ i ∈ I, lam i * y i ^ 2 := by
    rw [← Finset.sum_coe_sort I (fun i => lam i * y i ^ 2)]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [ne_of_gt (hlam i)]
    ring
  rw [hinv]
  have htotal := Finset.sum_sdiff (f := fun i => lam i * y i ^ 2)
    (Finset.subset_univ I)
  have hfull : (∑ x, y x * (lam x * y x)) = ∑ x, lam x * y x ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfull]
  linarith [htotal]

/-- Principal sums of a diagonal matrix are the actual elementary products. -/
theorem principalSum_diagonal {n : ℕ} (lam : Fin n → ℝ) (j : ℕ) :
    principalSum (Matrix.diagonal lam) j =
      ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j, ∏ i ∈ I, lam i := by
  classical
  unfold principalSum
  apply Finset.sum_congr rfl
  intro I _
  rw [← coordinateMatrix_gram, coordinateMatrix_gram_diagonal, Matrix.det_diagonal]
  exact Finset.prod_coe_sort I lam

/-- Summing the actual augmented Gram determinants in an eigenbasis yields
Module M's dimension-independent principal-sum bound. -/
theorem diagonal_coordinate_gram_sum_le {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (y : Vec n) (j : ℕ) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
      (metricGram (Matrix.diagonal lam)
        (Matrix.fromCols (Matrix.replicateCol Unit y) (coordinateMatrix I))).det) ≤
      sqNorm y * principalSum (Matrix.diagonal lam) (j + 1) := by
  classical
  simp_rw [diagonal_coordinate_gram_det lam hlam y]
  rw [principalSum_diagonal]
  exact principal_product_augmented_sum_le lam (fun i => (hlam i).le) y j

end BfgsVerification
