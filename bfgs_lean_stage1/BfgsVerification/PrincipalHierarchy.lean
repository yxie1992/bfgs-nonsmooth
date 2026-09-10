import BfgsVerification.BFGSCompression
import BfgsVerification.OrthogonalCoordinates
import BfgsVerification.CoordinateGram
import BfgsVerification.PrincipalInvariance

/-! The arbitrary-dimensional principal-minor hierarchy for full inverse BFGS. -/

noncomputable section
open scoped BigOperators Matrix
open Matrix

namespace BfgsVerification

open PrincipalInvariance

/-- An actual orthogonal diagonalization of an SPD real matrix. -/
theorem posDef_orthogonal_diagonalization {n : ℕ} {H : Mat n} (hH : H.PosDef) :
    ∃ (U : Mat n) (lam : Vec n), Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      Uᵀ * H * U = Matrix.diagonal lam ∧ (∀ i, 0 < lam i) := by
  let Q := hH.isHermitian.eigenvectorUnitary
  refine ⟨Q, hH.isHermitian.eigenvalues, ?_, ?_, ?_, hH.eigenvalues_pos⟩
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using unitary.coe_star_mul_self Q
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using unitary.coe_mul_star_self Q
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, Function.id_comp] using hH.isHermitian.star_mul_self_mul_eq_diagonal

theorem transformed_coordinateMatrix_injective {n : ℕ} (U : Mat n)
    (hU : Uᵀ * U = 1) (I : Finset (Fin n)) :
    Function.Injective (U * coordinateMatrix I).mulVec := by
  have hUinj : Function.Injective U.mulVec := by
    apply Function.LeftInverse.injective (g := Uᵀ.mulVec)
    intro x
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  intro x y hxy
  apply coordinateMatrix_injective I
  apply hUinj
  simpa only [Matrix.mulVec_mulVec] using hxy

/-- Summing the actual compressed determinants in any orthogonal basis returns
    the actual principal-determinant sum in the original coordinates. -/
theorem sum_transformed_coordinate_grams {n : ℕ} (H U : Mat n)
    (hU : Uᵀ * U = 1) (j : ℕ) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
      (metricGram H (U * coordinateMatrix I)).det) = principalSum H j := by
  simp only [metricGram_mul, coordinateMatrix_gram]
  change principalSum (Uᵀ * H * U) j = principalSum H j
  exact principalSum_conjugate Uᵀ U H hU j

/-- Module M.1 for actual principal determinants of the unmodified full
    inverse-BFGS update, in arbitrary finite dimension. -/
theorem principalMinorHierarchy : PrincipalMinorHierarchyTarget := by
  classical
  intro n H g y α hH hα
  dsimp only
  intro hq hβ j _hj1 _hjn
  let q := metricEnergy H g
  let β := -dot y (H.mulVec g) / q
  let Hplus := inverseBFGS H (bfgsStep H g α) y
  let S := (Finset.univ : Finset (Fin n)).powersetCard j
  obtain ⟨U, lam, hUL, hUR, hdiag, hlam⟩ := posDef_orthogonal_diagonalization hH
  have hpoint (I : Finset (Fin n)) :
      (metricGram Hplus (U * coordinateMatrix I)).det ≤
        (metricGram H (Matrix.fromCols (Matrix.replicateCol Unit y)
          (U * coordinateMatrix I))).det / (β ^ 2 * q) +
        α / β * (metricGram H (U * coordinateMatrix I)).det :=
    BFGSCompression.compressed_inverseBFGS_bound_generic H (U * coordinateMatrix I)
      g y α hH (transformed_coordinateMatrix_injective U hUL I) hα hq hβ
  have hgram :
      (∑ I ∈ S, (metricGram H (Matrix.fromCols (Matrix.replicateCol Unit y)
        (U * coordinateMatrix I))).det) ≤ sqNorm y * principalSum H (j + 1) := by
    calc
      _ = ∑ I ∈ S, (metricGram (Matrix.diagonal lam)
          (Matrix.fromCols (Matrix.replicateCol Unit (Uᵀ.mulVec y))
            (coordinateMatrix I))).det := by
        apply Finset.sum_congr rfl
        intro I _
        rw [metricGram_append_orthogonal H U hUR y, hdiag]
      _ ≤ sqNorm (Uᵀ.mulVec y) * principalSum (Matrix.diagonal lam) (j + 1) :=
        diagonal_coordinate_gram_sum_le lam hlam (Uᵀ.mulVec y) j
      _ = sqNorm y * principalSum H (j + 1) := by
        rw [sqNorm_orthogonal_coordinates U hUR y, ← hdiag,
          principalSum_conjugate Uᵀ U H hUL]
  change principalSum Hplus j ≤
    sqNorm y / (β ^ 2 * q) * principalSum H (j + 1) + α / β * principalSum H j
  calc
    principalSum Hplus j = ∑ I ∈ S, (metricGram Hplus (U * coordinateMatrix I)).det :=
      (sum_transformed_coordinate_grams Hplus U hUL j).symm
    _ ≤ ∑ I ∈ S,
        ((metricGram H (Matrix.fromCols (Matrix.replicateCol Unit y)
          (U * coordinateMatrix I))).det / (β ^ 2 * q) +
        α / β * (metricGram H (U * coordinateMatrix I)).det) :=
      Finset.sum_le_sum (fun I _ => hpoint I)
    _ = (∑ I ∈ S, (metricGram H (Matrix.fromCols (Matrix.replicateCol Unit y)
          (U * coordinateMatrix I))).det) / (β ^ 2 * q) + α / β * principalSum H j := by
      simp only [Finset.sum_add_distrib, Finset.sum_div, ← Finset.mul_sum]
      rw [show (∑ I ∈ S, (metricGram H (U * coordinateMatrix I)).det) =
        principalSum H j from sum_transformed_coordinate_grams H U hUL j]
    _ ≤ (sqNorm y * principalSum H (j + 1)) / (β ^ 2 * q) +
        α / β * principalSum H j := by
      exact add_le_add_right (div_le_div_of_nonneg_right hgram (by positivity)) _
    _ = sqNorm y / (β ^ 2 * q) * principalSum H (j + 1) + α / β * principalSum H j := by
      ring

end BfgsVerification
