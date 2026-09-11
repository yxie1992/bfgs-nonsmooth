import BfgsVerification.Normalization
import BfgsVerification.ConvexAnalysis

noncomputable section
open scoped BigOperators
open Set

namespace BfgsVerification

/-- Finite-coordinate Euclidean Cauchy–Schwarz, with the actual sum of squares. -/
theorem dot_sq_le_sqNorm_mul_sqNorm {n : ℕ} (x y : Vec n) :
    (dot x y) ^ 2 ≤ sqNorm x * sqNorm y :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem abs_dot_le_of_sqNorm_le {n : ℕ} (x y : Vec n) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : sqNorm x ≤ A ^ 2) (hy : sqNorm y ≤ B ^ 2) :
    |dot x y| ≤ A * B := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA hB)).mp
  calc
    |dot x y| ^ 2 = (dot x y) ^ 2 := sq_abs _
    _ ≤ sqNorm x * sqNorm y := dot_sq_le_sqNorm_mul_sqNorm x y
    _ ≤ A ^ 2 * B ^ 2 := mul_le_mul hx hy (sqNorm_nonneg y) (sq_nonneg A)
    _ = (A * B) ^ 2 := (mul_pow A B 2).symm

theorem continuous_sqNorm {n : ℕ} : Continuous (sqNorm : Vec n → ℝ) := by
  unfold sqNorm
  fun_prop

/-- A positive Euclidean radius bound on any compact set, including empty sets. -/
theorem compact_sqNorm_radius {n : ℕ} {K : Set (Vec n)} (hK : IsCompact K) (star : Vec n) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ K, sqNorm (x - star) ≤ R ^ 2 := by
  have hc : Continuous (fun x : Vec n => sqNorm (x - star)) :=
    continuous_sqNorm.comp (continuous_id.sub continuous_const)
  obtain ⟨M, hM⟩ := hK.bddAbove_image hc.continuousOn
  refine ⟨Real.sqrt (|M| + 1), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro x hx
  rw [Real.sq_sqrt (by positivity)]
  exact (hM ⟨x, hx, rfl⟩).trans (by linarith [le_abs_self M])

theorem sqNorm_difference_le_four {n : ℕ} (x y : Vec n) (A : ℝ)
    (hx : sqNorm x ≤ A ^ 2) (hy : sqNorm y ≤ A ^ 2) :
    sqNorm (x - y) ≤ (2 * A) ^ 2 := by
  nlinarith [sqNorm_sub_le x y]

end BfgsVerification
