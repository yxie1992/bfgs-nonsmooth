import BfgsVerification.Definitions

/-!
# Actual rank-two compression determinants

The base matrix is invertible and symmetric. No invertibility of the rank-two
perturbation is required, so the identities include singular compressions.
-/

noncomputable section
open scoped BigOperators Matrix
open Matrix

namespace BfgsVerification.CompressionDeterminant

theorem inverse_dot_symm {n : ℕ} (A : Mat n) (hA : A.IsSymm) (a b : Vec n) :
    dot b (A⁻¹.mulVec a) = dot a (A⁻¹.mulVec b) := by
  have hi : (A⁻¹).IsSymm := by
    change (A⁻¹)ᵀ = A⁻¹
    rw [Matrix.transpose_nonsing_inv, hA.eq]
  change b ⬝ᵥ (A⁻¹ *ᵥ a) = a ⬝ᵥ (A⁻¹ *ᵥ b)
  rw [dotProduct_mulVec, ← mulVec_transpose, hi.eq, dotProduct_comm]

/-- The determinant lemma reduced to a genuine two-by-two determinant. -/
theorem det_rank_two {n : ℕ} (A : Mat n) (a b : Vec n) (t v : ℝ)
    (hA : IsUnit A.det) (hsym : A.IsSymm) :
    (A + t • outer a a + v • (outer a b + outer b a)).det =
      A.det * ((1 + v * dot a (A⁻¹.mulVec b)) ^ 2 +
        dot a (A⁻¹.mulVec a) * (t - v ^ 2 * dot b (A⁻¹.mulVec b))) := by
  let U : Matrix (Fin n) (Fin 2) ℝ := fun i => ![a i, b i]
  let V : Matrix (Fin 2) (Fin n) ℝ := ![fun j => t * a j + v * b j, fun j => v * a j]
  have hUV : U * V = t • outer a a + v • (outer a b + outer b a) := by
    ext i j
    simp [U, V, Matrix.mul_apply, Fin.sum_univ_two, outer]
    ring
  have hAU : A⁻¹ * U = fun i => ![(A⁻¹.mulVec a) i, (A⁻¹.mulVec b) i] := by
    ext i j
    fin_cases j <;> simp [U, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hab := inverse_dot_symm A hsym a b
  have hsmall : (1 : Matrix (Fin 2) (Fin 2) ℝ) + V * A⁻¹ * U =
      !![1 + t * dot a (A⁻¹.mulVec a) + v * dot b (A⁻¹.mulVec a),
          t * dot a (A⁻¹.mulVec b) + v * dot b (A⁻¹.mulVec b);
        v * dot a (A⁻¹.mulVec a), 1 + v * dot a (A⁻¹.mulVec b)] := by
    rw [Matrix.mul_assoc, hAU]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V, Matrix.mul_apply, dot, add_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, mul_assoc]
    ring
  rw [add_assoc, ← hUV, Matrix.det_add_mul U V hA, hsmall, Matrix.det_fin_two, hab]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The compressed projected matrix occurring in the full inverse-BFGS update. -/
def compression {n : ℕ} (A : Mat n) (a b : Vec n) (κ r : ℝ) : Mat n :=
  A - κ⁻¹ • (outer a b + outer b a) + (r / κ ^ 2) • outer a a

theorem compression_eq_rank_two {n : ℕ} (A : Mat n) (a b : Vec n) (κ r : ℝ) :
    compression A a b κ r =
      A + (r / κ ^ 2) • outer a a + (-κ⁻¹) • (outer a b + outer b a) := by
  simp only [compression, sub_eq_add_neg, neg_smul]
  abel

/-- The source's rank-two determinant identity, cross-multiplied to avoid any
    hidden division by the determinant of the possibly singular compression. -/
theorem compression_det {n : ℕ} (A : Mat n) (a b : Vec n) (κ r : ℝ)
    (hA : IsUnit A.det) (hsym : A.IsSymm) (hκ : κ ≠ 0) :
    κ ^ 2 * (compression A a b κ r).det =
      A.det * ((κ - dot a (A⁻¹.mulVec b)) ^ 2 +
        dot a (A⁻¹.mulVec a) * (r - dot b (A⁻¹.mulVec b))) := by
  rw [compression_eq_rank_two, det_rank_two A a b (r / κ ^ 2) (-κ⁻¹) hA hsym]
  field_simp [hκ]
  ring_nf
  simp

/-- The determinant increment is exact even if the initial rank-two
    perturbation is singular. Only the original base matrix must be invertible. -/
theorem rank_two_add_rank_one_det {n : ℕ} (A : Mat n) (a b : Vec n) (t v ρ : ℝ)
    (hA : IsUnit A.det) (hsym : A.IsSymm) :
    (A + t • outer a a + v • (outer a b + outer b a) + ρ • outer a a).det =
      (A + t • outer a a + v • (outer a b + outer b a)).det +
        ρ * A.det * dot a (A⁻¹.mulVec a) := by
  have hid : A + t • outer a a + v • (outer a b + outer b a) + ρ • outer a a =
      A + (t + ρ) • outer a a + v • (outer a b + outer b a) := by
    rw [add_smul]
    abel
  rw [hid, det_rank_two A a b (t + ρ) v hA hsym, det_rank_two A a b t v hA hsym]
  ring

/-- Specialization of the exact increment to the projected compression. -/
theorem compression_add_rank_one_det {n : ℕ} (A : Mat n) (a b : Vec n) (κ r ρ : ℝ)
    (hA : IsUnit A.det) (hsym : A.IsSymm) :
    (compression A a b κ r + ρ • outer a a).det =
      (compression A a b κ r).det + ρ * A.det * dot a (A⁻¹.mulVec a) := by
  rw [compression_eq_rank_two]
  exact rank_two_add_rank_one_det A a b (r / κ ^ 2) (-κ⁻¹) ρ hA hsym

end BfgsVerification.CompressionDeterminant
