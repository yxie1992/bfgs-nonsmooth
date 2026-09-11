import BfgsVerification.AffineProjection

/-! Actual inverse-BFGS compression under an exact linear gradient image. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace AffineProjection
open EnergyIdentities

theorem mul_rectOuter {n r p : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (a : Vec n) (b : Vec p) : A * rectOuter a b = rectOuter (A.mulVec a) b := by
  ext i j
  simp only [Matrix.mul_apply, rectOuter, Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem rectOuter_mul {n r p : ℕ} (a : Vec n) (b : Vec r)
    (A : Matrix (Fin r) (Fin p) ℝ) : rectOuter a b * A = rectOuter a (Aᵀ.mulVec b) := by
  ext i j
  simp only [Matrix.mul_apply, rectOuter, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem rectOuter_zero_left {n r : ℕ} (b : Vec r) : rectOuter (0 : Vec n) b = 0 := by
  ext i j
  simp [rectOuter]

theorem projection_factor {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (s : Vec n) (y : Vec r) (ρ : ℝ) :
    A * (1 - ρ • outer s (Aᵀ.mulVec y)) = (1 - ρ • outer (A.mulVec s) y) * A := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  change A - ρ • (A * rectOuter s (Aᵀ.mulVec y)) =
    A - ρ • (rectOuter (A.mulVec s) y * A)
  rw [mul_rectOuter, rectOuter_mul]

/-- Exact compression of the full inverse update. No denominators or matrices
are abstracted away, and this identity itself requires no positivity premise. -/
theorem inverseBFGS_compress {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (H : Mat n) (s : Vec n) (y : Vec r) :
    compress A (inverseBFGS H s (Aᵀ.mulVec y)) =
      inverseBFGS (compress A H) (A.mulVec s) y := by
  have hr := congrArg Matrix.transpose (projection_factor A s y (dot y (A.mulVec s))⁻¹)
  simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_smul, BFGSCompression.transpose_outer, Matrix.transpose_transpose] at hr
  unfold inverseBFGS compress
  rw [dot_transpose_mulVec]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hrank : A * outer s s * Aᵀ = outer (A.mulVec s) (A.mulVec s) := by
    change A * rectOuter s s * Aᵀ = _
    rw [mul_rectOuter, rectOuter_mul, Matrix.transpose_transpose]
    rfl
  rw [hrank]
  congr 1
  simp only [← Matrix.mul_assoc]
  rw [projection_factor]
  simp only [Matrix.mul_assoc]
  rw [hr]

theorem project_step {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (H : Mat n) (g : Vec r) (α : ℝ) :
    A.mulVec (bfgsStep H (Aᵀ.mulVec g) α) = bfgsStep (compress A H) g α := by
  simp only [bfgsStep, Matrix.mulVec_smul, compress, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem project_energy {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (H : Mat n) (g : Vec r) :
    metricEnergy H (Aᵀ.mulVec g) = metricEnergy (compress A H) g := by
  simp only [metricEnergy, dot_transpose_mulVec, compress, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- A fixed annihilator continues to annihilate the gradient-image block. -/
theorem inverseBFGS_annihilator {n r p : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (D : Matrix (Fin p) (Fin n) ℝ) (H : Mat n) (s : Vec n) (y : Vec r)
    (hDH : D * H * Aᵀ = 0) (hDs : D.mulVec s = 0) :
    D * inverseBFGS H s (Aᵀ.mulVec y) * Aᵀ = 0 := by
  have hDP (ρ : ℝ) : D * (1 - ρ • outer s (Aᵀ.mulVec y)) = D := by
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
    change D - ρ • (D * rectOuter s (Aᵀ.mulVec y)) = D
    rw [mul_rectOuter, hDs, rectOuter_zero_left, smul_zero, sub_zero]
  have hDHy : (D * H).mulVec (Aᵀ.mulVec y) = 0 := by
    rw [Matrix.mulVec_mulVec, hDH, Matrix.zero_mulVec]
  unfold inverseBFGS
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  simp only [← Matrix.mul_assoc]
  rw [hDP]
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  change ((D * H) - (dot (Aᵀ.mulVec y) s)⁻¹ •
      ((D * H) * rectOuter (Aᵀ.mulVec y) s)) * Aᵀ +
      (dot (Aᵀ.mulVec y) s)⁻¹ • ((D * rectOuter s s) * Aᵀ) = 0
  rw [mul_rectOuter, hDHy, rectOuter_zero_left, smul_zero, sub_zero,
    mul_rectOuter, hDs, rectOuter_zero_left, Matrix.zero_mul, smul_zero, add_zero, hDH]

end AffineProjection
end BfgsVerification
