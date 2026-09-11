import BfgsVerification.EnergyIdentities
import BfgsVerification.Normalization

/-! Matrix trace bounds for the imperfect-frame argument. Operator bounds are
stated as their exact quadratic action on every vector, with no norm convention
or full-rank frame assumption hidden in the notation. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace BfgsVerification.FrameBounds

/-- Squared Euclidean operator bound for right multiplication of frame rows. -/
def OperatorSqBound {r : ℕ} (T : Mat r) (a : ℝ) : Prop :=
  ∀ v : Vec r, sqNorm (Tᵀ.mulVec v) ≤ a * sqNorm v

theorem trace_outer {r : ℕ} (v : Vec r) : (outer v v).trace = sqNorm v := by
  simp only [Matrix.trace, Matrix.diag, outer, sqNorm, pow_two]

theorem gram_trace_nonneg {n r : ℕ} {B : Mat n} (hB : B.PosSemidef)
    (V : Matrix (Fin n) (Fin r) ℝ) : 0 ≤ (metricGram B V).trace := by
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_nonneg
  intro j _
  rw [EnergyIdentities.gram_entry]
  simpa only [dot, dotProduct, star_trivial] using hB.2 (fun i => V i j)

theorem gram_trace_square {n r : ℕ} (C : Mat n) (V : Matrix (Fin n) (Fin r) ℝ) :
    (metricGram (Cᵀ * C) V).trace = ∑ i, sqNorm (fun j => (C * V) i j) := by
  have he : metricGram (Cᵀ * C) V = (C * V)ᵀ * (C * V) := by
    simp only [metricGram, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [he]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    sqNorm, pow_two]
  exact Finset.sum_comm

/-- An actual squared operator bound controls the PSD frame energy. -/
theorem gram_trace_transport_le {n r : ℕ} {M : Mat n} (hM : M.PosSemidef)
    (V : Matrix (Fin n) (Fin r) ℝ) (T : Mat r) (a : ℝ)
    (hT : OperatorSqBound T a) :
    (metricGram M (V * T)).trace ≤ a * (metricGram M V).trace := by
  obtain ⟨C, hC⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hM
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hC
  rw [hC, gram_trace_square, gram_trace_square, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hv : (fun j => (C * (V * T)) i j) = Tᵀ.mulVec (fun j => (C * V) i j) := by
    ext j
    rw [← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hv]
  exact hT _

theorem scalar_young (x y d : ℝ) (hd : 0 < d) :
    (x + y) ^ 2 ≤ (1 + d) * x ^ 2 + (1 + d⁻¹) * y ^ 2 := by
  apply (mul_le_mul_left hd).mp
  have hcancel : d * d⁻¹ = 1 := mul_inv_cancel₀ hd.ne'
  nlinarith [sq_nonneg (d * x - y)]

/-- Young's bound in an actual PSD matrix metric, including singular metrics. -/
theorem gram_trace_add_le {n r : ℕ} {M : Mat n} (hM : M.PosSemidef)
    (V W : Matrix (Fin n) (Fin r) ℝ) (d : ℝ) (hd : 0 < d) :
    (metricGram M (V + W)).trace ≤
      (1 + d) * (metricGram M V).trace + (1 + d⁻¹) * (metricGram M W).trace := by
  obtain ⟨C, hC⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hM
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hC
  rw [hC, gram_trace_square, gram_trace_square, gram_trace_square]
  simp only [Matrix.mul_add, sqNorm, Matrix.add_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact scalar_young _ _ d hd

end BfgsVerification.FrameBounds
