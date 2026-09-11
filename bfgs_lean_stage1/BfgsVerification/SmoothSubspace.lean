import BfgsVerification.ObjectiveEnergy

/-! Actual smooth-subspace trace budgets and residual Hessian energy bounds.
A fixed subspace is represented by orthonormal columns, with its actual
orthogonal projection `U * Uᵀ`. No Hessian growth bound is assumed. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace BfgsVerification
namespace SmoothSubspace

/-- The squared Frobenius norm, as the actual sum of squared matrix entries. -/
def frobSq {n r : ℕ} (W : Matrix (Fin n) (Fin r) ℝ) : ℝ :=
  ∑ i, ∑ j, (W i j) ^ 2

theorem frobSq_nonneg {n r : ℕ} (W : Matrix (Fin n) (Fin r) ℝ) : 0 ≤ frobSq W :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem trace_outer {n : ℕ} (g : Vec n) : (outer g g).trace = sqNorm g := by
  simp only [Matrix.trace, Matrix.diag, outer, sqNorm, pow_two]

/-- Gram trace is the sum of the actual column energies. -/
theorem gram_trace {n r : ℕ} (B : Mat n) (W : Matrix (Fin n) (Fin r) ℝ) :
    (metricGram B W).trace = ∑ j, metricEnergy B (fun i => W i j) := by
  simp only [Matrix.trace, Matrix.diag, EnergyIdentities.gram_entry, metricEnergy]

theorem gram_trace_nonneg {n r : ℕ} {B : Mat n} (hB : B.PosSemidef)
    (W : Matrix (Fin n) (Fin r) ℝ) : 0 ≤ (metricGram B W).trace := by
  rw [gram_trace]
  apply Finset.sum_nonneg
  intro j _
  simpa only [metricEnergy, dot, dotProduct, star_trivial] using hB.2 (fun i => W i j)

/-- The trace of a rank-two Hessian update on any fixed frame is exact. -/
theorem gram_trace_update {n r : ℕ} (B : Mat n) (g y : Vec n) (q t : ℝ)
    (U : Matrix (Fin n) (Fin r) ℝ) :
    (metricGram (B - q⁻¹ • outer g g + t⁻¹ • outer y y) U).trace =
      (metricGram B U).trace - sqNorm (Uᵀ.mulVec g) / q +
        sqNorm (Uᵀ.mulVec y) / t := by
  rw [EnergyIdentities.gram_add, EnergyIdentities.gram_sub,
    EnergyIdentities.gram_smul, EnergyIdentities.gram_smul,
    EnergyIdentities.gram_outer, EnergyIdentities.gram_outer,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    trace_outer, trace_outer]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

/-- Frobenius square is equally the sum of squared column norms. -/
theorem frobSq_eq_sum_columns {n r : ℕ} (W : Matrix (Fin n) (Fin r) ℝ) :
    frobSq W = ∑ j, sqNorm (fun i => W i j) := by
  unfold frobSq sqNorm
  exact Finset.sum_comm

/-- Rectangular congruence has the expected exact quadratic form. -/
theorem gram_energy {n r : ℕ} (B : Mat n) (U : Matrix (Fin n) (Fin r) ℝ) (v : Vec r) :
    metricEnergy (metricGram B U) v = metricEnergy B (U.mulVec v) := by
  change v ⬝ᵥ (Uᵀ * B * U) *ᵥ v = (U *ᵥ v) ⬝ᵥ B *ᵥ (U *ᵥ v)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose]

/-- Orthonormal columns preserve the actual Euclidean norm of coordinates. -/
theorem sqNorm_mulVec_orthonormal {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ * U = 1) (v : Vec r) : sqNorm (U.mulVec v) = sqNorm v := by
  have he := gram_energy (1 : Mat n) U v
  simp only [metricGram, Matrix.mul_one, hU, metricEnergy, Matrix.one_mulVec] at he
  simpa only [sqNorm, dot, pow_two] using he.symm

/-- Coordinate norm is exactly the norm of the actual orthogonal projection. -/
theorem sqNorm_projection {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ * U = 1) (v : Vec n) :
    sqNorm ((U * Uᵀ).mulVec v) = sqNorm (Uᵀ.mulVec v) := by
  rw [← Matrix.mulVec_mulVec]
  exact sqNorm_mulVec_orthonormal U hU _

/-- Orthonormal embedding also preserves the Frobenius norm of a rectangular frame. -/
theorem frobSq_mul_orthonormal {n r p : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ * U = 1) (A : Matrix (Fin r) (Fin p) ℝ) : frobSq (U * A) = frobSq A := by
  rw [frobSq_eq_sum_columns, frobSq_eq_sum_columns]
  apply Finset.sum_congr rfl
  intro j _
  exact sqNorm_mulVec_orthonormal U hU (fun i => A i j)

/-- The compressed Hessian trace equals trace against the actual orthogonal projection. -/
theorem gram_trace_eq_projection_trace {n r : ℕ} (B : Mat n)
    (U : Matrix (Fin n) (Fin r) ℝ) :
    (metricGram B U).trace = ((U * Uᵀ) * B).trace := by
  exact Matrix.trace_mul_cycle Uᵀ B U

/-- Every frame's energy is bounded by its actual Frobenius square times the metric trace. -/
theorem gram_trace_le_frobSq_mul_trace {n r : ℕ} {B : Mat n} (hB : B.PosSemidef)
    (W : Matrix (Fin n) (Fin r) ℝ) :
    (metricGram B W).trace ≤ frobSq W * B.trace := by
  rw [gram_trace, frobSq_eq_sum_columns, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  exact metricEnergy_le_sqNorm_mul_trace B (fun i => W i j) hB

/-- The rank-one matrix removed from a Hessian is actually positive semidefinite. -/
theorem scaled_outer_posSemidef {n : ℕ} (g : Vec n) (a : ℝ) (ha : 0 ≤ a) :
    (a • outer g g).PosSemidef := by
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, outer, star_trivial]
    ring
  · intro x
    have henergy : 0 ≤ metricEnergy (a • outer g g) x := by
      rw [EnergyIdentities.energy_smul_matrix, EnergyIdentities.energy_outer]
      exact mul_nonneg ha (sq_nonneg _)
    simpa only [metricEnergy, dot, dotProduct, star_trivial] using henergy

/-- Removing a nonnegative gradient rank-one matrix can only decrease frame energy. -/
theorem gram_trace_annihilated_le {n r : ℕ} (B : Mat n) (g : Vec n)
    (q : ℝ) (hq : 0 ≤ q) (W : Matrix (Fin n) (Fin r) ℝ) :
    (metricGram (B - q⁻¹ • outer g g) W).trace ≤ (metricGram B W).trace := by
  rw [EnergyIdentities.gram_sub, EnergyIdentities.gram_smul, EnergyIdentities.gram_outer,
    Matrix.trace_sub, Matrix.trace_smul, trace_outer]
  simp only [smul_eq_mul]
  exact sub_le_self _ (mul_nonneg (inv_nonneg.mpr hq) (sqNorm_nonneg _))

/-- Residual columns fixed by the actual projection lie in the controlled subspace.
Their annihilated Hessian energy is bounded using only that subspace's trace. -/
theorem residual_energy_le {n r p : ℕ} {B : Mat n} (hB : B.PosSemidef)
    (g : Vec n) (q : ℝ) (hq : 0 ≤ q)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (W : Matrix (Fin n) (Fin p) ℝ) (hW : (U * Uᵀ) * W = W) :
    (metricGram (B - q⁻¹ • outer g g) W).trace ≤
      frobSq W * (metricGram B U).trace := by
  apply (gram_trace_annihilated_le B g q hq W).trans
  let A := Uᵀ * W
  have hWA : W = U * A := by
    dsimp only [A]
    rw [← Matrix.mul_assoc, hW]
  have hgram : metricGram B (U * A) = metricGram (metricGram B U) A := by
    simp only [metricGram, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hWA, hgram, frobSq_mul_orthonormal U hU]
  exact gram_trace_le_frobSq_mul_trace (metricGram_posSemidef hB U) A

/-- The matrix used above is symmetric and idempotent, hence the actual orthogonal projection. -/
theorem projection_isSymm {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) :
    (U * Uᵀ).IsSymm := by
  simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem projection_idempotent {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ * U = 1) : (U * Uᵀ) * (U * Uᵀ) = U * Uᵀ := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]

/-- Fixing a vector by the projection is exactly membership in the column subspace. -/
theorem projection_fixed_iff {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ * U = 1) (v : Vec n) :
    (U * Uᵀ).mulVec v = v ↔ ∃ a : Vec r, U.mulVec a = v := by
  constructor
  · intro hv
    exact ⟨Uᵀ.mulVec v, by rw [Matrix.mulVec_mulVec, hv]⟩
  · rintro ⟨a, rfl⟩
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hU, Matrix.mul_one]

/-- The matrix residual condition is exactly that each column belongs to the fixed subspace. -/
theorem projection_columns_iff {n r p : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ * U = 1) (W : Matrix (Fin n) (Fin p) ℝ) :
    (U * Uᵀ) * W = W ↔ ∀ j, ∃ a : Vec r, U.mulVec a = (fun i => W i j) := by
  constructor
  · intro hW j
    apply (projection_fixed_iff U hU _).mp
    exact congrArg (fun A : Matrix (Fin n) (Fin p) ℝ => fun i => A i j) hW
  · intro hW
    ext i j
    exact congrFun ((projection_fixed_iff U hU _).mpr (hW j)) i

end SmoothSubspace

namespace AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- The fixed-subspace trace recurrence for the actual Hessian sequence. -/
theorem smooth_subspace_trace_update {r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (k : ℕ) :
    (metricGram (R.hessian (k + 1)) U).trace =
      (metricGram (R.hessian k) U).trace - sqNorm (Uᵀ.mulVec (R.g k)) / R.q k +
        sqNorm (Uᵀ.mulVec (R.gradientChange k)) / R.curvature k := by
  rw [R.hessian_update]
  exact SmoothSubspace.gram_trace_update _ _ _ _ _ _

/-- The source's smooth-direction hypothesis bounds each trace increment. -/
theorem smooth_subspace_trace_step {r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (L : ℝ) (hsmooth : ∀ k, sqNorm (Uᵀ.mulVec (R.gradientChange k)) ≤ L * R.curvature k)
    (k : ℕ) :
    (metricGram (R.hessian (k + 1)) U).trace ≤ (metricGram (R.hessian k) U).trace + L := by
  rw [R.smooth_subspace_trace_update]
  have hdecr := div_nonneg (sqNorm_nonneg (Uᵀ.mulVec (R.g k))) (R.q_pos k).le
  have hincr : sqNorm (Uᵀ.mulVec (R.gradientChange k)) / R.curvature k ≤ L :=
    (div_le_iff₀ (R.curvature_pos k)).mpr (hsmooth k)
  linarith

/-- Linear growth on fixed smooth directions is derived from the actual update. -/
theorem smooth_subspace_trace_bound {r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (L : ℝ) (hsmooth : ∀ k, sqNorm (Uᵀ.mulVec (R.gradientChange k)) ≤ L * R.curvature k)
    (k : ℕ) :
    (metricGram (R.hessian k) U).trace ≤ (metricGram (R.hessian 0) U).trace + L * (k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := R.smooth_subspace_trace_step U L hsmooth k
    push_cast
    nlinarith

/-- Both parts in the actual Hessian decomposition are PSD: the complementary
rank-one part here, and `annihilated_hessian_posSemidef` for the annihilated part. -/
theorem hessian_minus_annihilated_posSemidef (k : ℕ) :
    (R.hessian k - (R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k))).PosSemidef := by
  rw [sub_sub_cancel]
  exact SmoothSubspace.scaled_outer_posSemidef (R.g k) (R.q k)⁻¹
    (inv_nonneg.mpr (R.q_pos k).le)

/-- Actual residual energy is controlled by the derived smooth-subspace trace. -/
theorem smooth_subspace_residual_energy_le {r p : ℕ}
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (W : Matrix (Fin n) (Fin p) ℝ) (hW : (U * Uᵀ) * W = W) (k : ℕ) :
    (metricGram (R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) W).trace ≤
      SmoothSubspace.frobSq W * (metricGram (R.hessian k) U).trace :=
  SmoothSubspace.residual_energy_le (R.hessian_posDef k).posSemidef
    (R.g k) (R.q k) (R.q_pos k).le U hU W hW

/-- The full residual bound is derived from the smooth-direction hypothesis and
actual Frobenius control; no bound on the full Hessian is needed. -/
theorem smooth_subspace_residual_budget {r p : ℕ}
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (L : ℝ) (hsmooth : ∀ k, sqNorm (Uᵀ.mulVec (R.gradientChange k)) ≤ L * R.curvature k)
    (C : ℝ) (k : ℕ) (W : Matrix (Fin n) (Fin p) ℝ)
    (hW : (U * Uᵀ) * W = W) (hsize : SmoothSubspace.frobSq W ≤ C * R.d k) :
    (metricGram (R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) W).trace ≤
      C * R.d k * ((metricGram (R.hessian 0) U).trace + L * (k : ℝ)) := by
  apply (R.smooth_subspace_residual_energy_le U hU W hW k).trans
  have htrace := SmoothSubspace.gram_trace_nonneg (R.hessian_posDef k).posSemidef U
  calc
    SmoothSubspace.frobSq W * (metricGram (R.hessian k) U).trace ≤
      (C * R.d k) * (metricGram (R.hessian k) U).trace :=
        mul_le_mul_of_nonneg_right hsize htrace
    _ ≤ C * R.d k * ((metricGram (R.hessian 0) U).trace + L * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left (R.smooth_subspace_trace_bound U L hsmooth k)
        ((SmoothSubspace.frobSq_nonneg W).trans hsize)

/-- The trace identity stated directly using the actual orthogonal projection. -/
theorem smooth_subspace_projection_trace_update {r : ℕ}
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1) (k : ℕ) :
    ((U * Uᵀ) * R.hessian (k + 1)).trace =
      ((U * Uᵀ) * R.hessian k).trace - sqNorm ((U * Uᵀ).mulVec (R.g k)) / R.q k +
        sqNorm ((U * Uᵀ).mulVec (R.gradientChange k)) / R.curvature k := by
  rw [← SmoothSubspace.gram_trace_eq_projection_trace,
    ← SmoothSubspace.gram_trace_eq_projection_trace,
    SmoothSubspace.sqNorm_projection U hU, SmoothSubspace.sqNorm_projection U hU]
  exact R.smooth_subspace_trace_update U k

/-- Source M:residual's linear trace budget for the actual orthogonal projection. -/
theorem smooth_subspace_projection_trace_bound {r : ℕ}
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (L : ℝ) (hsmooth : ∀ k, sqNorm ((U * Uᵀ).mulVec (R.gradientChange k)) ≤ L * R.curvature k)
    (k : ℕ) :
    ((U * Uᵀ) * R.hessian k).trace ≤ ((U * Uᵀ) * R.hessian 0).trace + L * (k : ℝ) := by
  simp only [SmoothSubspace.sqNorm_projection U hU] at hsmooth
  rw [← SmoothSubspace.gram_trace_eq_projection_trace,
    ← SmoothSubspace.gram_trace_eq_projection_trace]
  exact R.smooth_subspace_trace_bound U L hsmooth k

end AdmissibleBFGSRun
end BfgsVerification
