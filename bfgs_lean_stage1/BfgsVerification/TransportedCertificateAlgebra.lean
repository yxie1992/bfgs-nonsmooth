import BfgsVerification.TransportedCertificateDefinitions
import BfgsVerification.SmoothSubspace

/-! Actual PSD trace and step-projector algebra for Module T. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace BfgsVerification.TransportedCertificate

/-- Trace of a product of actual PSD matrices is nonnegative. -/
theorem trace_mul_nonneg {n : ℕ} {B W : Mat n}
    (hB : B.PosSemidef) (hW : W.PosSemidef) : 0 ≤ (B * W).trace := by
  obtain ⟨C, hC⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hW
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hC
  rw [hC, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simpa only [metricGram, Matrix.transpose_transpose] using
    SmoothSubspace.gram_trace_nonneg hB Cᵀ

/-- Loewner order is tested against an actual PSD matrix by trace. -/
theorem trace_mul_mono {n : ℕ} {M A B : Mat n}
    (hM : M.PosSemidef) (hAB : (B - A).PosSemidef) :
    (M * A).trace ≤ (M * B).trace := by
  have h := trace_mul_nonneg hM hAB
  rw [Matrix.mul_sub, Matrix.trace_sub] at h
  linarith

theorem trace_outer_mul {n : ℕ} (g : Vec n) (W : Mat n) :
    (outer g g * W).trace = metricEnergy W g := by
  rw [Matrix.trace_mul_comm, BFGSCompression.mul_outer]
  change (∑ i, (W.mulVec g) i * g i) = ∑ i, g i * (W.mulVec g) i
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem stepProjector_isSymm {n : ℕ} (s : Vec n) : (stepProjector s).IsSymm := by
  simp only [stepProjector, Matrix.IsSymm, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_smul, outer_transpose]

/-- An annihilated matrix is unchanged by the step projector on the right. -/
theorem mul_stepProjector {n : ℕ} (M : Mat n) (s : Vec n) (hs : M.mulVec s = 0) :
    M * stepProjector s = M := by
  rw [stepProjector, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul,
    BFGSCompression.mul_outer, hs]
  have hz : outer (0 : Vec n) s = 0 := by ext i j; simp [outer]
  rw [hz, smul_zero, sub_zero]

/-- Symmetry gives the corresponding left projector identity. -/
theorem stepProjector_mul {n : ℕ} (M : Mat n) (hM : M.IsSymm)
    (s : Vec n) (hs : M.mulVec s = 0) : stepProjector s * M = M := by
  have h := congrArg Matrix.transpose (mul_stepProjector M s hs)
  simpa only [Matrix.transpose_mul, (stepProjector_isSymm s).eq, hM.eq] using h

theorem annihilated_projector {n : ℕ} (M : Mat n) (hM : M.IsSymm)
    (s : Vec n) (hs : M.mulVec s = 0) : stepProjector s * M * stepProjector s = M := by
  rw [stepProjector_mul M hM s hs, mul_stepProjector M s hs]

/-- The step direction contributes no energy when tested against an annihilated matrix. -/
theorem trace_projected {n : ℕ} (M : Mat n) (hM : M.IsSymm)
    (s : Vec n) (hs : M.mulVec s = 0) (W : Mat n) :
    (M * (stepProjector s * W * stepProjector s)).trace = (M * W).trace := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_stepProjector M s hs,
    Matrix.trace_mul_cycle, stepProjector_mul M hM s hs]

/-- The objective certificate's projected Loewner bound controls actual annihilated energy. -/
theorem projected_transport_trace {n : ℕ} (M : Mat n) (hM : M.PosSemidef)
    (s : Vec n) (hs : M.mulVec s = 0) (W Z : Mat n) (a : ℝ)
    (hT : (a • (stepProjector s * W * stepProjector s) -
      stepProjector s * Z * stepProjector s).PosSemidef) :
    (M * Z).trace ≤ a * (M * W).trace := by
  have hsym : M.IsSymm := by
    simpa only [Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using hM.isHermitian
  have h := trace_mul_mono hM hT
  rw [Matrix.mul_smul, Matrix.trace_smul, trace_projected M hsym s hs,
    trace_projected M hsym s hs] at h
  exact h

/-- Trace of the genuine rank-two Hessian update against an arbitrary finite field value. -/
theorem hessian_trace_update {n : ℕ} (B W : Mat n) (g y : Vec n) (q t : ℝ) :
    ((B - q⁻¹ • outer g g + t⁻¹ • outer y y) * W).trace =
      (B * W).trace - metricEnergy W g / q + metricEnergy W y / t := by
  rw [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    trace_outer_mul, trace_outer_mul]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

end BfgsVerification.TransportedCertificate
