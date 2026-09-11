import BfgsVerification.PositiveUpdate
import BfgsVerification.GramSchur

/-! Exact quadratic and frame identities used with the actual Hessian update.
The algebraic hypotheses in this file are discharged for BFGS in ObjectiveEnergy. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace BfgsVerification.EnergyIdentities

theorem energy_add_matrix {n : ℕ} (B C : Mat n) (x : Vec n) :
    metricEnergy (B + C) x = metricEnergy B x + metricEnergy C x := by
  change x ⬝ᵥ (B + C) *ᵥ x = x ⬝ᵥ B *ᵥ x + x ⬝ᵥ C *ᵥ x
  rw [Matrix.add_mulVec, dotProduct_add]

theorem energy_sub_matrix {n : ℕ} (B C : Mat n) (x : Vec n) :
    metricEnergy (B - C) x = metricEnergy B x - metricEnergy C x := by
  change x ⬝ᵥ (B - C) *ᵥ x = x ⬝ᵥ B *ᵥ x - x ⬝ᵥ C *ᵥ x
  rw [Matrix.sub_mulVec, dotProduct_sub]

theorem energy_smul_matrix {n : ℕ} (a : ℝ) (B : Mat n) (x : Vec n) :
    metricEnergy (a • B) x = a * metricEnergy B x := by
  unfold metricEnergy
  rw [Matrix.smul_mulVec_assoc, dot_smul_right]

theorem energy_outer {n : ℕ} (g x : Vec n) :
    metricEnergy (outer g g) x = (dot g x) ^ 2 := by
  unfold metricEnergy
  rw [outer_mulVec, dot_smul_right]
  have hc : dot x g = dot g x := dotProduct_comm x g
  rw [hc, pow_two]

theorem energy_add_kernel {n : ℕ} {M : Mat n} (hM : M.IsSymm)
    {s : Vec n} (hs : M.mulVec s = 0) (r : Vec n) :
    metricEnergy M (r + s) = metricEnergy M r := by
  have hcross : dot s (M.mulVec r) = 0 := by
    change s ⬝ᵥ (M *ᵥ r) = 0
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq, hs, zero_dotProduct]
  change (r + s) ⬝ᵥ M *ᵥ (r + s) = r ⬝ᵥ M *ᵥ r
  rw [Matrix.mulVec_add, hs, add_zero, add_dotProduct]
  change metricEnergy M r + dot s (M.mulVec r) = metricEnergy M r
  rw [hcross, add_zero]

/-- Fixed-reference cancellation from an annihilated step and exact rank-one update. -/
theorem fixed_reference {n : ℕ} (B : Mat n) (g y s r : Vec n) (q t : ℝ)
    (hM : (B - q⁻¹ • outer g g).IsSymm)
    (hs : (B - q⁻¹ • outer g g).mulVec s = 0) :
    metricEnergy (B - q⁻¹ • outer g g + t⁻¹ • outer y y) (r + s) =
      metricEnergy B r - (dot g r) ^ 2 / q + (dot y (r + s)) ^ 2 / t := by
  rw [energy_add_matrix, energy_add_kernel hM hs, energy_sub_matrix,
    energy_smul_matrix, energy_smul_matrix, energy_outer, energy_outer]
  simp only [div_eq_mul_inv]
  ring

/-- Actual rectangular Gram entries, with no independence hypothesis. -/
theorem gram_entry {n r : ℕ} (B : Mat n) (V : Matrix (Fin n) (Fin r) ℝ)
    (i j : Fin r) :
    metricGram B V i j = dot (fun k => V k i) (B.mulVec (fun k => V k j)) := by
  change (Vᵀ * B * V) i j = _
  rw [Matrix.mul_assoc]
  rfl

theorem gram_add {n r : ℕ} (B C : Mat n) (V : Matrix (Fin n) (Fin r) ℝ) :
    metricGram (B + C) V = metricGram B V + metricGram C V := by
  simp only [metricGram, Matrix.mul_add, Matrix.add_mul]

theorem gram_sub {n r : ℕ} (B C : Mat n) (V : Matrix (Fin n) (Fin r) ℝ) :
    metricGram (B - C) V = metricGram B V - metricGram C V := by
  simp only [metricGram, Matrix.mul_sub, Matrix.sub_mul]

theorem gram_smul {n r : ℕ} (a : ℝ) (B : Mat n)
    (V : Matrix (Fin n) (Fin r) ℝ) :
    metricGram (a • B) V = a • metricGram B V := by
  simp only [metricGram, Matrix.mul_smul, Matrix.smul_mul]

theorem gram_outer {n r : ℕ} (g : Vec n) (V : Matrix (Fin n) (Fin r) ℝ) :
    metricGram (outer g g) V = outer (Vᵀ.mulVec g) (Vᵀ.mulVec g) := by
  ext i j
  rw [gram_entry, outer_mulVec, dot_smul_right]
  change dot g (fun k => V k j) * dot (fun k => V k i) g =
    dot (fun k => V k i) g * dot (fun k => V k j) g
  rw [show dot g (fun k => V k j) = dot (fun k => V k j) g from dotProduct_comm _ _]
  ring

/-- Transport by a possibly singular matrix; no full-rank frame is required. -/
theorem gram_transport {n r : ℕ} (B : Mat n)
    (V : Matrix (Fin n) (Fin r) ℝ) (T : Mat r) :
    metricGram B (V * T) = Tᵀ * metricGram B V * T := by
  simp only [metricGram, Matrix.transpose_mul, Matrix.mul_assoc]

def rectOuter {n r : ℕ} (s : Vec n) (b : Vec r) : Matrix (Fin n) (Fin r) ℝ :=
  fun i j => s i * b j

theorem gram_add_kernel {n r : ℕ} {M : Mat n} (hM : M.IsSymm)
    {s : Vec n} (hs : M.mulVec s = 0)
    (V : Matrix (Fin n) (Fin r) ℝ) (b : Vec r) :
    metricGram M (V + rectOuter s b) = metricGram M V := by
  ext i j
  rw [gram_entry, gram_entry]
  have hcol (j : Fin r) : (fun k => (V + rectOuter s b) k j) =
      (fun k => V k j) + b j • s := by ext k; simp [rectOuter]; ring
  rw [hcol i, hcol j]
  have hz : M.mulVec (b j • s) = 0 := by rw [Matrix.mulVec_smul, hs, smul_zero]
  have hcross : dot s (M.mulVec (fun k => V k j)) = 0 := by
    change s ⬝ᵥ (M *ᵥ (fun k => V k j)) = 0
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq, hs, zero_dotProduct]
  change ((fun k => V k i) + b i • s) ⬝ᵥ
    M *ᵥ ((fun k => V k j) + b j • s) = _
  rw [Matrix.mulVec_add, hz, add_zero, add_dotProduct, smul_dotProduct]
  change dot (fun k => V k i) (M.mulVec (fun k => V k j)) +
    b i * dot s (M.mulVec (fun k => V k j)) = _
  rw [hcross, mul_zero, add_zero]

/-- Module M's moving-frame identity before instantiation with B=H⁻¹. -/
theorem moving_frame {n r : ℕ} (B : Mat n) (g y s : Vec n) (q t : ℝ)
    (hM : (B - q⁻¹ • outer g g).IsSymm)
    (hs : (B - q⁻¹ • outer g g).mulVec s = 0)
    (V W : Matrix (Fin n) (Fin r) ℝ) (T : Mat r) (b : Vec r)
    (hW : W = V * T + rectOuter s b) :
    metricGram (B - q⁻¹ • outer g g + t⁻¹ • outer y y) W =
      Tᵀ * (metricGram B V - q⁻¹ • outer (Vᵀ.mulVec g) (Vᵀ.mulVec g)) * T +
        t⁻¹ • outer (Wᵀ.mulVec y) (Wᵀ.mulVec y) := by
  rw [gram_add, gram_smul, gram_outer]
  congr 1
  rw [hW, gram_add_kernel hM hs, gram_transport, gram_sub, gram_smul, gram_outer]

end BfgsVerification.EnergyIdentities
