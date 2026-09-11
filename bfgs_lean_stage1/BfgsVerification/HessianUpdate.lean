import BfgsVerification.PositiveUpdate
import BfgsVerification.BFGSCompression

/-!
# The actual Hessian update and its annihilated positive semidefinite part

These identities are consequences of the ordinary full inverse-BFGS formula,
not extra assumptions on the Hessian matrices. All dimensions are finite but
arbitrary; no iterate or matrix limit is used.
-/

noncomputable section
open scoped BigOperators Matrix
open Matrix

namespace BfgsVerification

/-- Inverse Hessian action cancels the current metric. -/
theorem inverse_mul_mulVec {n : ℕ} {H : Mat n} (hH : H.PosDef) (g : Vec n) :
    H⁻¹.mulVec (H.mulVec g) = g := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul H hH.det_pos.ne'.isUnit,
    Matrix.one_mulVec]

/-- The inverse matrix sends the accepted step to minus its length times gradient. -/
theorem inverse_mul_step {n : ℕ} {H : Mat n} (hH : H.PosDef)
    (g : Vec n) (α : ℝ) : H⁻¹.mulVec (bfgsStep H g α) = -α • g := by
  rw [bfgsStep, Matrix.mulVec_smul, inverse_mul_mulVec hH]

/-- The Hessian with its gradient rank-one term removed is an actual congruence. -/
theorem annihilatedMatrix_projection {n : ℕ} {H : Mat n} (hH : H.PosDef)
    {g : Vec n} (hg : g ≠ 0) :
    H⁻¹ - (metricEnergy H g)⁻¹ • outer g g =
      (1 - (metricEnergy H g)⁻¹ • outer g (H.mulVec g)) * H⁻¹ *
        (1 - (metricEnergy H g)⁻¹ • outer g (H.mulVec g))ᵀ := by
  have hsym : H⁻¹.IsSymm := by
    simpa only [Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hH.inv.isHermitian
  rw [BFGSCompression.projection_expansion _ _ _ _ hsym,
    inverse_mul_mulVec hH]
  have hdot : dot (H.mulVec g) g = metricEnergy H g := dotProduct_comm _ _
  rw [hdot]
  have hq : metricEnergy H g ≠ 0 := (metricEnergy_pos hH hg).ne'
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The annihilated Hessian part is PSD by its exact congruence representation. -/
theorem annihilatedMatrix_posSemidef {n : ℕ} {H : Mat n} (hH : H.PosDef)
    {g : Vec n} (hg : g ≠ 0) :
    (H⁻¹ - (metricEnergy H g)⁻¹ • outer g g).PosSemidef := by
  rw [annihilatedMatrix_projection hH hg]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hH.inv.posSemidef.mul_mul_conjTranspose_same
      (1 - (metricEnergy H g)⁻¹ • outer g (H.mulVec g))

/-- The annihilated Hessian part kills the actual accepted search step. -/
theorem annihilatedMatrix_mul_step {n : ℕ} {H : Mat n} (hH : H.PosDef)
    {g : Vec n} (hg : g ≠ 0) (α : ℝ) :
    (H⁻¹ - (metricEnergy H g)⁻¹ • outer g g).mulVec (bfgsStep H g α) = 0 := by
  rw [Matrix.sub_mulVec, inverse_mul_step hH, Matrix.smul_mulVec_assoc,
    outer_mulVec, dot_bfgsStep, smul_smul]
  have hq : metricEnergy H g ≠ 0 := (metricEnergy_pos hH hg).ne'
  have hc : (metricEnergy H g)⁻¹ * -(α * metricEnergy H g) = -α := by
    field_simp
  rw [hc, sub_self]

/-- The actual inverse of the full inverse-BFGS update has the ordinary Hessian
rank-two formula. Positive curvature and initial SPD discharge its denominators. -/
theorem hessianUpdate {n : ℕ} {H : Mat n} (hH : H.PosDef)
    {g : Vec n} (hg : g ≠ 0) (y : Vec n) {α : ℝ} (hα : 0 < α)
    (ht : 0 < dot y (bfgsStep H g α)) :
    (inverseBFGS H (bfgsStep H g α) y)⁻¹ =
      H⁻¹ - (metricEnergy H g)⁻¹ • outer g g +
        (dot y (bfgsStep H g α))⁻¹ • outer y y := by
  let s := bfgsStep H g α
  let t := dot y s
  let q := metricEnergy H g
  let M := H⁻¹ - q⁻¹ • outer g g
  let C := M + t⁻¹ • outer y y
  let Q : Mat n := 1 - t⁻¹ • outer y s
  have ht0 : t ≠ 0 := ht.ne'
  have hα0 : α ≠ 0 := hα.ne'
  have hsym : H.IsSymm := by
    simpa only [Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hH.isHermitian
  have hMs : M.mulVec s = 0 := annihilatedMatrix_mul_step hH hg α
  have hCs : C.mulVec s = y := by
    dsimp only [C]
    rw [Matrix.add_mulVec, hMs, Matrix.smul_mulVec_assoc, outer_mulVec]
    change 0 + t⁻¹ • (t • y) = y
    rw [smul_smul, inv_mul_cancel₀ ht0, one_smul, zero_add]
  have hCP : C * (1 - t⁻¹ • outer s y) = M := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul,
      BFGSCompression.mul_outer, hCs]
    dsimp only [C]
    abel
  have horth : outer g s * Q = 0 := by
    dsimp only [Q]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul,
      BFGSCompression.outer_mul_outer]
    have hsy : dot s y = t := dotProduct_comm _ _
    rw [hsy, smul_smul, inv_mul_cancel₀ ht0, one_smul, sub_self]
  have hMH : M * H = 1 + (α * q)⁻¹ • outer g s := by
    dsimp only [M]
    rw [Matrix.sub_mul, Matrix.nonsing_inv_mul H hH.det_pos.ne'.isUnit,
      Matrix.smul_mul, BFGSCompression.outer_mul, hsym.eq]
    have hq0 : q ≠ 0 := (metricEnergy_pos hH hg).ne'
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      outer, s, bfgsStep, Pi.smul_apply]
    field_simp
    ring
  have hMHQ : M * H * Q = Q := by
    rw [hMH, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, horth,
      smul_zero, add_zero]
  have hprod : C * inverseBFGS H s y = 1 := by
    change C * ((1 - t⁻¹ • outer s y) * H * Q + t⁻¹ • outer s s) = 1
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hCP, hMHQ,
      Matrix.mul_smul, BFGSCompression.mul_outer, hCs]
    dsimp only [Q]
    abel
  exact Matrix.inv_eq_left_inv hprod

/-- The exact top determinant identity for the actual full inverse-BFGS update.
It uses the same genuine two-by-two determinant lemma as the principal hierarchy. -/
theorem inverseBFGS_det {n : ℕ} {H : Mat n} (hH : H.PosDef)
    (s y : Vec n) (ht : dot y s ≠ 0) :
    (inverseBFGS H s y).det =
      (dot s (H⁻¹.mulVec s) / dot y s) * H.det := by
  let t := dot y s
  let r := dot y (H.mulVec y)
  have hsym : H.IsSymm := by
    simpa only [Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hH.isHermitian
  have hexp : inverseBFGS H s y =
      H + (r / t ^ 2 + t⁻¹) • outer s s +
        (-t⁻¹) • (outer s (H.mulVec y) + outer (H.mulVec y) s) := by
    have htrans : (1 - t⁻¹ • outer s y)ᵀ = (1 : Mat n) - t⁻¹ • outer y s := by
      simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
        outer_transpose]
    have he := BFGSCompression.projection_expansion H s y t hsym
    rw [htrans] at he
    change (1 - t⁻¹ • outer s y) * H * (1 - t⁻¹ • outer y s) +
      t⁻¹ • outer s s = _
    rw [he]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, r]
    ring
  rw [hexp, CompressionDeterminant.det_rank_two _ _ _ _ _ hH.det_pos.ne'.isUnit hsym,
    inverse_mul_mulVec hH]
  have hsy : dot s y = t := dotProduct_comm _ _
  have hyy : dot (H.mulVec y) y = r := dotProduct_comm _ _
  rw [hsy, hyy]
  change H.det * ((1 + -t⁻¹ * t) ^ 2 +
    dot s (H⁻¹.mulVec s) * (r / t ^ 2 + t⁻¹ - (-t⁻¹) ^ 2 * r)) =
      dot s (H⁻¹.mulVec s) / t * H.det
  have ht0 : t ≠ 0 := ht
  field_simp
  ring

/-- Exact determinant update in the accepted-step energy notation. -/
theorem inverseBFGS_step_det {n : ℕ} {H : Mat n} (hH : H.PosDef)
    (g y : Vec n) (α : ℝ) (ht : dot y (bfgsStep H g α) ≠ 0) :
    (inverseBFGS H (bfgsStep H g α) y).det =
      (α ^ 2 * metricEnergy H g / dot y (bfgsStep H g α)) * H.det := by
  rw [inverseBFGS_det hH _ _ ht, inverse_mul_step hH]
  have he : dot (bfgsStep H g α) (-α • g) = α ^ 2 * metricEnergy H g := by
    rw [dot_smul_right]
    have hc : dot (bfgsStep H g α) g = dot g (bfgsStep H g α) :=
      dotProduct_comm _ _
    rw [hc, dot_bfgsStep]
    ring
  rw [he]

/-- The source's exact determinant ratio, with beta defined by actual gradients. -/
theorem inverseBFGS_step_det_beta {n : ℕ} {H : Mat n} (hH : H.PosDef)
    {g : Vec n} (hg : g ≠ 0) (y : Vec n) {α : ℝ} (hα : 0 < α)
    (ht : 0 < dot y (bfgsStep H g α)) :
    (inverseBFGS H (bfgsStep H g α) y).det =
      (α / (-dot y (H.mulVec g) / metricEnergy H g)) * H.det := by
  have hq : metricEnergy H g ≠ 0 := (metricEnergy_pos hH hg).ne'
  have hα0 : α ≠ 0 := hα.ne'
  have hcurv := curvature_eq_alpha_beta_q H g y α hq
  have hb : -dot y (H.mulVec g) / metricEnergy H g ≠ 0 := by
    intro hz
    rw [hz, mul_zero, zero_mul] at hcurv
    exact ht.ne' hcurv
  rw [inverseBFGS_step_det hH g y α ht.ne', hcurv]
  have hy : dot y (H.mulVec g) ≠ 0 := neg_ne_zero.mp (div_ne_zero_iff.mp hb).1
  field_simp [hα0, hq, hy]
  ring

end BfgsVerification
