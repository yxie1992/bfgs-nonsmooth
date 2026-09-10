import BfgsVerification.BFGSUpdate

/-! Positive definiteness and curvature are consequences of the ordinary full
inverse-BFGS update and weak Wolfe, starting only from an SPD initial matrix. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace BfgsVerification

/-- A nonzero gradient has strictly positive energy in an SPD metric. -/
theorem metricEnergy_pos {n : ℕ} {H : Mat n} (hH : H.PosDef)
    {g : Vec n} (hg : g ≠ 0) : 0 < metricEnergy H g := by
  simpa only [metricEnergy, dot, dotProduct, star_trivial] using hH.2 g hg

theorem outer_mulVec {n : ℕ} (u v x : Vec n) :
    (outer u v).mulVec x = dot v x • u := by
  ext i
  simp only [Matrix.mulVec, dotProduct, outer, dot, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem outer_transpose {n : ℕ} (u v : Vec n) :
    (outer u v)ᵀ = outer v u := by
  ext i j
  simp only [Matrix.transpose_apply, outer, mul_comm]

/-- Exact quadratic form of a matrix congruence. -/
theorem metricEnergy_congruence {n : ℕ} (H A : Mat n) (x : Vec n) :
    metricEnergy (Aᵀ * H * A) x = metricEnergy H (A.mulVec x) := by
  change x ⬝ᵥ (Aᵀ * H * A) *ᵥ x = (A *ᵥ x) ⬝ᵥ H *ᵥ (A *ᵥ x)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec]
  rw [vecMul_transpose]

/-- Ordinary full inverse-BFGS preserves positive definiteness whenever its
actual curvature product is positive. No matrix bound is required. -/
theorem inverseBFGS_posDef {n : ℕ} {H : Mat n} (hH : H.PosDef)
    (s y : Vec n) (ht : 0 < dot y s) : (inverseBFGS H s y).PosDef := by
  let t := dot y s
  let A : Mat n := 1 - t⁻¹ • outer y s
  have hA : Aᵀ = 1 - t⁻¹ • outer s y := by
    simp only [A, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      outer_transpose]
  have hu : inverseBFGS H s y = Aᵀ * H * A + t⁻¹ • outer s s := by
    rw [hA]
    rfl
  rw [hu]
  constructor
  · apply Matrix.IsHermitian.add
    · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        isHermitian_conjTranspose_mul_mul A hH.isHermitian
    · apply Matrix.IsHermitian.ext
      intro i j
      simp only [Matrix.smul_apply, smul_eq_mul, outer, star_trivial]
      ring
  · intro x hx
    have hquad : dot x ((Aᵀ * H * A + t⁻¹ • outer s s).mulVec x) =
        metricEnergy H (A.mulVec x) + t⁻¹ * (dot s x) ^ 2 := by
      change x ⬝ᵥ (Aᵀ * H * A + t⁻¹ • outer s s) *ᵥ x = _
      rw [Matrix.add_mulVec, dotProduct_add]
      change metricEnergy (Aᵀ * H * A) x +
        dot x ((t⁻¹ • outer s s).mulVec x) = _
      rw [metricEnergy_congruence, Matrix.smul_mulVec_assoc, outer_mulVec,
        dot_smul_right, dot_smul_right]
      have hcomm : dot x s = dot s x := dotProduct_comm x s
      rw [hcomm]
      ring
    have hnonneg : 0 ≤ metricEnergy H (A.mulVec x) := by
      simpa only [metricEnergy, dot, dotProduct, star_trivial] using
        hH.posSemidef.2 (A.mulVec x)
    have htinv : 0 < t⁻¹ := inv_pos.mpr ht
    have hgoal : 0 < dot x ((Aᵀ * H * A + t⁻¹ • outer s s).mulVec x) := by
      rw [hquad]
      by_cases hsx : dot s x = 0
      · have hAx : A.mulVec x = x := by
          simp only [A, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc,
            outer_mulVec, hsx, zero_smul, smul_zero, sub_zero]
        rw [hAx, hsx]
        simpa using metricEnergy_pos hH hx
      · exact add_pos_of_nonneg_of_pos hnonneg
          (mul_pos htinv (sq_pos_of_ne_zero hsx))
    simpa only [dot, dotProduct, star_trivial] using hgoal

/-- The accepted step has the exact negative predicted-decrease product. -/
theorem dot_bfgsStep {n : ℕ} (H : Mat n) (g : Vec n) (α : ℝ) :
    dot g (bfgsStep H g α) = -(α * metricEnergy H g) := by
  rw [bfgsStep, dot_smul_right]
  unfold metricEnergy
  ring

/-- Weak Wolfe yields a positive lower bound for the actual curvature product
before a matrix-run invariant has been assumed or constructed. -/
theorem curvature_ge_of_weakWolfe {n : ℕ} (H : Mat n) (g gnext : Vec n)
    (α c₂ : ℝ)
    (hw : c₂ * dot g (bfgsStep H g α) ≤ dot gnext (bfgsStep H g α)) :
    (1 - c₂) * (α * metricEnergy H g) ≤
      dot (gnext - g) (bfgsStep H g α) := by
  rw [dot_sub_left, dot_bfgsStep]
  rw [dot_bfgsStep] at hw
  linarith

/-- With an SPD current matrix and nonzero gradient, ordinary weak Wolfe
implies strictly positive curvature for every positive accepted length. -/
theorem curvature_pos_of_weakWolfe {n : ℕ} {H : Mat n} (hH : H.PosDef)
    {g : Vec n} (hg : g ≠ 0) (gnext : Vec n) {α c₂ : ℝ}
    (hα : 0 < α) (hc₂ : c₂ < 1)
    (hw : c₂ * dot g (bfgsStep H g α) ≤ dot gnext (bfgsStep H g α)) :
    0 < dot (gnext - g) (bfgsStep H g α) :=
  lt_of_lt_of_le
    (mul_pos (sub_pos.mpr hc₂) (mul_pos hα (metricEnergy_pos hH hg)))
    (curvature_ge_of_weakWolfe H g gnext α c₂ hw)

/-- The infinite nonstationary ordinary full-BFGS recursion propagates all
positivity invariants from its initial SPD matrix. In particular, positivity
at later iterations is a conclusion, not a field assumed at every iteration. -/
theorem fullBFGS_positive_invariants {n : ℕ}
    (H : ℕ → Mat n) (g : ℕ → Vec n) (α : ℕ → ℝ) (c₂ : ℝ)
    (hH0 : (H 0).PosDef) (hg : ∀ k, g k ≠ 0)
    (hα : ∀ k, 0 < α k) (hc₂ : c₂ < 1)
    (hw : ∀ k, c₂ * dot (g k) (bfgsStep (H k) (g k) (α k)) ≤
      dot (g (k + 1)) (bfgsStep (H k) (g k) (α k)))
    (hupdate : ∀ k, H (k + 1) =
      inverseBFGS (H k) (bfgsStep (H k) (g k) (α k)) (g (k + 1) - g k)) :
    ∀ k, (H k).PosDef ∧ 0 < metricEnergy (H k) (g k) ∧
      0 < dot (g (k + 1) - g k) (bfgsStep (H k) (g k) (α k)) := by
  have hH : ∀ k, (H k).PosDef := by
    intro k
    induction k with
    | zero => exact hH0
    | succ k ih =>
      rw [hupdate]
      exact inverseBFGS_posDef ih _ _
        (curvature_pos_of_weakWolfe ih (hg k) (g (k + 1)) (hα k) hc₂ (hw k))
  intro k
  exact ⟨hH k, metricEnergy_pos (hH k) (hg k),
    curvature_pos_of_weakWolfe (hH k) (hg k) (g (k + 1)) (hα k) hc₂ (hw k)⟩

end BfgsVerification
