import BfgsVerification.AffineCompression

/-! A genuine full-BFGS run on a linear-image objective descends to a genuine
full-BFGS run, with actual derivatives and exactly the same accepted lengths. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace AffineProjection

variable {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) (hA : FullRowRank A)
    (F : Vec r → ℝ) (R : AdmissibleBFGSRun n (fun x => F (A.mulVec x)))

def projectedGradient (k : ℕ) : Vec r := (rightInverse A)ᵀ.mulVec (R.g k)

include hA R

theorem projected_gradient_lift (k : ℕ) : Aᵀ.mulVec (projectedGradient A F R k) = R.g k :=
  gradient_in_image A (rightInverse A) (mul_rightInverse A hA) F (R.x k) (R.g k) (R.hasGradient k)

theorem projected_hasGradient (k : ℕ) :
    HasFDerivAt F (gradientFunctional (projectedGradient A F R k)) (A.mulVec (R.x k)) :=
  hasGradient_descend A (rightInverse A) (mul_rightInverse A hA) F (R.x k) (R.g k) (R.hasGradient k)

theorem image_objective_convex : ConvexOn ℝ Set.univ F := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := R.convex.2 (show (rightInverse A).mulVec x ∈ Set.univ from mem_univ _)
    (show (rightInverse A).mulVec y ∈ Set.univ from mem_univ _) ha hb hab
  simpa only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    mul_rightInverse A hA, Matrix.one_mulVec] using h

theorem projected_step (k : ℕ) :
    A.mulVec (bfgsStep (R.H k) (R.g k) (R.α k)) =
      bfgsStep (compress A (R.H k)) (projectedGradient A F R k) (R.α k) := by
  rw [← projected_gradient_lift A hA F R k]
  exact project_step A _ _ _

theorem projected_update (k : ℕ) :
    compress A (R.H (k + 1)) =
      inverseBFGS (compress A (R.H k))
        (bfgsStep (compress A (R.H k)) (projectedGradient A F R k) (R.α k))
        (projectedGradient A F R (k + 1) - projectedGradient A F R k) := by
  rw [R.update]
  have hy : R.g (k + 1) - R.g k =
      Aᵀ.mulVec (projectedGradient A F R (k + 1) - projectedGradient A F R k) := by
    rw [Matrix.mulVec_sub, projected_gradient_lift A hA F R,
      projected_gradient_lift A hA F R]
  rw [hy, inverseBFGS_compress, projected_step A hA F R]

/-- The projected trajectory is packaged only after its actual derivative,
positive definiteness, step, and full inverse-update identities are proved. -/
def projectRun (A : Matrix (Fin r) (Fin n) ℝ) (hA : FullRowRank A)
    (F : Vec r → ℝ) (R : AdmissibleBFGSRun n (fun x => F (A.mulVec x))) :
    AdmissibleBFGSRun r F where
  convex := image_objective_convex A hA F R
  x k := A.mulVec (R.x k)
  H k := compress A (R.H k)
  g := projectedGradient A F R
  α := R.α
  c₁ := R.c₁
  c₂ := R.c₂
  c₁_pos := R.c₁_pos
  c₁_lt_c₂ := R.c₁_lt_c₂
  c₂_lt_one := R.c₂_lt_one
  initial_posDef := compress_posDef A hA R.initial_posDef
  alpha_pos := R.alpha_pos
  gradient_nonzero k := by
    intro hk
    apply R.gradient_nonzero k
    rw [← projected_gradient_lift A hA F R k, hk, Matrix.mulVec_zero]
  hasGradient := projected_hasGradient A hA F R
  step k := by
    rw [R.step, Matrix.mulVec_add, projected_step A hA F R]
  update := projected_update A hA F R
  armijo k := by
    have h := R.armijo k
    rw [← projected_gradient_lift A hA F R k, dot_transpose_mulVec] at h
    simp only [project_step] at h
    exact h
  weak_wolfe k := by
    have h := R.weak_wolfe k
    rw [← projected_gradient_lift A hA F R k,
      ← projected_gradient_lift A hA F R (k + 1), dot_transpose_mulVec,
      dot_transpose_mulVec] at h
    simp only [project_step] at h
    exact h

@[simp] theorem projectRun_x (k : ℕ) : (projectRun A hA F R).x k = A.mulVec (R.x k) := rfl
@[simp] theorem projectRun_H (k : ℕ) : (projectRun A hA F R).H k = compress A (R.H k) := rfl
@[simp] theorem projectRun_alpha (k : ℕ) : (projectRun A hA F R).α k = R.α k := rfl
@[simp] theorem projectRun_value (k : ℕ) : F ((projectRun A hA F R).x k) = F (A.mulVec (R.x k)) := rfl

@[simp] theorem projectRun_q (k : ℕ) : (projectRun A hA F R).q k = R.q k := by
  change metricEnergy (compress A (R.H k)) (projectedGradient A F R k) = metricEnergy (R.H k) (R.g k)
  rw [← project_energy, projected_gradient_lift A hA F R]

@[simp] theorem projectRun_d (k : ℕ) : (projectRun A hA F R).d k = R.d k := by
  simp only [AdmissibleBFGSRun.d, projectRun_alpha, projectRun_q]

@[simp] theorem projectRun_displacement (k : ℕ) :
    (projectRun A hA F R).displacement k = A.mulVec (R.displacement k) := by
  exact (projected_step A hA F R k).symm

@[simp] theorem projectRun_curvature (k : ℕ) :
    (projectRun A hA F R).curvature k = R.curvature k := by
  unfold AdmissibleBFGSRun.curvature AdmissibleBFGSRun.gradientChange
  rw [projectRun_displacement, ← dot_transpose_mulVec, Matrix.mulVec_sub]
  change dot (Aᵀ.mulVec (projectedGradient A F R (k + 1)) -
    Aᵀ.mulVec (projectedGradient A F R k)) (R.displacement k) = _
  rw [projected_gradient_lift A hA F R, projected_gradient_lift A hA F R]

end AffineProjection
end BfgsVerification
