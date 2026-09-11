import BfgsVerification.AffineLifting

noncomputable section
open Set Matrix
namespace BfgsVerification.AffineProjection

theorem range_mulVec_mul_invertible {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℝ)
    (B : Mat r) (hB : B.det≠0) : range (A*B).mulVec=range A.mulVec := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨B.mulVec x,Matrix.mulVec_mulVec _ _ _⟩
  · rintro ⟨x,rfl⟩
    refine ⟨B⁻¹.mulVec x,?_⟩
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hB.isUnit,Matrix.mul_one]

/-- The fixed image equality asserted in F's linear-image lifting proof,
for actual full BFGS and the actual gradient subspace. -/
theorem matrix_image_constant {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) (R : FullBFGSRun n) (gbar : ℕ → Vec r)
    (hg : ∀ k,Aᵀ.mulVec (gbar k)=R.g k) (k : ℕ) :
    range (R.H k*Aᵀ).mulVec=range (R.H 0*Aᵀ).mulVec := by
  rw [matrix_lift_invariant A hA R gbar hg k,matrix_lift_invariant A hA R gbar hg 0]
  rw [range_mulVec_mul_invertible _ _ (compress_posDef A hA (R.positive_definite k)).det_pos.ne',
    range_mulVec_mul_invertible _ _ (compress_posDef A hA (R.positive_definite 0)).det_pos.ne']

theorem image_objective_matrix_image {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) (F : Vec r → ℝ)
    (R : AdmissibleBFGSRun n (fun x => F (A.mulVec x))) (k : ℕ) :
    range (R.H k*Aᵀ).mulVec=range (R.H 0*Aᵀ).mulVec :=
  matrix_image_constant A hA R.toFullBFGSRun (projectedGradient A F R)
    (projected_gradient_lift A hA F R) k

def ActualImageRangeTarget : Prop := ∀{n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ),
  FullRowRank A → ∀(F : Vec r → ℝ) (R : AdmissibleBFGSRun n (fun x => F (A.mulVec x))) (k : ℕ),
    range (R.H k*Aᵀ).mulVec=range (R.H 0*Aᵀ).mulVec

theorem actualImageRange : ActualImageRangeTarget := @image_objective_matrix_image

end BfgsVerification.AffineProjection
