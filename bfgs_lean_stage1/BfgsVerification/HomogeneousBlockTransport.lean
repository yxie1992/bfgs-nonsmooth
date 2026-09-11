import BfgsVerification.AffineImageLifting

/-! Exact finite-prefix lifting. Gradients through index N suffice for steps
through index N and points through index N+1: the final arriving step is covered
even when its new gradient leaves the subspace. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace AffineProjection

theorem matrix_lift_prefix {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) (R : FullBFGSRun n) (gbar : ℕ → Vec r)
    (N : ℕ) (hg : ∀ k, k ≤ N → Aᵀ.mulVec (gbar k) = R.g k)
    (k : ℕ) (hk : k ≤ N) :
    R.H k * Aᵀ = lift A (R.H 0) * compress A (R.H k) := by
  let D : Mat n := 1 - lift A (R.H 0) * A
  have hD : ∀ k, k ≤ N → D * R.H k * Aᵀ = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      dsimp only [D]
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul]
      have h := lift_mul_compress A hA (R.positive_definite 0)
      unfold compress at h
      simp only [← Matrix.mul_assoc] at h
      rw [h, sub_self]
    | succ k ih =>
      intro hk
      have hk0 : k ≤ N := by omega
      have hi := ih hk0
      have hs : D.mulVec (bfgsStep (R.H k) (R.g k) (R.α k)) = 0 := by
        rw [bfgsStep, Matrix.mulVec_smul, ← hg k hk0]
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hi,
          Matrix.zero_mulVec, smul_zero]
      have hy : R.g (k+1) - R.g k = Aᵀ.mulVec (gbar (k+1) - gbar k) := by
        rw [Matrix.mulVec_sub, hg (k+1) hk, hg k hk0]
      rw [R.update k, hy]
      exact inverseBFGS_annihilator A D (R.H k) _ _ hi hs
  have h := hD k hk
  dsimp only [D] at h
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul] at h
  have he := sub_eq_zero.mp h
  simpa only [compress, Matrix.mul_assoc] using he

theorem step_lift_prefix {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) (R : FullBFGSRun n) (gbar : ℕ → Vec r)
    (N : ℕ) (hg : ∀ k, k ≤ N → Aᵀ.mulVec (gbar k) = R.g k)
    (k : ℕ) (hk : k ≤ N) :
    bfgsStep (R.H k) (R.g k) (R.α k) =
      (lift A (R.H 0)).mulVec (A.mulVec (bfgsStep (R.H k) (R.g k) (R.α k))) := by
  have h : (R.H k).mulVec (R.g k) =
      (lift A (R.H 0)).mulVec (A.mulVec ((R.H k).mulVec (R.g k))) := by
    have he := congrArg (fun M : Matrix (Fin n) (Fin r) ℝ => M.mulVec (gbar k))
      (matrix_lift_prefix A hA R gbar N hg k hk)
    simpa only [compress, ← Matrix.mulVec_mulVec, hg k hk] using he
  simp only [bfgsStep, Matrix.mulVec_smul]
  exact congrArg (fun v => -R.α k • v) h

end AffineProjection
namespace AdmissibleBFGSRun
open AffineProjection

/-- All block points lie in the fixed lifted affine space. The endpoint at N+1
requires no membership condition on the new gradient at N+1. -/
theorem affine_iterate_lift_prefix {n r : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) (gbar : ℕ → Vec r)
    (N : ℕ) (hg : ∀ k, k ≤ N → Aᵀ.mulVec (gbar k) = R.g k)
    (k : ℕ) (hk : k ≤ N+1) :
    R.x k = R.x 0 + (lift A (R.H 0)).mulVec (A.mulVec (R.x k) - A.mulVec (R.x 0)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk0 : k ≤ N := by omega
    have ih0 := ih (by omega)
    have hs := AffineProjection.step_lift_prefix A hA R.toFullBFGSRun gbar N hg k hk0
    change bfgsStep (R.H k) (R.g k) (R.α k) =
      (lift A (R.H 0)).mulVec (A.mulVec (bfgsStep (R.H k) (R.g k) (R.α k))) at hs
    rw [R.step, Matrix.mulVec_add]
    rw [show A.mulVec (R.x k) + A.mulVec (bfgsStep (R.H k) (R.g k) (R.α k)) -
      A.mulVec (R.x 0) = (A.mulVec (R.x k) - A.mulVec (R.x 0)) +
      A.mulVec (bfgsStep (R.H k) (R.g k) (R.α k)) by abel, Matrix.mulVec_add]
    calc
      _ = (R.x 0 + (lift A (R.H 0)).mulVec (A.mulVec (R.x k) - A.mulVec (R.x 0))) +
          bfgsStep (R.H k) (R.g k) (R.α k) := congrArg (fun z => z + _) ih0
      _ = _ := by
        simpa only [add_assoc] using congrArg
          (fun v => (R.x 0 + (lift A (R.H 0)).mulVec
            (A.mulVec (R.x k) - A.mulVec (R.x 0))) + v) hs

end AdmissibleBFGSRun
end BfgsVerification
