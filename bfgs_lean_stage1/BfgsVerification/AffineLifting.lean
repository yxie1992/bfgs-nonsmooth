import BfgsVerification.AffineImageRun

/-! Fixed affine lifting and the exact initial-metric fiber projection.
All matrix invariants hold before any iterate convergence is invoked. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace AffineProjection

theorem lift_mul_compress {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) {H : Mat n} (hH : H.PosDef) :
    lift A H * compress A H = H * Aᵀ := by
  unfold lift
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (compress_posDef A hA hH).det_pos.ne'), Matrix.mul_one]

/-- Strong fixed-image invariant for the actual matrix trajectory. The only
subspace premise is the displayed actual gradient representation. -/
theorem matrix_lift_invariant {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) (R : FullBFGSRun n) (gbar : ℕ → Vec r)
    (hg : ∀ k, Aᵀ.mulVec (gbar k) = R.g k) (k : ℕ) :
    R.H k * Aᵀ = lift A (R.H 0) * compress A (R.H k) := by
  let D : Mat n := 1 - lift A (R.H 0) * A
  have hD : ∀ k, D * R.H k * Aᵀ = 0 := by
    intro k
    induction k with
    | zero =>
      dsimp only [D]
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul]
      have h := lift_mul_compress A hA (R.positive_definite 0)
      unfold compress at h
      simp only [← Matrix.mul_assoc] at h
      rw [h, sub_self]
    | succ k ih =>
      have hs : D.mulVec (bfgsStep (R.H k) (R.g k) (R.α k)) = 0 := by
        rw [bfgsStep, Matrix.mulVec_smul, ← hg k]
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ih,
          Matrix.zero_mulVec, smul_zero]
      have hy : R.g (k + 1) - R.g k = Aᵀ.mulVec (gbar (k + 1) - gbar k) := by
        rw [Matrix.mulVec_sub, hg, hg]
      rw [R.update k, hy]
      exact inverseBFGS_annihilator A D (R.H k) _ _ ih hs
  have hk := hD k
  dsimp only [D] at hk
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul] at hk
  have he := sub_eq_zero.mp hk
  simpa only [compress, Matrix.mul_assoc] using he

/-- Every executed step has the same fixed lift as the initial compressed metric. -/
theorem step_lift {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) (R : FullBFGSRun n) (gbar : ℕ → Vec r)
    (hg : ∀ k, Aᵀ.mulVec (gbar k) = R.g k) (k : ℕ) :
    bfgsStep (R.H k) (R.g k) (R.α k) =
      (lift A (R.H 0)).mulVec (A.mulVec (bfgsStep (R.H k) (R.g k) (R.α k))) := by
  have h : (R.H k).mulVec (R.g k) =
      (lift A (R.H 0)).mulVec (A.mulVec ((R.H k).mulVec (R.g k))) := by
    have he := congrArg (fun M : Matrix (Fin n) (Fin r) ℝ => M.mulVec (gbar k))
      (matrix_lift_invariant A hA R gbar hg k)
    simpa only [compress, ← Matrix.mulVec_mulVec, hg] using he
  simp only [bfgsStep, Matrix.mulVec_smul]
  exact congrArg (fun v => -R.α k • v) h

end AffineProjection
namespace AdmissibleBFGSRun
open AffineProjection

/-- Exact H.7.1 for any actual objective run whose gradients lie in the fixed
transpose image. Global objective factorization is not inferred here. -/
theorem affine_iterate_lift {n r : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) (gbar : ℕ → Vec r)
    (hg : ∀ k, Aᵀ.mulVec (gbar k) = R.g k) (k : ℕ) :
    R.x k = R.x 0 + (lift A (R.H 0)).mulVec (A.mulVec (R.x k) - A.mulVec (R.x 0)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := AffineProjection.step_lift A hA R.toFullBFGSRun gbar hg k
    change bfgsStep (R.H k) (R.g k) (R.α k) =
      (lift A (R.H 0)).mulVec (A.mulVec (bfgsStep (R.H k) (R.g k) (R.α k))) at hs
    rw [R.step, Matrix.mulVec_add]
    rw [show A.mulVec (R.x k) + A.mulVec (bfgsStep (R.H k) (R.g k) (R.α k)) -
      A.mulVec (R.x 0) = (A.mulVec (R.x k) - A.mulVec (R.x 0)) +
      A.mulVec (bfgsStep (R.H k) (R.g k) (R.α k)) by abel, Matrix.mulVec_add]
    calc
      _ = (R.x 0 + (lift A (R.H 0)).mulVec (A.mulVec (R.x k) - A.mulVec (R.x 0))) +
          bfgsStep (R.H k) (R.g k) (R.α k) := congrArg (fun z => z + _) ih
      _ = _ := by
        simpa only [add_assoc] using congrArg
          (fun v => (R.x 0 + (lift A (R.H 0)).mulVec
            (A.mulVec (R.x k) - A.mulVec (R.x 0))) + v) hs

/-- Convergence lifts through a fixed finite matrix; no matrix convergence is assumed. -/
theorem affine_limit_lift {n r : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) (gbar : ℕ → Vec r)
    (hg : ∀ k, Aᵀ.mulVec (gbar k) = R.g k) (zstar : Vec r)
    (hz : Tendsto (fun k => A.mulVec (R.x k)) atTop (𝓝 zstar)) :
    Tendsto R.x atTop (𝓝 (R.x 0 + (lift A (R.H 0)).mulVec (zstar - A.mulVec (R.x 0)))) := by
  have h := (tendsto_const_nhds (x := R.x 0)).add
    (((matrixCLM (lift A (R.H 0))).continuous.tendsto _).comp
      (hz.sub_const (A.mulVec (R.x 0))))
  convert h using 1
  funext k
  exact R.affine_iterate_lift A hA gbar hg k

end AdmissibleBFGSRun
end BfgsVerification
