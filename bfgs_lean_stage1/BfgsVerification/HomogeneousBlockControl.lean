import BfgsVerification.HomogeneousLowRankLine

/-! Actual finite opposite-gradient blocks, including the final arriving step.
Their length is unrestricted. Only the initial opposite pair enters the bound. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace HomogeneousBlock

theorem line_lift_collinear {n : ℕ} (a x₀ x x₁ : Vec n)
    (L : Matrix (Fin n) (Fin 1) ℝ)
    (hx : x = x₀ + L.mulVec ((lineMatrix a).mulVec x - (lineMatrix a).mulVec x₀))
    (h₁ : x₁ = x₀ + L.mulVec ((lineMatrix a).mulVec x₁ - (lineMatrix a).mulVec x₀))
    (hne : dot a x₁ - dot a x₀ ≠ 0) :
    x = x₀ + ((dot a x - dot a x₀)/(dot a x₁-dot a x₀)) • (x₁-x₀) := by
  let θ := (dot a x - dot a x₀)/(dot a x₁-dot a x₀)
  have hc : (lineMatrix a).mulVec x - (lineMatrix a).mulVec x₀ =
      θ • ((lineMatrix a).mulVec x₁ - (lineMatrix a).mulVec x₀) := by
    ext i
    change dot a x-dot a x₀ = θ*(dot a x₁-dot a x₀)
    exact (div_mul_cancel₀ _ hne).symm
  have hd : x₁-x₀ = L.mulVec ((lineMatrix a).mulVec x₁ - (lineMatrix a).mulVec x₀) := by
    calc
      x₁-x₀ = (x₀ + L.mulVec ((lineMatrix a).mulVec x₁ - (lineMatrix a).mulVec x₀))-x₀ :=
        congrArg (fun z => z-x₀) h₁
      _ = _ := by abel
  calc
    x = x₀ + L.mulVec ((lineMatrix a).mulVec x - (lineMatrix a).mulVec x₀) := hx
    _ = x₀ + θ • (x₁-x₀) := by rw [hc, Matrix.mulVec_smul, ← hd]

end HomogeneousBlock
namespace AdmissibleBFGSRun
open Homogeneous HomogeneousBlock HomogeneousPlanar AffineProjection

/-- Dependence of all consecutive gradients in a finite prefix places every
prefix gradient on the actual initial gradient line. -/
theorem planar_dependent_prefix_line {F : Vec 2 → ℝ} (R : AdmissibleBFGSRun 2 F)
    (N : ℕ) (hd : ∀ k, k < N → pairDet (R.g k) (R.g (k+1)) = 0)
    (k : ℕ) (hk : k ≤ N) : ∃ c : ℝ, R.g k = c • R.g 0 := by
  induction k with
  | zero => exact ⟨1, (one_smul ℝ (R.g 0)).symm⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih (by omega)
    obtain ⟨d, hdg⟩ := exists_smul_of_pairDet_eq_zero (R.g k) (R.g (k+1))
      (R.gradient_nonzero k) (hd k (by omega))
    exact ⟨d*c, by rw [hdg, hc, smul_smul]⟩

/-- Actual block points are collinear with the two endpoint iterates. Membership
of the arriving endpoint's new gradient in the line is not required. -/
theorem planar_dependent_prefix_collinear {F : Vec 2 → ℝ} (R : AdmissibleBFGSRun 2 F)
    (N : ℕ) (hd : ∀ k, k < N → pairDet (R.g k) (R.g (k+1)) = 0)
    (hne : dot (R.g 0) (R.x (N+1)) - dot (R.g 0) (R.x 0) ≠ 0)
    (k : ℕ) (hk : k ≤ N+1) :
    R.x k = R.x 0 + ((dot (R.g 0) (R.x k) - dot (R.g 0) (R.x 0)) /
      (dot (R.g 0) (R.x (N+1)) - dot (R.g 0) (R.x 0))) • (R.x (N+1)-R.x 0) := by
  classical
  let c : ℕ → ℝ := fun j => if hj : j ≤ N then (R.planar_dependent_prefix_line N hd j hj).choose else 0
  have hg (j : ℕ) (hj : j ≤ N) : (lineMatrix (R.g 0))ᵀ.mulVec (fun _ => c j) = R.g j := by
    rw [lineMatrix_transpose_mulVec]
    dsimp [c]
    rw [dif_pos hj]
    exact (R.planar_dependent_prefix_line N hd j hj).choose_spec.symm
  exact line_lift_collinear (R.g 0) (R.x 0) (R.x k) (R.x (N+1)) _
    (R.affine_iterate_lift_prefix _ (lineMatrix_fullRowRank _ (R.gradient_nonzero 0)) _ N hg k hk)
    (R.affine_iterate_lift_prefix _ (lineMatrix_fullRowRank _ (R.gradient_nonzero 0)) _ N hg (N+1) le_rfl) hne

/-- H.7.4 finite block bound. It is uniform in the number N of dependent
transitions, and includes the endpoint of the next independent transition. -/
theorem maxLinear_opposite_block_norm_bound (A : Finset (Vec 2)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun 2 (finiteMaxLinear A hA))
    (hp : ∀ k, 0 < finiteMaxLinear A hA (R.x k)) (N : ℕ) (hN : 1 ≤ N)
    (hd : ∀ k, k < N → pairDet (R.g k) (R.g (k+1)) = 0)
    (κ : ℝ) (hκ : 0 < κ) (hg : R.g 1 = -κ • R.g 0) (k : ℕ) (hk : k ≤ N+1) :
    ‖R.x k‖ ≤ (1+(1+1/κ)/R.c₁)*‖R.x 0‖ + ((1+1/κ)/R.c₁)*‖R.x (N+1)‖ := by
  let F := finiteMaxLinear A hA
  have hh := finiteMaxLinear_homogeneous A hA
  have hc := (R.homogeneous_opposite_contraction hh 0 κ hκ hg (hp 0).le).2
  have he : dot (R.g 0) (R.x 0) = F (R.x 0) := R.homogeneous_euler hh 0
  have hb : dot (R.g 0) (R.x (N+1)) ≤ (1-R.c₁)*F (R.x 0) :=
    (R.homogeneous_support hh 0 _).trans ((R.objective_antitone (by omega : 1 ≤ N+1)).trans hc)
  have hne : dot (R.g 0) (R.x (N+1)) - dot (R.g 0) (R.x 0) ≠ 0 := by
    rw [he]
    have hm := mul_pos R.c₁_pos (hp 0)
    linarith
  have hxhigh : dot (R.g 0) (R.x k) ≤ F (R.x 0) :=
    (R.homogeneous_support hh 0 _).trans (R.objective_antitone (Nat.zero_le k))
  have hxlow : -F (R.x 0)/κ ≤ dot (R.g 0) (R.x k) := by
    have hs := (R.homogeneous_support hh 1 (R.x k)).trans (R.objective_antitone (Nat.zero_le k))
    rw [hg, dot_smul_first] at hs
    apply (div_le_iff₀ hκ).mpr
    nlinarith
  have hcol := R.planar_dependent_prefix_collinear N hd hne k hk
  obtain ⟨hθ, hθC⟩ := interpolation_parameter_bound (R.g 0) (R.x 0) (R.x (N+1)) (R.x k)
    (F (R.x 0)) κ R.c₁ _ (hp 0) hκ R.c₁_pos he hb hxlow hxhigh hcol
  exact interpolation_norm_bound _ _ _ _ _ hθ hθC hcol

end AdmissibleBFGSRun
end BfgsVerification
