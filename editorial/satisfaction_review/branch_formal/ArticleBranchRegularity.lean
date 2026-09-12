import BfgsVerification.LIdentityGeometry

/-! Exact branch-level negative regularity in the lower-curvature article.
Second differentiability means differentiability of the Frechet derivative.
This supplements, without modifying, the original scalar and failure results. -/
noncomputable section
open scoped Topology
open Set Filter Matrix
namespace ArticleBranchRegularity
open BfgsVerification

/-- Each of the three actual unwhitened scalar-ridge branches fails to have a
second Frechet derivative at the origin. -/
theorem branch_not_twice_differentiable_zero (i : Fin 3) :
    ¬ DifferentiableAt ℝ (fderiv ℝ (LEmbedding.branch i.castSucc)) (0 : Vec 2) := by
  intro hsecond
  let b := LEmbedding.parameter i
  let v : Vec 2 := b⁻¹ • LEmbedding.center
  have hb : b ≠ 0 := by
    have h := (LEmbedding.parameter_bounds i).1
    dsimp [b]
    linarith
  have hv : dot (LEmbedding.slope i) v = 1 := by
    simp only [v, dot, Pi.smul_apply, smul_eq_mul]
    rw [show (∑ j, LEmbedding.slope i j * (b⁻¹ * LEmbedding.center j)) =
      b⁻¹ * ∑ j, LEmbedding.slope i j * LEmbedding.center j by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring]
    change b⁻¹ * b = 1
    exact inv_mul_cancel₀ hb
  have hr (x : Vec 2) : LEmbedding.residualGradient i.castSucc x =
      LEmbedding.ridgeGradient i x := by fin_cases i <;> rfl
  have he (t : ℝ) : (fderiv ℝ (LEmbedding.branch i.castSucc) (t • v)) v =
      LEmbedding.mu * t * dot v v + LScalar.phiFirst b t := by
    rw [(LEmbedding.branch_hasGradient i.castSucc (t • v)).fderiv,
      gradientFunctional_apply, LEmbedding.branchGradient, hr, LEmbedding.ridgeGradient]
    have hs : dot (LEmbedding.slope i) (t • v) = t := by
      simpa only [hv,mul_one] using dot_smul_right t (LEmbedding.slope i) v
    rw [hs]
    simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
    have hv' : (∑ j, LEmbedding.slope i j * v j) = 1 := hv
    calc
      _ = LEmbedding.mu * t * (∑ j, v j * v j) + LScalar.phiFirst b t *
          (∑ j, LEmbedding.slope i j * v j) := by
        congr 1 <;> (rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring)
      _ = _ := by rw [hv']; ring
  have hd : DifferentiableAt ℝ (fun t : ℝ =>
      (fderiv ℝ (LEmbedding.branch i.castSucc) (t • v)) v) 0 := by
    have hcomp : DifferentiableAt ℝ (fun t : ℝ =>
        fderiv ℝ (LEmbedding.branch i.castSucc) (t • v)) 0 := by
      apply DifferentiableAt.comp 0 _ (differentiableAt_id.smul_const v)
      simpa only [id_eq,zero_smul] using hsecond
    exact hcomp.clm_apply (differentiableAt_const v)
  have hlin : DifferentiableAt ℝ (fun t : ℝ => LEmbedding.mu * t * dot v v) 0 := by
    fun_prop
  have hscalar : DifferentiableAt ℝ (LScalar.phiFirst b) 0 := by
    convert hd.sub hlin using 1
    funext t
    rw [he]
    ring
  apply LScalar.phi_not_twice_differentiable_zero
    (LEmbedding.parameter_bounds i).1.le (LEmbedding.parameter_bounds i).2.le
  simpa only [LScalar.deriv_phi (LEmbedding.parameter_bounds i).1.le
    (LEmbedding.parameter_bounds i).2.le] using hscalar

/-- The three actual branches of the one fixed identity-initialized objective
retain the same failure of second differentiability after its fixed whitening. -/
theorem whitened_branch_not_twice_differentiable_zero (i : Fin 3) :
    ¬ DifferentiableAt ℝ (fderiv ℝ (LWhitening.smoothBranch i.castSucc)) (0 : Vec 2) := by
  intro hd
  have h := (AffineWhitening.second_differentiableAt_iff
    LWhitening.coordinateMatrix LWhitening.coordinateMatrix_invertible
    (LEmbedding.branch i.castSucc) (0 : Vec 2)).mp hd
  exact branch_not_twice_differentiable_zero i (by simpa only [Matrix.mulVec_zero] using h)

/-- One literal strengthened endpoint for the article: the unchanged full
identity-initialized failure contract, together with the actual three whitened
branches failing second differentiability at the minimizer. -/
theorem smoothLocalFailure_with_branch_obstruction :
    LWhitening.SmoothLocalFailureTarget ∧
      ∀ i : Fin 3, ¬ DifferentiableAt ℝ
        (fderiv ℝ (LWhitening.smoothBranch i.castSucc)) (0 : Vec 2) :=
  ⟨LWhitening.smoothLocalFailure, whitened_branch_not_twice_differentiable_zero⟩

end ArticleBranchRegularity
