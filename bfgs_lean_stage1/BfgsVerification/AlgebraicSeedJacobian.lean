import BfgsVerification.AlgebraicSeedRoot
import BfgsVerification.AffineProjection
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Matrix
namespace BfgsVerification.AlgebraicSeed
open PolynomialBounds AffineProjection

theorem P_hasFDerivAt_center : HasFDerivAt P (matrixCLM J) center := by
  have h0 := (ContinuousLinearMap.proj (0 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasFDerivAt (x := center)
  have h1 := (ContinuousLinearMap.proj (1 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasFDerivAt (x := center)
  have hU := (h0.const_mul 127).add (h1.const_mul 16)
  have hV := ((h0.const_mul 16).sub (h1.const_mul 127)).sub_const 16
  have hR := h0.sub (h1.const_mul 8)
  have hK := (((h0.mul h0).const_mul 8).add ((h1.mul h1).const_mul 8)).add h1 |>.sub_const 8
  have hT := ((h0.mul h0).sub h0).add (h1.mul h1)
  have hY := ((h0.sub_const 1).mul (h0.sub_const 1)).add (h1.mul h1)
  have hP0 := ((hR.mul hK).const_mul 264192).sub ((hU.mul hV).mul (hU.add_const 129))
  have hP1 := (((hV.mul hT).mul hK).const_mul 16).sub ((hR.mul hU).mul hY)
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert hP0 using 1
    · funext x
      dsimp [P,U,V,R,K]
      ring
    · ext v
      norm_num [matrixCLM_apply,J,center,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
      <;> ring
  · convert hP1 using 1
    · funext x
      dsimp [P,U,V,R,K,T,Y]
      ring
    · ext v
      norm_num [matrixCLM_apply,J,center,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
      <;> ring

theorem actual_Jacobian : fderiv ℝ P center = matrixCLM J := P_hasFDerivAt_center.fderiv

theorem P_differentiable : Differentiable ℝ P := by
  apply differentiable_pi.mpr
  intro i
  fin_cases i <;> dsimp [P,U,V,R,K,T,Y] <;> fun_prop

theorem newton_lipschitz_radius {x y : Vec 2} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ 1) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖newton x-newton y‖ ≤ 7000*r*‖x-y‖ := by
  have hx' : ∀ i, |x i| ≤ r := fun i => (show |x i| ≤ ‖x‖ from norm_le_pi_norm x i).trans hx
  have hy' : ∀ i, |y i| ≤ r := fun i => (show |y i| ≤ ‖y‖ from norm_le_pi_norm y i).trans hy
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 7000*r*‖x-y‖)).mpr
  intro i
  fin_cases i
  · change |newton x 0-newton y 0| ≤ _
    rw [expansion0,expansion0,add_sub_add_left_eq_sub]
    exact (polynomial_quadratic_abs_sub_le coeff0 words words_quadratic hr hx' hy').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right coeff0_bound hr0) (norm_nonneg _))
  · change |newton x 1-newton y 1| ≤ _
    rw [expansion1,expansion1,add_sub_add_left_eq_sub]
    exact (polynomial_quadratic_abs_sub_le coeff1 words words_quadratic hr hx' hy').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right coeff1_bound hr0) (norm_nonneg _))

theorem newton_hasFDerivAt (x : Vec 2) : HasFDerivAt newton
    (ContinuousLinearMap.id ℝ (Vec 2)-(matrixCLM M).comp (fderiv ℝ P (center+x))) x := by
  have ha := (hasFDerivAt_id (𝕜 := ℝ) x).const_add center
  have hb := (P_differentiable (center+x)).hasFDerivAt.comp x ha
  have hc := (matrixCLM M).hasFDerivAt.comp x hb
  convert (hasFDerivAt_id (𝕜 := ℝ) x).sub hc using 1 <;> simp only [newton,matrixCLM_apply,ContinuousLinearMap.comp_id]


theorem source_Jacobian_uniform {z : Vec 2} (hz : ‖z-center‖ ≤ radius) :
    ‖ContinuousLinearMap.id ℝ (Vec 2)-(matrixCLM M).comp (fderiv ℝ P z)‖ ≤ 7000*(4*radius/3) := by
  let r : ℝ := 4*radius/3
  have hr0 : 0 ≤ r := by dsimp [r]; have := radius_pos; positivity
  have hr1 : r ≤ 1 := by norm_num [r,radius]
  have hx : ‖z-center‖ < r := hz.trans_lt (by dsimp [r]; have := radius_pos; linarith)
  have he : ∀ᶠ x in 𝓝 (z-center), ‖x‖ < r :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hx
  have hb : ‖fderiv ℝ newton (z-center)‖ ≤ 7000*r := by
    apply norm_fderiv_le_of_lip' ℝ (by positivity)
    filter_upwards [he] with x hx'
    exact newton_lipschitz_radius hr0 hr1 hx'.le hx.le
  rw [(newton_hasFDerivAt (z-center)).fderiv] at hb
  have heq : center+(z-center)=z := add_sub_cancel _ _
  rw [heq] at hb
  exact hb

theorem source_Jacobian_bound {z : Vec 2} (hz : ‖z-center‖ ≤ radius) :
    ‖ContinuousLinearMap.id ℝ (Vec 2)-(matrixCLM M).comp (fderiv ℝ P z)‖ < 1/(10:ℝ)^26 :=
  (source_Jacobian_uniform hz).trans_lt (by norm_num [radius])

theorem source_Jacobian_sup_bound :
    sSup ((fun z => ‖ContinuousLinearMap.id ℝ (Vec 2)-(matrixCLM M).comp (fderiv ℝ P z)‖) ''
      {z | ‖z-center‖ ≤ radius}) < 1/(10:ℝ)^26 := by
  have hn : ((fun z => ‖ContinuousLinearMap.id ℝ (Vec 2)-(matrixCLM M).comp (fderiv ℝ P z)‖) ''
      {z | ‖z-center‖ ≤ radius}).Nonempty := by
    refine ⟨_,⟨center,?_,rfl⟩⟩
    change ‖center-center‖ ≤ radius
    simpa only [sub_self,norm_zero] using radius_pos.le
  have hb : sSup ((fun z => ‖ContinuousLinearMap.id ℝ (Vec 2)-(matrixCLM M).comp (fderiv ℝ P z)‖) ''
      {z | ‖z-center‖ ≤ radius}) ≤ 7000*(4*radius/3) := by
    apply csSup_le hn
    rintro _ ⟨z,hz,rfl⟩
    exact source_Jacobian_uniform hz
  exact hb.trans_lt (by norm_num [radius])

theorem M_eq_J_inverse : M=J⁻¹ := (Matrix.inv_eq_left_inv M_left_inverse).symm

theorem source_inverse_Jacobian : (matrixCLM M).comp (fderiv ℝ P center) = ContinuousLinearMap.id ℝ (Vec 2) := by
  rw [actual_Jacobian]
  ext v i
  simp only [ContinuousLinearMap.comp_apply,matrixCLM_apply,ContinuousLinearMap.id_apply]
  rw [mulVec_mulVec,M_left_inverse,one_mulVec]

theorem source_residual : ‖M.mulVec (P center)‖ < 1/(10:ℝ)^50 := by
  have hh := newton_zero_small
  simpa only [newton,add_zero,zero_sub,norm_neg] using hh

end BfgsVerification.AlgebraicSeed
