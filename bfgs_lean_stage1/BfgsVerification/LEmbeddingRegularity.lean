import BfgsVerification.LEmbeddingObjective
import BfgsVerification.DEmbeddingObjective

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.LEmbedding

/-- The two derivative extensions have disjoint interiors, so their common
Lipschitz bound is the maximum of their bounds. Here 768/b exceeds one. -/
theorem scalar_derivative_lipschitz {b : ℝ} (hl : 17/10≤b) (hr : b≤34) :
    LipschitzWith ⟨768/b,by positivity⟩ (LScalar.phiFirst b) := by
  have hb : 0<b := by linarith
  have hK : 1≤768/b := (le_div_iff₀ hb).mpr (by linarith)
  have hpos := LScalar.positiveSlope_lipschitz hl hr
  have hz := LScalar.positiveSlope_nonpos hl hr (le_refl (0 : ℝ))
  have hordered (x y : ℝ) (hxy : x≤y) :
      |LScalar.phiFirst b x-LScalar.phiFirst b y|≤(768/b)*(y-x) := by
    by_cases hy : y≤0
    · rw [LScalar.phiFirst_eq_negative hl hr (hxy.trans hy),LScalar.phiFirst_eq_negative hl hr hy,
        abs_of_nonpos (sub_nonpos.mpr hxy)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hxy)]
    by_cases hx : x≤0
    · rw [LScalar.phiFirst_eq_negative hl hr hx,LScalar.phiFirst_eq_positive (by linarith : 0≤y)]
      have hp := hpos.dist_le_mul y 0
      simp only [Real.dist_eq,hz,sub_zero] at hp
      have hn : 0≤LScalar.positiveSlope b y := LScalar.positiveSlope_nonnegative b y
      rw [abs_of_nonpos (by linarith : x-LScalar.positiveSlope b y≤0)]
      rw [abs_of_nonneg hn,abs_of_nonneg (by linarith : 0≤y)] at hp
      change LScalar.positiveSlope b y≤(768/b)*y at hp
      nlinarith [mul_nonneg (sub_nonneg.mpr hK) (neg_nonneg.mpr hx)]
    · rw [LScalar.phiFirst_eq_positive (by linarith : 0≤x),
        LScalar.phiFirst_eq_positive (by linarith : 0≤y)]
      have hp := hpos.dist_le_mul x y
      simpa only [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hp
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rcases le_total x y with hxy|hyx
  · simpa only [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hordered x y hxy
  · have hh := hordered y x hyx
    simpa only [Real.dist_eq,abs_sub_comm y x,abs_sub_comm (LScalar.phiFirst b y) (LScalar.phiFirst b x),
      abs_of_nonneg (sub_nonneg.mpr hyx)] using hh

def ridgeGradient (i : Fin 3) (x : Vec 2) : Vec 2 :=
  LScalar.phiFirst (parameter i) (dot (slope i) x) • slope i

def residualGradient : Fin 4 → Vec 2 → Vec 2 :=
  ![ridgeGradient 0,ridgeGradient 1,ridgeGradient 2,fun _ => ![0,1]]

def branchGradient (i : Fin 4) (x : Vec 2) : Vec 2 := mu • x+residualGradient i x

theorem ridge_hasGradient (i : Fin 3) (x : Vec 2) :
    HasFDerivAt (fun z => LScalar.phi (parameter i) (dot (slope i) z))
      (gradientFunctional (ridgeGradient i x)) x := by
  rw [ridgeGradient,DEmbedding.gradientFunctional_smul]
  exact (LScalar.phi_hasDerivAt (parameter_bounds i).1.le (parameter_bounds i).2.le _).comp_hasFDerivAt x
    (DEmbedding.dot_hasFDerivAt (slope i) x)

theorem residual_hasGradient (i : Fin 4) (x : Vec 2) :
    HasFDerivAt (residualBranch i) (gradientFunctional (residualGradient i x)) x := by
  fin_cases i
  · exact ridge_hasGradient 0 x
  · exact ridge_hasGradient 1 x
  · exact ridge_hasGradient 2 x
  · convert (ContinuousLinearMap.proj (1 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasFDerivAt (x := x) using 1
    ext v
    simp [residualGradient,gradientFunctional_apply,dot,Fin.sum_univ_two]

theorem branch_hasGradient (i : Fin 4) (x : Vec 2) :
    HasFDerivAt (branch i) (gradientFunctional (branchGradient i x)) x := by
  convert (LQuadraticSeed.quadratic_hasGradient mu x).add (residual_hasGradient i x) using 1
  ext v
  simp [branchGradient,gradientFunctional_apply,ContinuousLinearMap.add_apply,
    dot,Pi.add_apply,add_mul,Finset.sum_add_distrib]

theorem ridge_contDiff (i : Fin 3) :
    ContDiff ℝ 1 (fun x => LScalar.phi (parameter i) (dot (slope i) x)) := by
  simpa only [gradientFunctional_apply,Function.comp_def] using
    (LScalar.phi_contDiff (parameter_bounds i).1.le (parameter_bounds i).2.le).comp
      (gradientFunctional (slope i)).contDiff

theorem residualBranch_contDiff (i : Fin 4) : ContDiff ℝ 1 (residualBranch i) := by
  fin_cases i
  · exact ridge_contDiff 0
  · exact ridge_contDiff 1
  · exact ridge_contDiff 2
  · exact (ContinuousLinearMap.proj (1 : Fin 2) : Vec 2 →L[ℝ] ℝ).contDiff

theorem branch_contDiff (i : Fin 4) : ContDiff ℝ 1 (branch i) := by
  have hq : ContDiff ℝ 1 (LQuadraticSeed.quadratic mu) := by
    unfold LQuadraticSeed.quadratic sqNorm
    simp only [Fin.sum_univ_two]
    fun_prop
  exact hq.add (residualBranch_contDiff i)

theorem residualGradient_zero (i : Fin 3) : residualGradient i.castSucc 0=0 := by
  have hh := LScalar.phiFirst_zero (parameter_bounds i).1.le (parameter_bounds i).2.le
  have he : residualGradient i.castSucc 0=ridgeGradient i 0 := by fin_cases i <;> rfl
  rw [he,ridgeGradient]
  simp only [dot,Pi.zero_apply,mul_zero,Finset.sum_const_zero] at *
  rw [hh,zero_smul]

theorem branchGradient_zero (i : Fin 3) : branchGradient i.castSucc 0=0 := by
  simp [branchGradient,residualGradient_zero]

theorem objective_not_differentiable_zero : ¬DifferentiableAt ℝ objective (0 : Vec 2) := by
  intro hd
  let g : Vec 2 := fun i => fderiv ℝ objective 0 (Pi.single i 1)
  have hg : HasFDerivAt objective (gradientFunctional g) 0 := by
    rw [show gradientFunctional g=fderiv ℝ objective 0 from gradientFunctional_coordinates _]
    exact hd.hasFDerivAt
  have h0 : (0 : Vec 2)=g := supporting_vector_eq_gradient (fun x => by
    simpa [dot,objective_zero] using objective_nonnegative x) hg
  have he : (![0,1] : Vec 2)=g := supporting_vector_eq_gradient (fun x => by
    have h3 := branch_le 3 x
    have hq : 0≤LQuadraticSeed.quadratic mu x :=
      mul_nonneg (div_nonneg mu_pos.le (by norm_num)) (sqNorm_nonneg x)
    change LQuadraticSeed.quadratic mu x+x 1≤objective x at h3
    simp only [objective_zero,dot,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      zero_mul,one_mul,zero_add,sub_zero]
    linarith) hg
  have hh := congrFun (he.trans h0.symm) 1
  norm_num at hh

end BfgsVerification.LEmbedding
