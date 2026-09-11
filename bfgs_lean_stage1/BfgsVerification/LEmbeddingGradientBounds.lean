import BfgsVerification.LEmbeddingRegularity
import BfgsVerification.FiniteMaxHessianTargets

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.LEmbedding

theorem slope_third_sqNorm_bound : sqNorm (slope 2)<57/50 := by
  obtain ⟨⟨hc0,hc1⟩,⟨hd0,hd1⟩⟩ := SeedOrbit.root_tight_box
  rw [slope_third]
  simp only [sqNorm,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  change (SeedOrbit.seedC-1/2048)^2+(SeedOrbit.seedD+1/128)^2<57/50
  have hcx : -(8/25 : ℝ)<SeedOrbit.seedC-1/2048 ∧ SeedOrbit.seedC-1/2048<8/25 := by
    constructor <;> linarith
  have hdx : -(509/500 : ℝ)<SeedOrbit.seedD+1/128 ∧ SeedOrbit.seedD+1/128<509/500 := by
    constructor <;> linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hcx.2.le) (show 0≤8/25+(SeedOrbit.seedC-1/2048) by linarith),
    mul_nonneg (sub_nonneg.mpr hdx.2.le) (show 0≤509/500+(SeedOrbit.seedD+1/128) by linarith)]

theorem parameter_third_gt : 33<parameter 2 := by
  rw [parameter_third]
  obtain ⟨⟨hc0,hc1⟩,⟨hd0,hd1⟩⟩ := SeedOrbit.root_tight_box
  linarith

def gradientBound (i : Fin 3) : ℝ := mu+(768/parameter i)*sqNorm (slope i)

theorem gradientBound_pos (i : Fin 3) : 0<gradientBound i := by
  have hp : 0<parameter i := by linarith [(parameter_bounds i).1]
  exact add_pos_of_pos_of_nonneg mu_pos (mul_nonneg (by positivity) (sqNorm_nonneg _))

theorem gradientBound_source (i : Fin 3) : gradientBound i < ![439,446,27] i := by
  fin_cases i
  · norm_num [gradientBound,mu,parameter_first,slope_first,sqNorm,Fin.sum_univ_two]
  · norm_num [gradientBound,mu,parameter_second,slope_second,sqNorm,Fin.sum_univ_two]
  · change mu+(768/parameter 2)*sqNorm (slope 2)<27
    have hb : 0<parameter 2 := by linarith [parameter_third_gt]
    have hk : 768/parameter 2≤768/33 := (div_le_iff₀ hb).mpr (by linarith [parameter_third_gt])
    have hmul := mul_le_mul_of_nonneg_right hk (sqNorm_nonneg (slope 2))
    dsimp [mu]
    nlinarith [slope_third_sqNorm_bound]

theorem gradientBound_le_512 (i : Fin 3) : gradientBound i≤512 := by
  have h := gradientBound_source i
  fin_cases i <;> norm_num at h ⊢ <;> linarith

theorem ridge_gradient_bound (i : Fin 3) (x y : Vec 2) :
    sqNorm (ridgeGradient i x-ridgeGradient i y) ≤
      ((768/parameter i)*sqNorm (slope i))^2*sqNorm (x-y) := by
  let c : ℝ := LScalar.phiFirst (parameter i) (dot (slope i) x)-LScalar.phiFirst (parameter i) (dot (slope i) y)
  have he : ridgeGradient i x-ridgeGradient i y=c • slope i := by
    dsimp [ridgeGradient,c]
    exact (sub_smul _ _ _).symm
  have hl := (scalar_derivative_lipschitz (parameter_bounds i).1.le (parameter_bounds i).2.le).dist_le_mul
    (dot (slope i) x) (dot (slope i) y)
  have hd : dot (slope i) x-dot (slope i) y=dot (slope i) (x-y) := by
    exact (dotProduct_sub _ _ _).symm
  simp only [Real.dist_eq,hd] at hl
  change |c|≤(768/parameter i)*|dot (slope i) (x-y)| at hl
  have hp : 0<parameter i := by linarith [(parameter_bounds i).1]
  have hs := (sq_le_sq₀ (abs_nonneg c) (by positivity : 0≤(768/parameter i)*|dot (slope i) (x-y)|)).mpr hl
  simp only [mul_pow,sq_abs] at hs
  rw [he,CertificateGeometry.sqNorm_smul]
  have h1 := mul_le_mul_of_nonneg_right hs (sqNorm_nonneg (slope i))
  have h2 := mul_le_mul_of_nonneg_left (dot_sq_le_sqNorm_mul_sqNorm (slope i) (x-y))
    (mul_nonneg (sq_nonneg (768/parameter i)) (sqNorm_nonneg (slope i)))
  nlinarith

theorem add_scalar_sqNorm_bound {n : ℕ} {v w : Vec n} {a K : ℝ} (ha : 0≤a) (hK : 0≤K)
    (hw : sqNorm w≤K^2*sqNorm v) : sqNorm (a • v+w)≤(a+K)^2*sqNorm v := by
  have hn : ‖euclideanVector w‖≤K*‖euclideanVector v‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
    simpa only [mul_pow,FrameNorms.euclidean_norm_sq] using hw
  have he : euclideanVector (a • v+w)=a • euclideanVector v+euclideanVector w := by rfl
  have hu : ‖euclideanVector (a • v+w)‖≤(a+K)*‖euclideanVector v‖ := by
    rw [he]
    have hh := norm_add_le (a • euclideanVector v) (euclideanVector w)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha] at hh
    nlinarith
  have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (add_nonneg ha hK) (norm_nonneg _))).mpr hu
  simpa only [mul_pow,FrameNorms.euclidean_norm_sq] using hh

theorem branch_old_gradient_bound (i : Fin 3) (x y : Vec 2) :
    sqNorm (branchGradient i.castSucc x-branchGradient i.castSucc y)≤
      (gradientBound i)^2*sqNorm (x-y) := by
  have he : branchGradient i.castSucc x-branchGradient i.castSucc y=
      mu • (x-y)+(ridgeGradient i x-ridgeGradient i y) := by
    have hi (z : Vec 2) : residualGradient i.castSucc z=ridgeGradient i z := by fin_cases i <;> rfl
    simp only [branchGradient,hi,smul_sub]
    abel
  rw [he]
  have hp : 0<parameter i := by linarith [(parameter_bounds i).1]
  exact add_scalar_sqNorm_bound mu_pos.le (mul_nonneg (by positivity) (sqNorm_nonneg _))
    (ridge_gradient_bound i x y)

theorem branch_gradient_bound (i : Fin 4) (x y : Vec 2) :
    sqNorm (branchGradient i x-branchGradient i y)≤512^2*sqNorm (x-y) := by
  by_cases hi : i=3
  · subst i
    have he : branchGradient 3 x-branchGradient 3 y=mu • (x-y) := by
      change (mu • x+![0,1])-(mu • y+![0,1])=mu • (x-y)
      rw [smul_sub]
      abel
    rw [he,CertificateGeometry.sqNorm_smul]
    have hs := sqNorm_nonneg (x-y)
    dsimp [mu]
    nlinarith
  · obtain ⟨j,hj⟩ : ∃j : Fin 3,j.castSucc=i := by
      have hh : i.val≠3 := by
        intro he
        apply hi
        exact Fin.ext he
      refine ⟨⟨i.val,by have := i.isLt; omega⟩,?_⟩
      rfl
    rw [←hj]
    have hh := branch_old_gradient_bound j x y
    have hs := mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (gradientBound_pos j).le (by norm_num : (0 : ℝ)≤512)).mpr (gradientBound_le_512 j))
      (sqNorm_nonneg (x-y))
    exact hh.trans hs

end BfgsVerification.LEmbedding
