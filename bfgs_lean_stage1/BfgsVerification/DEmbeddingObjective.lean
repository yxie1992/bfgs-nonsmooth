import BfgsVerification.DScalarTarget
import BfgsVerification.AlgebraicSeedFiniteCycle
import BfgsVerification.ConvexGradientLimits
import BfgsVerification.Localization
import BfgsVerification.RadialHessian
import BfgsVerification.FrameNorms

open Set Filter Matrix
open scoped Topology BigOperators

namespace BfgsVerification.DEmbedding
open SeedCycle SeedOrbit
noncomputable section

def bStar : ℝ := 2*seedC-32*seedD

def parameter : Fin 3 → ℝ := ![2,2,bStar]

def branch : Fin 4 → Vec 2 → ℝ :=
  ![fun x => DScalar.phi 2 (dot g0 x),
    fun x => DScalar.phi 2 (dot g1 x),
    fun x => DScalar.phi bStar (dot (g2 seedC seedD) x),
    fun x => x 1]

def objective (x : Vec 2) : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => branch i x)

theorem bStar_bounds : 33 < bStar ∧ bStar < 34 := by
  obtain ⟨⟨hc0,hc1⟩,⟨hd0,hd1⟩⟩ := root_tight_box
  dsimp [bStar, seedC, seedD]
  constructor <;> linarith

theorem parameter_bounds (i : Fin 3) : 2 ≤ parameter i ∧ parameter i ≤ 34 := by
  fin_cases i <;> norm_num [parameter]
  exact ⟨by linarith [bStar_bounds.1], bStar_bounds.2.le⟩

theorem branch_old (i : Fin 3) (x : Vec 2) :
    branch i.castSucc x = DScalar.phi (parameter i) (dot (SeedOrbit.gradient seedC seedD i) x) := by
  fin_cases i <;> rfl

theorem branch_last (x : Vec 2) : branch 3 x=x 1 := rfl

theorem branch_le (i : Fin 4) (x : Vec 2) : branch i x ≤ objective x :=
  Finset.le_sup' (fun j => branch j x) (Finset.mem_univ i)

theorem objective_le {x : Vec 2} {a : ℝ} (h : ∀ i, branch i x ≤ a) : objective x ≤ a :=
  by
    apply Finset.sup'_le
    intro i _
    exact h i

theorem ridge_convex {n : ℕ} {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (a : Vec n) :
    ConvexOn ℝ univ (fun x => DScalar.phi b (dot a x)) := by
  simpa only [preimage_univ, ContinuousLinearMap.coe_coe, gradientFunctional_apply, Function.comp_def]
    using (DScalar.phi_convex hl hr).comp_linearMap (gradientFunctional a).toLinearMap

theorem ridge_contDiff {n : ℕ} {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (a : Vec n) :
    ContDiff ℝ 2 (fun x => DScalar.phi b (dot a x)) := by
  have h : ContDiff ℝ 2 (gradientFunctional a) := (gradientFunctional a).contDiff
  simpa only [gradientFunctional_apply, Function.comp_def] using (DScalar.phi_contDiff hl hr).comp h

theorem branch_convex (i : Fin 4) : ConvexOn ℝ univ (branch i) := by
  fin_cases i
  · exact ridge_convex (by norm_num) (by norm_num) g0
  · exact ridge_convex (by norm_num) (by norm_num) g1
  · exact ridge_convex (by linarith [bStar_bounds.1]) bStar_bounds.2.le (g2 seedC seedD)
  · exact (ContinuousLinearMap.proj (1 : Fin 2) : Vec 2 →L[ℝ] ℝ).toLinearMap.convexOn convex_univ

theorem branch_contDiff (i : Fin 4) : ContDiff ℝ 2 (branch i) := by
  fin_cases i
  · exact ridge_contDiff (by norm_num) (by norm_num) g0
  · exact ridge_contDiff (by norm_num) (by norm_num) g1
  · exact ridge_contDiff (by linarith [bStar_bounds.1]) bStar_bounds.2.le (g2 seedC seedD)
  · exact (ContinuousLinearMap.proj (1 : Fin 2) : Vec 2 →L[ℝ] ℝ).contDiff

theorem objective_convex : ConvexOn ℝ univ objective := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  apply objective_le
  intro i
  have hi := (branch_convex i).2 hx hy ha hb hab
  exact hi.trans (add_le_add (mul_le_mul_of_nonneg_left (branch_le i x) ha)
    (mul_le_mul_of_nonneg_left (branch_le i y) hb))

theorem objective_nonnegative (x : Vec 2) : 0 ≤ objective x :=
  (DScalar.phi_nonnegative (by norm_num : (2 : ℝ) ≤ 2) (by norm_num) (dot g0 x)).trans (branch_le 0 x)

theorem branch_zero (i : Fin 4) : branch i 0=0 := by
  fin_cases i
  · simpa [branch, dot] using DScalar.phi_zero (by norm_num : (2 : ℝ) ≤ 2) (by norm_num)
  · simpa [branch, dot] using DScalar.phi_zero (by norm_num : (2 : ℝ) ≤ 2) (by norm_num)
  · simpa [branch, dot] using DScalar.phi_zero (by linarith [bStar_bounds.1] : 2 ≤ bStar) bStar_bounds.2.le
  · rfl

theorem objective_zero : objective 0=0 := by
  exact le_antisymm (objective_le (fun i => (branch_zero i).le)) (objective_nonnegative 0)

theorem objective_unique_zero {x : Vec 2} (hx : objective x=0) : x=0 := by
  have h0 := branch_le 0 x
  have h1 := branch_le 1 x
  rw [hx] at h0 h1
  have he0 : DScalar.phi 2 (dot g0 x)=0 := le_antisymm h0 (DScalar.phi_nonnegative (by norm_num) (by norm_num) _)
  have he1 : DScalar.phi 2 (dot g1 x)=0 := le_antisymm h1 (DScalar.phi_nonnegative (by norm_num) (by norm_num) _)
  have hg0 := (DScalar.phi_zero_iff (by norm_num : (2 : ℝ) ≤ 2) (by norm_num) _).mp he0
  have hg1 := (DScalar.phi_zero_iff (by norm_num : (2 : ℝ) ≤ 2) (by norm_num) _).mp he1
  norm_num [dot, g0, g1, Fin.sum_univ_two] at hg0 hg1
  ext i
  fin_cases i
  · exact hg0
  · change x 1=0
    linarith

theorem objective_sublevels_compact (a : ℝ) : IsCompact {x | objective x ≤ a} := by
  apply Localization.sublevel_compact objective_convex (0 : Vec 2)
  · intro x
    rw [objective_zero]
    exact objective_nonnegative x
  · intro x hx
    rw [objective_zero] at hx
    exact objective_unique_zero hx

theorem objective_not_differentiable_zero : ¬ DifferentiableAt ℝ objective (0 : Vec 2) := by
  intro hd
  let g : Vec 2 := fun i => fderiv ℝ objective 0 (Pi.single i 1)
  have hg : HasFDerivAt objective (gradientFunctional g) 0 := by
    rw [show gradientFunctional g=fderiv ℝ objective 0 from gradientFunctional_coordinates _]
    exact hd.hasFDerivAt
  have h0 : (0 : Vec 2)=g := supporting_vector_eq_gradient (fun x => by
    simpa [dot, objective_zero] using objective_nonnegative x) hg
  have he : (![0,1] : Vec 2)=g := supporting_vector_eq_gradient (fun x => by
    simpa [objective_zero, dot, Fin.sum_univ_two, branch_last] using branch_le 3 x) hg
  have h := congrFun (he.trans h0.symm) 1
  norm_num at h


def ridge {n : ℕ} (b : ℝ) (a : Vec n) (x : Vec n) : ℝ := DScalar.phi b (dot a x)

def ridgeGradient {n : ℕ} (b : ℝ) (a x : Vec n) : Vec n := DScalar.phiFirst b (dot a x) • a

theorem gradientFunctional_smul {n : ℕ} (t : ℝ) (a : Vec n) :
    gradientFunctional (t • a)=t • gradientFunctional a := by
  ext x
  simp [gradientFunctional_apply, ContinuousLinearMap.smul_apply, dot, Finset.mul_sum, mul_assoc]

theorem dot_hasFDerivAt {n : ℕ} (a x : Vec n) : HasFDerivAt (dot a) (gradientFunctional a) x := by
  convert (gradientFunctional a).hasFDerivAt (x := x) using 1
  exact funext (fun y => (gradientFunctional_apply a y).symm)

theorem ridge_hasFDerivAt {n : ℕ} {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (a x : Vec n) :
    HasFDerivAt (ridge b a) (DScalar.phiFirst b (dot a x) • gradientFunctional a) x := by
  exact (DScalar.phi_hasDerivAt hl hr (dot a x)).comp_hasFDerivAt x (dot_hasFDerivAt a x)

theorem ridge_hasGradient {n : ℕ} {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (a x : Vec n) :
    HasFDerivAt (ridge b a) (gradientFunctional (ridgeGradient b a x)) x := by
  rw [ridgeGradient, gradientFunctional_smul]
  exact ridge_hasFDerivAt hl hr a x

theorem ridge_second_hasFDerivAt {n : ℕ} {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (a x : Vec n) :
    HasFDerivAt (fderiv ℝ (ridge b a))
      ((DScalar.phiSecond b (dot a x) • gradientFunctional a).smulRight (gradientFunctional a)) x := by
  have h : fderiv ℝ (ridge b a) = fun z => DScalar.phiFirst b (dot a z) • gradientFunctional a :=
    funext (fun z => (ridge_hasFDerivAt hl hr a z).fderiv)
  rw [h]
  exact ((DScalar.phiFirst_hasDerivAt hl (dot a x)).comp_hasFDerivAt x (dot_hasFDerivAt a x)).smul_const
    (gradientFunctional a)

theorem ridge_hessian {n : ℕ} {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (a x : Vec n) :
    RadialHessian.matrix (ridge b a) x = DScalar.phiSecond b (dot a x) • outer a a := by
  rw [RadialHessian.matrix, (ridge_second_hasFDerivAt hl hr a x).fderiv]
  ext i j
  have hs (k : Fin n) : dot a (Pi.single k 1)=a k := by
    change dotProduct a (Pi.single k 1)=a k
    simp
  simp only [RadialHessian.bilinearMatrix, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, gradientFunctional_apply, smul_eq_mul, hs, Matrix.smul_apply, outer]
  ring


theorem rankOne_quadratic {n : ℕ} (t : ℝ) (a v : Vec n) :
    dot v ((t • outer a a).mulVec v)=t*(dot a v)^2 := by
  rw [Matrix.smul_mulVec_assoc, outer_mulVec, smul_smul]
  change dotProduct v ((t*dot a v) • a)=_
  rw [dotProduct_smul, dotProduct_comm v a]
  change (t*dot a v)*dot a v=t*(dot a v)^2
  ring

theorem rankOne_posSemidef {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (a : Vec n) :
    (t • outer a a).PosSemidef := by
  constructor
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_smul, outer_transpose]
  · intro v
    change 0 ≤ dot v ((t • outer a a).mulVec v)
    rw [rankOne_quadratic]
    exact mul_nonneg ht (sq_nonneg _)

theorem rankOne_upper_bound {n : ℕ} {t K : ℝ} (ht : 0 ≤ t) (a : Vec n)
    (hK : t*sqNorm a ≤ K) : (K • (1 : Mat n)-t • outer a a).PosSemidef := by
  constructor
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_sub, Matrix.transpose_smul, outer_transpose]
  · intro v
    change 0 ≤ dot v ((K • (1 : Mat n)-t • outer a a).mulVec v)
    rw [Matrix.sub_mulVec]
    change 0 ≤ dotProduct v ((K • (1 : Mat n)).mulVec v-(t • outer a a).mulVec v)
    rw [dotProduct_sub]
    change 0 ≤ dot v ((K • (1 : Mat n)).mulVec v)-dot v ((t • outer a a).mulVec v)
    rw [rankOne_quadratic, Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
    change 0 ≤ dotProduct v (K • v)-t*(dot a v)^2
    rw [dotProduct_smul]
    have hv : dotProduct v v=sqNorm v := by simp [dotProduct, sqNorm, pow_two]
    rw [hv]
    simp only [smul_eq_mul]
    have hc := mul_le_mul_of_nonneg_left (dot_sq_le_sqNorm_mul_sqNorm a v) ht
    have hk := mul_le_mul_of_nonneg_right hK (sqNorm_nonneg v)
    nlinarith

theorem rankOne_euclideanOpNorm_le {n : ℕ} (t : ℝ) (a : Vec n) :
    FrameNorms.euclideanOpNorm (t • outer a a) ≤ |t| *sqNorm a := by
  have hsq : FrameNorms.euclideanOpNorm (t • outer a a)^2 ≤ (|t| *sqNorm a)^2 := by
    apply (FrameNorms.operatorSqBound_iff_opNorm_sq _ _ (sq_nonneg _)).mp
    intro v
    rw [Matrix.transpose_smul, outer_transpose, Matrix.smul_mulVec_assoc, outer_mulVec, smul_smul,
      RadialPower.sqNorm_smul]
    have hc := mul_le_mul_of_nonneg_left (dot_sq_le_sqNorm_mul_sqNorm a v)
      (mul_nonneg (sq_nonneg t) (sqNorm_nonneg a))
    simp only [mul_pow, sq_abs]
    nlinarith
  have hn : 0 ≤ FrameNorms.euclideanOpNorm (t • outer a a) := norm_nonneg _
  have hr : 0 ≤ |t| *sqNorm a := mul_nonneg (abs_nonneg _) (sqNorm_nonneg a)
  exact (sq_le_sq₀ hn hr).mp hsq


theorem gradient_sqNorm_lt_two (i : Fin 3) : sqNorm (SeedOrbit.gradient seedC seedD i) < 2 := by
  fin_cases i
  · norm_num [SeedOrbit.gradient, g0, sqNorm, Fin.sum_univ_two]
  · norm_num [SeedOrbit.gradient, g1, sqNorm, Fin.sum_univ_two]
  · obtain ⟨⟨hc0,hc1⟩,⟨hd0,hd1⟩⟩ := root_tight_box
    have hc : -1/2 < seedC ∧ seedC < 1/2 := ⟨by linarith, by linarith⟩
    have hd : -6/5 < seedD ∧ seedD < 0 := ⟨by linarith, by linarith⟩
    norm_num only [SeedOrbit.gradient, g2, sqNorm, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    change seedC^2+seedD^2 < 2
    nlinarith [sq_nonneg (seedC+1/2), mul_nonneg (sub_nonneg.mpr hc.2.le) (show 0 ≤ seedC+1/2 by linarith),
      mul_nonneg (show 0 ≤ seedD+6/5 by linarith) (show 0 ≤ -seedD by linarith)]

theorem parameter_curvature_product_le (i : Fin 3) :
    max 6 (102/parameter i)*sqNorm (SeedOrbit.gradient seedC seedD i) ≤ 64 := by
  fin_cases i
  · norm_num [parameter, SeedOrbit.gradient, g0, sqNorm, Fin.sum_univ_two]
  · norm_num [parameter, SeedOrbit.gradient, g1, sqNorm, Fin.sum_univ_two]
  · change max 6 (102/bStar)*sqNorm (g2 seedC seedD) ≤ 64
    have hb : 0 < bStar := by linarith [bStar_bounds.1]
    have hq : 102/bStar ≤ 6 := (div_le_iff₀ hb).mpr (by linarith [bStar_bounds.1])
    rw [max_eq_left hq]
    have hg : sqNorm (g2 seedC seedD) < 2 := gradient_sqNorm_lt_two 2
    linarith

theorem branch_old_hasGradient (i : Fin 3) (x : Vec 2) :
    HasFDerivAt (branch i.castSucc)
      (gradientFunctional (ridgeGradient (parameter i) (SeedOrbit.gradient seedC seedD i) x)) x := by
  rw [show branch i.castSucc=ridge (parameter i) (SeedOrbit.gradient seedC seedD i) from funext (branch_old i)]
  exact ridge_hasGradient (parameter_bounds i).1 (parameter_bounds i).2 _ _

theorem branch_last_hasGradient (x : Vec 2) :
    HasFDerivAt (branch 3) (gradientFunctional (![0,1] : Vec 2)) x := by
  have h : gradientFunctional (![0,1] : Vec 2)=ContinuousLinearMap.proj (1 : Fin 2) := by
    ext z
    norm_num [gradientFunctional_apply, dot, Fin.sum_univ_two]
  rw [h]
  exact (ContinuousLinearMap.proj (1 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasFDerivAt

theorem branch_old_hessian (i : Fin 3) (x : Vec 2) :
    RadialHessian.matrix (branch i.castSucc) x =
      DScalar.phiSecond (parameter i) (dot (SeedOrbit.gradient seedC seedD i) x) •
        outer (SeedOrbit.gradient seedC seedD i) (SeedOrbit.gradient seedC seedD i) := by
  rw [show branch i.castSucc=ridge (parameter i) (SeedOrbit.gradient seedC seedD i) from funext (branch_old i)]
  exact ridge_hessian (parameter_bounds i).1 (parameter_bounds i).2 _ _

theorem branch_last_hessian (x : Vec 2) : RadialHessian.matrix (branch 3) x=0 := by
  have h : fderiv ℝ (branch 3)=fun _ => gradientFunctional (![0,1] : Vec 2) :=
    funext (fun z => (branch_last_hasGradient z).fderiv)
  rw [RadialHessian.matrix, h, fderiv_const]
  rfl

theorem branch_old_hessian_bounds (i : Fin 3) (x : Vec 2) :
    (RadialHessian.matrix (branch i.castSucc) x).PosSemidef ∧
      ((64 : ℝ) • (1 : Mat 2)-RadialHessian.matrix (branch i.castSucc) x).PosSemidef := by
  rw [branch_old_hessian]
  obtain ⟨h0,h1⟩ := DScalar.phiSecond_bounds (parameter_bounds i).1 (parameter_bounds i).2
    (dot (SeedOrbit.gradient seedC seedD i) x)
  exact ⟨rankOne_posSemidef h0 _, rankOne_upper_bound h0 _
    ((mul_le_mul_of_nonneg_right h1 (sqNorm_nonneg _)).trans (parameter_curvature_product_le i))⟩

theorem branch_hessian_bounds (i : Fin 4) (x : Vec 2) :
    (RadialHessian.matrix (branch i) x).PosSemidef ∧
      ((64 : ℝ) • (1 : Mat 2)-RadialHessian.matrix (branch i) x).PosSemidef := by
  fin_cases i
  · exact branch_old_hessian_bounds 0 x
  · exact branch_old_hessian_bounds 1 x
  · exact branch_old_hessian_bounds 2 x
  · change (RadialHessian.matrix (branch 3) x).PosSemidef ∧ ((64 : ℝ) • (1 : Mat 2)-RadialHessian.matrix (branch 3) x).PosSemidef
    rw [branch_last_hessian, sub_zero]
    exact ⟨Matrix.PosSemidef.zero, by
      have h := rankOne_upper_bound (t := (0 : ℝ)) (K := 64) (by norm_num) (0 : Vec 2) (by simp)
      simpa only [zero_smul, sub_zero] using h⟩

theorem branch_hessian_opNorm_bound (i : Fin 4) (x : Vec 2) :
    FrameNorms.euclideanOpNorm (RadialHessian.matrix (branch i) x) ≤ 64 := by
  have h (j : Fin 3) : FrameNorms.euclideanOpNorm (RadialHessian.matrix (branch j.castSucc) x) ≤ 64 := by
    rw [branch_old_hessian]
    have ht := (DScalar.phiSecond_bounds (parameter_bounds j).1 (parameter_bounds j).2
      (dot (SeedOrbit.gradient seedC seedD j) x))
    have hn := rankOne_euclideanOpNorm_le (DScalar.phiSecond (parameter j) (dot (SeedOrbit.gradient seedC seedD j) x))
      (SeedOrbit.gradient seedC seedD j)
    rw [abs_of_nonneg ht.1] at hn
    exact hn.trans ((mul_le_mul_of_nonneg_right ht.2 (sqNorm_nonneg _)).trans (parameter_curvature_product_le j))
  fin_cases i
  · exact h 0
  · exact h 1
  · exact h 2
  · change FrameNorms.euclideanOpNorm (RadialHessian.matrix (branch 3) x) ≤ 64
    rw [branch_last_hessian]
    norm_num [FrameNorms.euclideanOpNorm]

theorem phiSecond_lipschitz_constant_le {b : ℝ} (hl : 2 ≤ b) :
    max 6 (139264/(5*b^2)) ≤ 139264/20 := by
  have hb : 0 < 5*b^2 := by positivity
  apply max_le (by norm_num)
  apply (div_le_iff₀ hb).mpr
  nlinarith [sq_nonneg (b-2)]

theorem branch_old_hessian_lipschitz (i : Fin 3) (x y : Vec 2) :
    FrameNorms.euclideanOpNorm
      (RadialHessian.matrix (branch i.castSucc) x-RadialHessian.matrix (branch i.castSucc) y)
      ≤ 60000*‖euclideanVector (x-y)‖ := by
  let a := SeedOrbit.gradient seedC seedD i
  let b := parameter i
  have hb := parameter_bounds i
  have ha : sqNorm a ≤ 4 := by linarith [gradient_sqNorm_lt_two i]
  have hd : |dot a x-dot a y| ≤ 2*‖euclideanVector (x-y)‖ := by
    have hsq : sqNorm (x-y) ≤ ‖euclideanVector (x-y)‖^2 := by
      rw [FrameNorms.euclidean_norm_sq]
      rfl
    have h := abs_dot_le_of_sqNorm_le a (x-y) 2 ‖euclideanVector (x-y)‖
      (by norm_num) (norm_nonneg _) (by norm_num; exact ha) hsq
    simpa only [dot, dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] using h
  have hφ : |DScalar.phiSecond b (dot a x)-DScalar.phiSecond b (dot a y)|
      ≤ (139264/20)*|dot a x-dot a y| := by
    have h := (DScalar.phiSecond_lipschitz hb.1 hb.2).norm_sub_le (dot a x) (dot a y)
    simp only [Real.norm_eq_abs, NNReal.coe_mk] at h
    exact h.trans (mul_le_mul_of_nonneg_right (phiSecond_lipschitz_constant_le hb.1) (abs_nonneg _))
  rw [branch_old_hessian, branch_old_hessian, ← sub_smul]
  calc
    FrameNorms.euclideanOpNorm
      ((DScalar.phiSecond b (dot a x)-DScalar.phiSecond b (dot a y)) • outer a a)
        ≤ |DScalar.phiSecond b (dot a x)-DScalar.phiSecond b (dot a y)| * sqNorm a :=
      rankOne_euclideanOpNorm_le _ _
    _ ≤ ((139264/20)*|dot a x-dot a y|)*4 :=
      mul_le_mul hφ ha (sqNorm_nonneg _) (by positivity)
    _ ≤ ((139264/20)*(2*‖euclideanVector (x-y)‖))*4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) (by norm_num)
    _ ≤ 60000*‖euclideanVector (x-y)‖ := by nlinarith [norm_nonneg (euclideanVector (x-y))]

theorem branch_hessian_lipschitz (i : Fin 4) (x y : Vec 2) :
    FrameNorms.euclideanOpNorm
      (RadialHessian.matrix (branch i) x-RadialHessian.matrix (branch i) y)
      ≤ 60000*‖euclideanVector (x-y)‖ := by
  fin_cases i
  · exact branch_old_hessian_lipschitz 0 x y
  · exact branch_old_hessian_lipschitz 1 x y
  · exact branch_old_hessian_lipschitz 2 x y
  · change FrameNorms.euclideanOpNorm
      (RadialHessian.matrix (branch 3) x-RadialHessian.matrix (branch 3) y) ≤ _
    rw [branch_last_hessian, branch_last_hessian, sub_self]
    simp [FrameNorms.euclideanOpNorm]

theorem branch_old_hessian_parameter_bound (i : Fin 3) (x : Vec 2) :
    FrameNorms.euclideanOpNorm (RadialHessian.matrix (branch i.castSucc) x) ≤
      max 6 (102/parameter i)*sqNorm (SeedOrbit.gradient seedC seedD i) := by
  rw [branch_old_hessian]
  obtain ⟨h0,h1⟩ := DScalar.phiSecond_bounds (parameter_bounds i).1 (parameter_bounds i).2
    (dot (SeedOrbit.gradient seedC seedD i) x)
  have h := rankOne_euclideanOpNorm_le (DScalar.phiSecond (parameter i) (dot (SeedOrbit.gradient seedC seedD i) x))
    (SeedOrbit.gradient seedC seedD i)
  rw [abs_of_nonneg h0] at h
  exact h.trans (mul_le_mul_of_nonneg_right h1 (sqNorm_nonneg _))

theorem branch_individual_hessian_bounds (x : Vec 2) :
    FrameNorms.euclideanOpNorm (RadialHessian.matrix (branch 0) x) ≤ 51 ∧
    FrameNorms.euclideanOpNorm (RadialHessian.matrix (branch 1) x) ≤ 51*(65/64) ∧
    FrameNorms.euclideanOpNorm (RadialHessian.matrix (branch 1) x) < 52 ∧
    FrameNorms.euclideanOpNorm (RadialHessian.matrix (branch 2) x) < 12 ∧
    RadialHessian.matrix (branch 3) x=0 := by
  have h0 := branch_old_hessian_parameter_bound 0 x
  have h1 := branch_old_hessian_parameter_bound 1 x
  have h2 := branch_old_hessian_parameter_bound 2 x
  norm_num [parameter, SeedOrbit.gradient, g0, g1, sqNorm, Fin.sum_univ_two] at h0 h1
  have hb : 0 < bStar := by linarith [bStar_bounds.1]
  have hq : 102/bStar ≤ 6 := (div_le_iff₀ hb).mpr (by linarith [bStar_bounds.1])
  change FrameNorms.euclideanOpNorm (RadialHessian.matrix (branch 2) x) ≤
    max 6 (102/bStar)*sqNorm (g2 seedC seedD) at h2
  rw [max_eq_left hq] at h2
  have hg : sqNorm (g2 seedC seedD)<2 := gradient_sqNorm_lt_two 2
  exact ⟨h0, by norm_num; exact h1, by norm_num at h1; linarith, by linarith, branch_last_hessian x⟩

theorem objective_eq_max (x : Vec 2) :
    objective x=max (max (branch 0 x) (branch 1 x)) (max (branch 2 x) (branch 3 x)) := by
  apply le_antisymm
  · apply objective_le
    intro i
    fin_cases i
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact max_le (max_le (branch_le 0 x) (branch_le 1 x)) (max_le (branch_le 2 x) (branch_le 3 x))

theorem phiFirst_zero {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) : DScalar.phiFirst b 0=0 := by
  rw [DScalar.phiFirst, DScalar.positiveSlope_nonpos hl hr (le_refl 0),
    DScalarNegative.first_eq_zero (le_refl 0), add_zero]

theorem branch_old_ray_hasDerivAt_zero (i : Fin 3) (h : Vec 2) :
    HasDerivAt (fun t : ℝ => branch i.castSucc (t • h)) 0 0 := by
  have hd := (branch_old_hasGradient i (0 : Vec 2)).comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).smul_const h) (by simp)
  simpa [Function.comp_def, ridgeGradient, dot, phiFirst_zero (parameter_bounds i).1 (parameter_bounds i).2]
    using hd

theorem objective_directional_derivative_zero (h : Vec 2) :
    Tendsto (fun t : ℝ => (objective (t • h)-objective 0)/t)
      (𝓝[>] 0) (𝓝 (max 0 (h 1))) := by
  have hold (i : Fin 3) : Tendsto (fun t : ℝ => branch i.castSucc (t • h)/t)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_add, zero_smul, branch_zero, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
      using (branch_old_ray_hasDerivAt_zero i h).tendsto_slope_zero_right
  have hlast : Tendsto (fun t : ℝ => branch 3 (t • h)/t) (𝓝[>] 0) (𝓝 (h 1)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ne_of_gt ht
    simp [branch_last, ht']
  have hm := ((hold 0).max (hold 1)).max ((hold 2).max hlast)
  simp only [max_self] at hm
  rw [max_eq_right (le_max_left (0 : ℝ) (h 1))] at hm
  apply hm.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [objective_zero, sub_zero, objective_eq_max]
  change max (max (branch 0 (t • h)/t) (branch 1 (t • h)/t))
    (max (branch 2 (t • h)/t) (branch 3 (t • h)/t)) = _
  rw [max_div_div_right ht.le, max_div_div_right ht.le, max_div_div_right ht.le]

theorem objective_literal (x : Vec 2) :
    objective x=max
      (max (DScalar.phi 2 (x 0)) (DScalar.phi 2 (-x 0-x 1/8)))
      (max (DScalar.phi bStar (seedC*x 0+seedD*x 1)) (x 1)) := by
  rw [objective_eq_max]
  norm_num only [branch, dot, g0, g1, g2, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
    Matrix.vecTail, one_mul, zero_mul, add_zero, neg_one_mul]
  congr 3
  congr 1
  ring

theorem objective_unique_minimum :
    objective 0=0 ∧ (∀ x, 0 ≤ objective x) ∧ (∀ x, objective x=0 ↔ x=0) := by
  exact ⟨objective_zero, objective_nonnegative, fun x => ⟨objective_unique_zero, fun hx => hx ▸ objective_zero⟩⟩

/-- The actual scalar construction gives the four concrete branches in Module D,
with the Hessian interpreted as the derivative of the actual first derivative. -/
theorem objective_function_contract :
    (∀ x, objective x=Finset.univ.sup' Finset.univ_nonempty (fun i => branch i x)) ∧
    (∀ i, ConvexOn ℝ univ (branch i) ∧ ContDiff ℝ 2 (branch i)) ∧
    ConvexOn ℝ univ objective ∧
    objective 0=0 ∧ (∀ x, 0 ≤ objective x) ∧ (∀ x, objective x=0 ↔ x=0) ∧
    (∀ a, IsCompact {x | objective x ≤ a}) ∧
    ¬ DifferentiableAt ℝ objective (0 : Vec 2) ∧
    (∀ h, Tendsto (fun t : ℝ => (objective (t • h)-objective 0)/t)
      (𝓝[>] 0) (𝓝 (max 0 (h 1)))) ∧
    (∀ i x, (RadialHessian.matrix (branch i) x).PosSemidef ∧
      ((64 : ℝ) • (1 : Mat 2)-RadialHessian.matrix (branch i) x).PosSemidef) ∧
    (∀ i x y, FrameNorms.euclideanOpNorm
      (RadialHessian.matrix (branch i) x-RadialHessian.matrix (branch i) y)
      ≤ 60000*‖euclideanVector (x-y)‖) := by
  exact ⟨fun _ => rfl, fun i => ⟨branch_convex i, branch_contDiff i⟩,
    objective_convex, objective_zero, objective_nonnegative, objective_unique_minimum.2.2,
    objective_sublevels_compact, objective_not_differentiable_zero,
    objective_directional_derivative_zero, branch_hessian_bounds, branch_hessian_lipschitz⟩

end
end BfgsVerification.DEmbedding
