import BfgsVerification.NormalSpikeVariableGeometry
import BfgsVerification.RadialHessian

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.NormalSpike
open FixedNormal

def variableQuadraticBranch {n : ℕ} (a c : Vec n) (σ : ℝ) (x : Vec n) : ℝ :=
  quadratic x+σ*(1+dot c x)*dot a x

theorem variableQuadraticBranch_contDiff {n : ℕ} (a c : Vec n) (σ : ℝ) :
    ContDiff ℝ 3 (variableQuadraticBranch a c σ) := by
  have hl (b : Vec n) : ContDiff ℝ 3 (dot b) := by
    convert (gradientFunctional b).contDiff using 1
    exact funext (fun y => (gradientFunctional_apply b y).symm)
  exact quadratic_contDiff.add ((contDiff_const.mul (contDiff_const.add (hl c))).mul (hl a))

theorem sqNorm_add_smul {n : ℕ} (x v : Vec n) (t : ℝ) :
    sqNorm (x+t • v) = sqNorm x+2*t*dot x v+t^2*sqNorm v := by
  have hh := sqNorm_sub_smul x v (-t)
  have hvx : dot v x = dot x v := by exact dotProduct_comm _ _
  simpa only [neg_smul, sub_neg_eq_add, neg_mul, mul_neg, neg_neg, neg_sq, hvx] using hh

theorem variableQuadraticBranch_ray_polynomial {n : ℕ} (a c x v : Vec n) (σ t : ℝ) :
    variableQuadraticBranch a c σ (RadialHessian.ray x v t) =
      variableQuadraticBranch a c σ x +
        t*(dot x v+σ*(dot c v*dot a x+(1+dot c x)*dot a v)) +
        (t^2/2)*(sqNorm v+2*σ*dot c v*dot a v) := by
  simp only [variableQuadraticBranch, RadialHessian.ray, quadratic, sqNorm_add_smul, dot_add_smul]
  ring

theorem quadratic_polynomial_hasSecondDerivAt (A B C : ℝ) :
    HasDerivAt (deriv (fun t : ℝ => A+t*B+(t^2/2)*C)) C 0 := by
  have hh (t : ℝ) : HasDerivAt (fun t : ℝ => A+t*B+(t^2/2)*C) (B+t*C) t := by
    convert ((hasDerivAt_const t A).add ((hasDerivAt_id t).mul_const B)).add
      ((((hasDerivAt_id t).pow 2).div_const 2).mul_const C) using 1 <;> (try simp only [id_eq]) <;> ring
  rw [funext (fun t => (hh t).deriv)]
  convert (hasDerivAt_const (0 : ℝ) B).add ((hasDerivAt_id (0 : ℝ)).mul_const C) using 1 <;> (try simp only [id_eq]) <;> ring

theorem variableQuadraticBranch_hessian_quadratic {n : ℕ} (a c x v : Vec n) (σ : ℝ) :
    (fderiv ℝ (fderiv ℝ (variableQuadraticBranch a c σ)) x) v v =
      sqNorm v+2*σ*dot c v*dot a v := by
  have he : (fun t : ℝ => variableQuadraticBranch a c σ (RadialHessian.ray x v t)) =
      (fun t : ℝ => variableQuadraticBranch a c σ x+
        t*(dot x v+σ*(dot c v*dot a x+(1+dot c x)*dot a v))+
        (t^2/2)*(sqNorm v+2*σ*dot c v*dot a v)) := by
    ext t
    exact variableQuadraticBranch_ray_polynomial a c x v σ t
  have hd := RadialHessian.ray_second_derivative (x := x)
    ((variableQuadraticBranch_contDiff a c σ).contDiffAt.of_le (by decide)) v
  rw [he, (quadratic_polynomial_hasSecondDerivAt _ _ _).deriv] at hd
  exact hd.symm

theorem variableQuadraticBranch_hessian_bilinear {n : ℕ} (a c x v w : Vec n) (σ : ℝ) :
    (fderiv ℝ (fderiv ℝ (variableQuadraticBranch a c σ)) x) v w =
      dot v w+σ*(dot c v*dot a w+dot c w*dot a v) := by
  let B := fderiv ℝ (fderiv ℝ (variableQuadraticBranch a c σ)) x
  have hs : B v w = B w v :=
    (variableQuadraticBranch_contDiff a c σ).contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; decide) v w
  have hsum := variableQuadraticBranch_hessian_quadratic a c x (v+w) σ
  have hv := variableQuadraticBranch_hessian_quadratic a c x v σ
  have hw := variableQuadraticBranch_hessian_quadratic a c x w σ
  have hq : sqNorm (v+w) = sqNorm v+2*dot v w+sqNorm w := by
    simpa only [one_smul, one_pow, mul_one, one_mul] using sqNorm_add_smul v w 1
  have hd (b : Vec n) : dot b (v+w) = dot b v+dot b w := by exact dotProduct_add _ _ _
  simp only [map_add, ContinuousLinearMap.add_apply, hq, hd c, hd a] at hsum
  change B v v+B w v+(B v w+B w w) = _ at hsum
  change B v v = _ at hv
  change B w w = _ at hw
  change B v w = _
  nlinarith

theorem variableQuadraticBranch_hessian_matrix {n : ℕ} (a c x : Vec n) (σ : ℝ) :
    RadialHessian.matrix (variableQuadraticBranch a c σ) x =
      (1 : Mat n)+σ • (outer c a+outer a c) := by
  ext i j
  rw [RadialHessian.matrix, RadialHessian.bilinearMatrix, variableQuadraticBranch_hessian_bilinear]
  simp only [dot, Pi.single_apply, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, outer,
    Matrix.one_apply]
  split_ifs <;> simp_all <;> ring <;> simp

theorem variableQuadraticBranch_hessian_lower {n : ℕ} {a c : Vec n}
    (ha : sqNorm a = 1) (hc : dot a c = 0) (σ : ℝ) (hσ : |σ| ≤ 1) (x v : Vec n) :
    (1-Real.sqrt (sqNorm c))*sqNorm v ≤
      dot v ((RadialHessian.matrix (variableQuadraticBranch a c σ) x).mulVec v) := by
  rw [RadialHessian.matrix, RadialHessian.bilinearMatrix_quadratic, variableQuadraticBranch_hessian_quadratic]
  have hn := couplingQuadratic_nonneg ha hc (Real.sqrt_nonneg (sqNorm c))
    (Real.sq_sqrt (sqNorm_nonneg c)) hσ v
  dsimp [couplingQuadratic] at hn
  nlinarith

theorem printed_variable_quadratic_hessian_blocks (n : ℕ) (c : Vec (n+1))
    (x : Vec (n+2)) (σ : ℝ) :
    let B := RadialHessian.matrix (variableQuadraticBranch (normal n) (Fin.cons 0 c) σ) x
    B 0 0 = 1 ∧ (∀ j : Fin (n+1), B 0 j.succ = σ*c j) ∧
      (∀ i : Fin (n+1), B i.succ 0 = σ*c i) ∧
      (∀ i j : Fin (n+1), B i.succ j.succ = if i=j then 1 else 0) := by
  rw [variableQuadraticBranch_hessian_matrix]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, outer, normal, Pi.single_apply,
    Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero, if_false, if_true, zero_mul, mul_zero,
    add_zero, zero_add, mul_one, one_mul, Matrix.one_apply, Fin.succ_inj]
  simp [eq_comm]

end BfgsVerification.NormalSpike
