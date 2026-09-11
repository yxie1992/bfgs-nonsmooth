import BfgsVerification.PoweredGaugeRadial

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.RadialHessian

def ray {n : ℕ} (x v : Vec n) (t : ℝ) : Vec n := x+t • v

theorem ray_hasDerivAt {n : ℕ} (x v : Vec n) (t : ℝ) :
    HasDerivAt (ray x v) v t := by
  simpa only [ray,one_smul] using ((hasDerivAt_id t).smul_const v).const_add x

/-- The actual scalar second derivative along a straight ray is the actual
second Fréchet derivative applied twice to that direction. -/
theorem ray_second_derivative {n : ℕ} {F : Vec n → ℝ} {x : Vec n}
    (hF : ContDiffAt ℝ 2 F x) (v : Vec n) :
    deriv (deriv (fun t => F (ray x v t))) 0 = (fderiv ℝ (fderiv ℝ F) x) v v := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hd := hfd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (ray_hasDerivAt x v 0) (by simp [ray])
  have ha := hd.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have heq : deriv (fun t => F (ray x v t)) =ᶠ[𝓝 0]
      (fun t => (fderiv ℝ F (ray x v t)) v) := by
    have hnear := (ray_hasDerivAt x v 0).continuousAt.eventually
      (by simpa only [ray,zero_smul,add_zero] using hF.eventually (by norm_num))
    filter_upwards [hnear] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (ray_hasDerivAt x v t)).deriv
  have hh := ha.congr_of_eventuallyEq heq
  simpa only [map_zero,add_zero] using hh.deriv

def bilinearMatrix {n : ℕ} (B : Vec n →L[ℝ] Vec n →L[ℝ] ℝ) : Mat n :=
  fun i j => B (Pi.single i 1) (Pi.single j 1)

theorem bilinearMatrix_quadratic {n : ℕ} (B : Vec n →L[ℝ] Vec n →L[ℝ] ℝ)
    (v : Vec n) : dot v ((bilinearMatrix B).mulVec v)=B v v := by
  have he (l : Vec n →L[ℝ] ℝ) : l v=∑ i, v i*l (Pi.single i 1) := by
    have hh := congrArg (fun l : Vec n →L[ℝ] ℝ => l v) (gradientFunctional_coordinates l)
    simpa only [gradientFunctional_apply,dot,mul_comm] using hh.symm
  have hB : B v=∑ i, v i • B (Pi.single i 1) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hs : Pi.single i (v i)=v i • (Pi.single i 1 : Vec n) := by
      simpa only [smul_eq_mul,mul_one] using Pi.single_smul' i (v i) (1 : ℝ)
    rw [hs,map_smul]
  rw [hB]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  simp only [dot,Matrix.mulVec,dotProduct,bilinearMatrix]
  apply Finset.sum_congr rfl
  intro i hi
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

def matrix {n : ℕ} (F : Vec n → ℝ) (x : Vec n) : Mat n :=
  bilinearMatrix (fderiv ℝ (fderiv ℝ F) x)

/-- Source R's literal rᵀ Hessian(F)(x) r interpretation, with the matrix
entries constructed from the actual second derivative. -/
theorem ray_second_derivative_matrix {n : ℕ} {F : Vec n → ℝ} {x : Vec n}
    (hF : ContDiffAt ℝ 2 F x) (v : Vec n) :
    deriv (deriv (fun t => F (ray x v t))) 0 = dot v ((matrix F x).mulVec v) := by
  rw [ray_second_derivative hF v]
  exact (bilinearMatrix_quadratic _ _).symm

end BfgsVerification.RadialHessian
