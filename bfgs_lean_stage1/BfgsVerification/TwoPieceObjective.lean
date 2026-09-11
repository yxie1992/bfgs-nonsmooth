import BfgsVerification.TwoPieceAlgebra
import BfgsVerification.ConvexSubdifferential

noncomputable section
open Set Matrix
namespace BfgsVerification.TwoPieceBudget

def objective (x : Vec 2) : ℝ := |x 0|+x 1

theorem objective_convex : ConvexOn ℝ univ objective := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  have hh : |a*x 0+b*y 0| ≤ a*|x 0|+b*|y 0| := by
    calc
      _ ≤ |a*x 0|+|b*y 0| := abs_add_le _ _
      _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
  simp only [objective,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  nlinarith only [hh]

theorem support_positive {x : Vec 2} (hx : 0 ≤ x 0) :
    Homogeneous.Supports objective x (gradient 1) := by
  intro z
  simp only [objective,abs_of_nonneg hx,gradient,dot,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,Pi.sub_apply]
  linarith [le_abs_self (z 0)]

theorem support_negative {x : Vec 2} (hx : x 0 ≤ 0) :
    Homogeneous.Supports objective x (gradient (-1)) := by
  intro z
  simp only [objective,abs_of_nonpos hx,gradient,dot,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,Pi.sub_apply]
  linarith [neg_le_abs (z 0)]

theorem actual_gradient_shape {x g : Vec 2}
    (hg : HasFDerivAt objective (gradientFunctional g) x) :
    (g 0)^2=1 ∧ g=gradient (g 0) ∧ 0 < g 0*x 0 ∧ |x 0|=g 0*x 0 := by
  have hx : x 0 ≠ 0 := by
    intro hz
    have hp := supporting_vector_eq_gradient (support_positive (by linarith : 0 ≤ x 0)) hg
    have hn := supporting_vector_eq_gradient (support_negative (by linarith : x 0 ≤ 0)) hg
    have he := congrArg (fun v : Vec 2 => v 0) (hp.trans hn.symm)
    norm_num [gradient] at he
  rcases lt_or_gt_of_ne hx with hn | hp
  · have hg' := (supporting_vector_eq_gradient (support_negative hn.le) hg).symm
    rw [hg']
    simp [gradient,abs_of_neg hn,hn]
  · have hg' := (supporting_vector_eq_gradient (support_positive hp.le) hg).symm
    rw [hg']
    simp [gradient,abs_of_pos hp,hp]

variable (R : AdmissibleBFGSRun 2 objective)

def sigma (k : ℕ) : ℝ := R.g k 0
def aa (k : ℕ) : ℝ := R.H k 0 0
def bb (k : ℕ) : ℝ := R.H k 0 1
def cc (k : ℕ) : ℝ := R.H k 1 1
def A (k : ℕ) : ℝ := energy (aa R k) (bb R k) (cc R k) (sigma R k)
def B (k : ℕ) : ℝ := cross (aa R k) (bb R k) (sigma R k)
def D (k : ℕ) : ℝ := determinant (aa R k) (bb R k) (cc R k)
def X (k : ℕ) : ℝ := |R.x k 0|

theorem sigma_sq (k : ℕ) : (sigma R k)^2=1 := (actual_gradient_shape (R.hasGradient k)).1
theorem gradient_shape (k : ℕ) : R.g k=gradient (sigma R k) :=
  (actual_gradient_shape (R.hasGradient k)).2.1
theorem X_eq (k : ℕ) : X R k=sigma R k*R.x k 0 :=
  (actual_gradient_shape (R.hasGradient k)).2.2.2
theorem X_pos (k : ℕ) : 0 < X R k := by
  rw [X_eq]
  exact (actual_gradient_shape (R.hasGradient k)).2.2.1

theorem matrix_shape (k : ℕ) : R.H k=matrix (aa R k) (bb R k) (cc R k) := by
  have h := (R.positive_definite k).isHermitian.eq
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix,aa,bb,cc]
  have he := congrArg (fun M : Mat 2 => M 0 1) h
  simpa using he

theorem sigma_next (k : ℕ) : sigma R (k+1) = -sigma R k := by
  have hs : sigma R (k+1) = sigma R k ∨ sigma R (k+1) = -sigma R k :=
    sq_eq_sq_iff_eq_or_eq_neg.mp ((sigma_sq R (k+1)).trans (sigma_sq R k).symm)
  rcases hs with hs | hs
  · have he : R.g (k+1)=R.g k := by rw [gradient_shape R (k+1),gradient_shape R k,hs]
    have hp := R.curvature_pos k
    rw [he,sub_self] at hp
    simp [dot] at hp
  · exact hs

theorem A_eq_q (k : ℕ) : A R k=R.q k := by
  rw [AdmissibleBFGSRun.q,metricEnergy,matrix_shape R k,gradient_shape R k]
  obtain hs | hs := sq_eq_one_iff.mp (sigma_sq R k)
  all_goals
    simp only [A,hs,energy,gradient,matrix,dot,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    ring

theorem A_pos (k : ℕ) : 0 < A R k := by rw [A_eq_q]; exact R.q_pos k

theorem D_pos (k : ℕ) : 0 < D R k := by
  have hd := (R.positive_definite k).det_pos
  rw [matrix_shape R k,Matrix.det_fin_two] at hd
  simpa [D,determinant,matrix,pow_two] using hd

theorem B_pos (k : ℕ) : 0 < B R k := by
  have hc := R.curvature_pos k
  rw [matrix_shape R k,gradient_shape R k,gradient_shape R (k+1),sigma_next R k,
    curvature_formula _ _ _ _ _ (sigma_sq R k)] at hc
  exact (mul_pos_iff_of_pos_left (mul_pos (by norm_num) (R.alpha_pos k))).mp hc

end BfgsVerification.TwoPieceBudget
