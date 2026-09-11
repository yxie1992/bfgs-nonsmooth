import BfgsVerification.BFGSGradientScaling
import BfgsVerification.ObjectiveRun
import BfgsVerification.ConvexSubdifferential

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.TranslatedRun

variable {n : ℕ} {Q F : Vec n → ℝ}

def point (R : AdmissibleBFGSRun n Q) (p : Vec n) (t : ℝ) (k : ℕ) : Vec n := p+t • R.x k
def gradient (R : AdmissibleBFGSRun n Q) (t : ℝ) (k : ℕ) : Vec n := t • R.g k

/-- Actual local-model data at every accepted point. Applications prove these
fields from the literal objective; they are not replacement convergence assumptions. -/
structure Data (R : AdmissibleBFGSRun n Q) (F : Vec n → ℝ) (p : Vec n) (t A : ℝ) : Prop where
  convex : ConvexOn ℝ univ F
  value : ∀ k, F (point R p t k)=A+t^2*Q (R.x k)
  hasGradient : ∀ k, HasFDerivAt F (gradientFunctional (gradient R t k)) (point R p t k)

theorem point_step (R : AdmissibleBFGSRun n Q) (p : Vec n) (t : ℝ) (k : ℕ) :
    point R p t (k+1)=point R p t k+bfgsStep (R.H k) (gradient R t k) (R.α k) := by
  simp only [point,gradient,R.step,bfgsStep_scale_gradient,smul_add]
  abel

theorem matrix_update (R : AdmissibleBFGSRun n Q) {t : ℝ} (ht : t≠0) (k : ℕ) :
    R.H (k+1)=inverseBFGS (R.H k) (bfgsStep (R.H k) (gradient R t k) (R.α k))
      (gradient R t (k+1)-gradient R t k) := by
  simp only [gradient,bfgsStep_scale_gradient,← smul_sub,inverseBFGS_scale_secant_pair _ _ _ ht]
  exact R.update k

theorem scaled_pairing (R : AdmissibleBFGSRun n Q) (t : ℝ) (j k : ℕ) :
    dot (gradient R t j) (bfgsStep (R.H k) (gradient R t k) (R.α k))=
      t^2*dot (R.g j) (bfgsStep (R.H k) (R.g k) (R.α k)) := by
  simp only [gradient,bfgsStep_scale_gradient,dot_smul_right,PlanarUpdate.dot_scale_left]
  ring

def run {R : AdmissibleBFGSRun n Q} {p : Vec n} {t A : ℝ} (D : Data R F p t A) (ht : t≠0) :
    AdmissibleBFGSRun n F where
  convex := D.convex
  x := point R p t
  H := R.H
  g := gradient R t
  α := R.α
  c₁ := R.c₁
  c₂ := R.c₂
  c₁_pos := R.c₁_pos
  c₁_lt_c₂ := R.c₁_lt_c₂
  c₂_lt_one := R.c₂_lt_one
  initial_posDef := R.initial_posDef
  alpha_pos := R.alpha_pos
  gradient_nonzero k := smul_ne_zero ht (R.gradient_nonzero k)
  hasGradient := D.hasGradient
  step := point_step R p t
  update := matrix_update R ht
  armijo k := by
    rw [D.value,D.value,scaled_pairing]
    have hh := mul_le_mul_of_nonneg_left (R.armijo k) (sq_nonneg t)
    nlinarith [hh]
  weak_wolfe k := by
    rw [scaled_pairing,scaled_pairing]
    have hh := mul_le_mul_of_nonneg_left (R.weak_wolfe k) (sq_nonneg t)
    nlinarith [hh]

theorem point_tendsto (R : AdmissibleBFGSRun n Q) {z : Vec n}
    (hz : Tendsto R.x atTop (𝓝 z)) (p : Vec n) (t : ℝ) :
    Tendsto (point R p t) atTop (𝓝 (p+t • z)) :=
  tendsto_const_nhds.add (tendsto_const_nhds.smul hz)

theorem value_tendsto {R : AdmissibleBFGSRun n Q} {p : Vec n} {t A q : ℝ}
    (D : Data R F p t A) (hq : Tendsto (fun k => Q (R.x k)) atTop (𝓝 q)) :
    Tendsto (fun k => F (point R p t k)) atTop (𝓝 (A+t^2*q)) := by
  simp_rw [D.value]
  exact tendsto_const_nhds.add (tendsto_const_nhds.mul hq)

end BfgsVerification.TranslatedRun
