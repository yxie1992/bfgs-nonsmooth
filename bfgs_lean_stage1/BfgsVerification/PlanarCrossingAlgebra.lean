import BfgsVerification.PlanarCornerTransport

/-! Exact crossing numerator and linear-curvature algebra for C's endpoint
secant estimate. All norms marked Euclidean are the actual L2 norms. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
namespace PlanarCrossing
open HomogeneousPlanar

theorem abs_dot_le_euclidean_norm (u v : Vec 2) :
    |dot u v| ≤ ‖euclideanVector u‖*‖euclideanVector v‖ :=
  abs_dot_le_of_sqNorm_le u v ‖euclideanVector u‖ ‖euclideanVector v‖
    (norm_nonneg _) (norm_nonneg _)
    (FrameNorms.euclidean_norm_sq (euclideanVector u)).symm.le
    (FrameNorms.euclidean_norm_sq (euclideanVector v)).symm.le

/-- At a tie point the jump pairs to zero. Both branch remainders and the
field increment are first order in the step length. -/
theorem crossing_numerator_bound {y ri rj jump wz wp : Vec 2} {L G H B r : ℝ}
    (hL : 0≤L) (hG : 0≤G) (hH : 0≤H) (hB : 0≤B) (hr : 0≤r)
    (hy : y=rj+jump+ri) (horth : dot jump wp=0)
    (hi : ‖euclideanVector ri‖≤L*r) (hj : ‖euclideanVector rj‖≤L*r)
    (hw : ‖euclideanVector wz‖≤G) (hjump : ‖euclideanVector jump‖≤H)
    (hchange : ‖euclideanVector (wz-wp)‖≤B*r) :
    |dot y wz| ≤ (2*L*G+H*B)*r := by
  have he : dot y wz=dot rj wz+dot ri wz+dot jump (wz-wp) := by
    rw [hy]
    simp only [dot,dotProduct,Pi.add_apply,Pi.sub_apply,add_mul,mul_sub,
      Finset.sum_add_distrib,Finset.sum_sub_distrib] at horth ⊢
    linarith
  have hb1 : |dot rj wz|≤L*r*G := (abs_dot_le_euclidean_norm _ _).trans (by gcongr)
  have hb2 : |dot ri wz|≤L*r*G := (abs_dot_le_euclidean_norm _ _).trans (by gcongr)
  have hb3 : |dot jump (wz-wp)|≤H*(B*r) := (abs_dot_le_euclidean_norm _ _).trans (by gcongr)
  rw [he]
  calc
    _ ≤ |dot rj wz+dot ri wz|+|dot jump (wz-wp)| := abs_add _ _
    _ ≤ (|dot rj wz|+|dot ri wz|)+|dot jump (wz-wp)| := by gcongr; exact abs_add _ _
    _ ≤ (L*r*G+L*r*G)+H*(B*r) := by gcongr
    _ = _ := by ring

/-- The exact planar inverse turns the two accepted directional pairings
into a step-length estimate. This is the actual inverse of the gradient rows. -/
theorem crossing_inverse_step_bound {a b s r : Vec 2} {A E d t : ℝ}
    (hdet : pairDet a b ≠ 0) (hA : 0≤A) (hE : 0≤E) (hd : 0≤d) (ht : 0≤t)
    (hinv : ‖AffineProjection.matrixCLM (pairMatrix a b)⁻¹‖≤A)
    (ha : dot a s = -d) (hb : dot b s=t-d-dot r s)
    (hr : |dot r s|≤E*‖s‖^2) :
    ‖s‖ ≤ A*(2*d+t+E*‖s‖^2) := by
  have habs : |dot a s|=d := by rw [ha,abs_neg,abs_of_nonneg hd]
  have hbabs : |dot b s|≤t+d+E*‖s‖^2 := by
    rw [hb]
    calc
      _ ≤ |t-d|+|dot r s| := abs_sub _ _
      _ ≤ (|t|+|d|)+|dot r s| := by gcongr; exact abs_sub _ _
      _ ≤ t+d+E*‖s‖^2 := by rw [abs_of_nonneg ht,abs_of_nonneg hd]; gcongr
  calc
    ‖s‖ ≤ ‖AffineProjection.matrixCLM (pairMatrix a b)⁻¹‖*(|dot a s|+|dot b s|) :=
      pair_inverse_bound a b s hdet
    _ ≤ A*(d+(t+d+E*‖s‖^2)) := by rw [habs]; gcongr
    _ = _ := by ring

/-- Absorption needs only a sufficiently small step, not a positive Hessian
lower bound. Weak Wolfe supplies the linear curvature term. -/
theorem crossing_linear_curvature {r A L σ d t : ℝ}
    (hr : 0≤r) (hA : 0<A) (hσ : 0<σ)
    (hstep : r≤A*(2*d+t+L*r^2)) (hsmall : A*L*r≤1/2)
    (hwolfe : σ*d≤t) :
    r≤(2*A*(1+2/σ))*t := by
  have hquad : A*L*r^2≤r/2 := by
    have hm := mul_le_mul_of_nonneg_right hsmall hr
    nlinarith
  have hlin : r≤2*A*(2*d+t) := by nlinarith [hstep]
  have hd : d≤t/σ := (le_div_iff₀ hσ).mpr (by nlinarith [hwolfe])
  calc
    r≤2*A*(2*d+t) := hlin
    _≤2*A*(2*(t/σ)+t) := by gcongr
    _=(2*A*(1+2/σ))*t := by ring

/-- First-order numerator and linear curvature give a secant correction
that is itself bounded by a constant times the step length. -/
theorem crossing_secant_correction {num B C r t : ℝ}
    (hB : 0≤B) (hC : 0≤C) (hr : 0≤r) (ht : 0<t)
    (hnum : |num|≤B*r) (hcurv : r≤C*t) :
    num^2/t≤B^2*C*r := by
  apply (div_le_iff₀ ht).mpr
  have hn := (sq_le_sq₀ (abs_nonneg num) (mul_nonneg hB hr)).mpr hnum
  rw [sq_abs] at hn
  have hm := mul_le_mul_of_nonneg_left hcurv (by positivity : 0≤B^2*r)
  nlinarith [hn]

end PlanarCrossing
end BfgsVerification
