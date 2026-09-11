import BfgsVerification.NormalSpikeSamples
import BfgsVerification.RadialHessian

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike

theorem objective_contDiffAt_pos {n : ℕ} (a x : Vec n) (hv : 0 < dot a x) :
    ContDiffAt ℝ 3 (objective a) x := by
  have hr : ContDiffAt ℝ 3 sourcePrimitive (dot a x) := by
    have he : sourcePrimitive = seriesPrimitive := funext fun v => (seriesPrimitive_eq_source v).symm
    rw [he]
    exact seriesPrimitive_contDiffAt_pos hv
  have hp : ContDiffAt ℝ 3 normalPenalty (dot a x) := (contDiffAt_abs hv.ne').add hr
  have hl : ContDiff ℝ 3 (dot a) := by
    convert (gradientFunctional a).contDiff using 1
    exact funext (fun y => (gradientFunctional_apply a y).symm)
  exact quadratic_contDiff.contDiffAt.add (hp.comp x hl.contDiffAt)

theorem objective_hasSecondDerivAt_inward_ray {n : ℕ} (a x : Vec n) (hv : 0 < dot a x) :
    HasDerivAt (deriv (fun t : ℝ => objective a ((1-t) • x)))
      (sqNorm x+(dot a x)^2*density (dot a x)) 0 := by
  have hdA := (radial_gradient_difference_hasDerivAt a x hv).sub_const (dot (positiveGradient a x) x)
  have hd : HasDerivAt (fun t : ℝ => -dot (positiveGradient a ((1-t) • x)) x)
      (sqNorm x+(dot a x)^2*density (dot a x)) 0 := by
    convert hdA using 1
    ext t
    rw [dot_sub_left]
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
  have hpos : 0 < dot a ((1-t) • x) := by
    rw [dot_smul_right]
    exact mul_pos (sub_pos.mpr ht) hv
  have hray : HasDerivAt (fun s : ℝ => (1-s) • x) (-x) t := by
    simpa only [sub_zero, zero_sub, neg_smul, one_smul] using
      (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const x)
  have hf := (objective_hasFDerivAt_pos a ((1-t) • x) hpos).comp_hasDerivAt t hray
  simpa only [map_neg, gradientFunctional_apply] using hf.deriv

theorem objective_radial_hessian {n : ℕ} (a x : Vec n) (hv : 0 < dot a x) :
    dot x ((RadialHessian.matrix (objective a) x).mulVec x) =
      sqNorm x+(dot a x)^2*density (dot a x) := by
  have hs := (objective_hasSecondDerivAt_inward_ray a x hv).deriv
  have he : (fun t : ℝ => objective a ((1-t) • x)) =
      (fun t : ℝ => objective a (RadialHessian.ray x (-x) t)) := by
    ext t
    congr 1
    unfold RadialHessian.ray
    module
  rw [he, RadialHessian.ray_second_derivative ((objective_contDiffAt_pos a x hv).of_le (by decide))] at hs
  simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg] at hs
  rw [RadialHessian.matrix, RadialHessian.bilinearMatrix_quadratic]
  exact hs

theorem printed_radial_hessian_peak (n : ℕ) (u : ℝ) (N : ℕ) :
    dot (sample n u (scale N)) ((RadialHessian.matrix (objective (normal n)) (sample n u (scale N))).mulVec
      (sample n u (scale N))) = u^2+(scale N)^2+(scale N)⁻¹ := by
  rw [objective_radial_hessian (normal n) (sample n u (scale N))
    (by rw [sample_normal]; exact scale_pos N)]
  exact sample_radial_curvature_peak n u N

end BfgsVerification.NormalSpike
