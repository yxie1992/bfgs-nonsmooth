import BfgsVerification.NormalSpikeVariableGeometry
import BfgsVerification.NormalSpikeHessian

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike
open RadialCertificate

theorem variableObjective_hasSecondDerivAt_inward_ray {n : ℕ} (a c x : Vec n)
    (hw : 0 < 1+dot c x) (hv : 0 < dot a x) :
    HasDerivAt (deriv (fun t : ℝ => variableObjective a c ((1-t) • x)))
      (sqNorm x+2*dot c x*dot a x+(dot a x)^2*density (dot a x)) 0 := by
  have hdA := (variable_radial_gradient_difference_hasDerivAt a c x hv).sub_const (dot (variablePositiveGradient a c x) x)
  have hd : HasDerivAt (fun t : ℝ => -dot (variablePositiveGradient a c ((1-t) • x)) x)
      (sqNorm x+2*dot c x*dot a x+(dot a x)^2*density (dot a x)) 0 := by
    convert hdA using 1
    ext t
    rw [dot_sub_left]
    ring
  apply hd.congr_of_eventuallyEq
  have hwnear : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1+dot c ((1-t) • x) := by
    have hcont : ContinuousAt (fun t : ℝ => 1+dot c ((1-t) • x)) 0 := by unfold dot; fun_prop
    exact hcont.eventually_const_lt (by simpa using hw)
  filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ) < 1), hwnear] with t ht hwt
  have hpos : 0 < dot a ((1-t) • x) := by
    rw [dot_smul_right]
    exact mul_pos (sub_pos.mpr ht) hv
  have hray : HasDerivAt (fun s : ℝ => (1-s) • x) (-x) t := by
    simpa only [sub_zero, zero_sub, neg_smul, one_smul] using
      (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const x)
  have hf := (variableObjective_hasFDerivAt_pos a c ((1-t) • x) hwt hpos).comp_hasDerivAt t hray
  simpa only [map_neg, gradientFunctional_apply] using hf.deriv

theorem variableObjective_radial_hessian {n : ℕ} (a c x : Vec n)
    (hw : 0 < 1+dot c x) (hv : 0 < dot a x) :
    dot x ((RadialHessian.matrix (variableObjective a c) x).mulVec x) =
      sqNorm x+2*dot c x*dot a x+(dot a x)^2*density (dot a x) := by
  have hs := (variableObjective_hasSecondDerivAt_inward_ray a c x hw hv).deriv
  have he : (fun t : ℝ => variableObjective a c ((1-t) • x)) =
      (fun t : ℝ => variableObjective a c (RadialHessian.ray x (-x) t)) := by
    ext t
    congr 1
    unfold RadialHessian.ray
    module
  rw [he, RadialHessian.ray_second_derivative ((variableObjective_contDiffAt_regular a c x hw hv.ne').of_le (by decide))] at hs
  simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg] at hs
  rw [RadialHessian.matrix, RadialHessian.bilinearMatrix_quadratic]
  exact hs


theorem variable_printed_radial_hessian_peak (n : ℕ) {c : Vec (n+2)}
    (hc : dot (normal n) c = 0) (u : ℝ) (hu : 0 ≤ c 1*u) (N : ℕ) :
    dot (sample n u (scale N))
      ((RadialHessian.matrix (variableObjective (normal n) c) (sample n u (scale N))).mulVec
        (sample n u (scale N))) = u^2+(scale N)^2+2*(c 1*u)*scale N+(scale N)⁻¹ := by
  rw [variableObjective_radial_hessian (normal n) c (sample n u (scale N))
    (by rw [variable_sample_dot n hc]; linarith)
    (by rw [sample_normal]; exact scale_pos N)]
  exact variable_sample_radial_curvature_peak n hc u N

end BfgsVerification.NormalSpike
