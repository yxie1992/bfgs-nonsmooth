import BfgsVerification.NormalSpikeVariableConvergence
import BfgsVerification.NormalSpikeRadialBound

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.NormalSpike
open FixedNormal RadialCertificate

def variablePositiveGradient {n : ℕ} (a c x : Vec n) : Vec n :=
  x + dot a x • c + (1+dot c x+seriesMass (dot a x)) • a

theorem variableObjective_hasFDerivAt_pos {n : ℕ} (a c x : Vec n)
    (hw : 0 < 1+dot c x) (hv : 0 < dot a x) :
    HasFDerivAt (variableObjective a c) (gradientFunctional (variablePositiveGradient a c x)) x := by
  have hl (b : Vec n) : HasFDerivAt (dot b) (gradientFunctional b) x := by
    convert (gradientFunctional b).hasFDerivAt (x := x) using 1
    exact funext (fun y => (gradientFunctional_apply b y).symm)
  have hp := ((hl c).const_add 1).mul (hl a)
  have habs := (hasDerivAt_abs_pos (mul_pos hw hv)).comp_hasFDerivAt x hp
  have hr := (sourcePrimitive_hasDerivAt (dot a x)).comp_hasFDerivAt x (hl a)
  have hd := ((quadratic_hasFDerivAt x).add habs).add hr
  convert hd using 1
  ext z
  simp only [variablePositiveGradient, gradientFunctional_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, one_mul]
  change (x+dot a x • c+(1+dot c x+seriesMass (dot a x)) • a) ⬝ᵥ z = _
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  change dot x z+dot a x*dot c z+(1+dot c x+seriesMass (dot a x))*dot a z = _
  ring

theorem variablePositiveGradient_pair {n : ℕ} (a c x z : Vec n) :
    dot (variablePositiveGradient a c x) z =
      dot x z+dot a x*dot c z+(1+dot c x+seriesMass (dot a x))*dot a z := by
  change (x+dot a x • c+(1+dot c x+seriesMass (dot a x)) • a) ⬝ᵥ z = _
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  rfl

theorem variable_radial_gradient_difference {n : ℕ} (a c x : Vec n) (t : ℝ) :
    dot (variablePositiveGradient a c x-variablePositiveGradient a c ((1-t) • x)) x =
      t*(sqNorm x+2*dot c x*dot a x) +
        (seriesMass (dot a x)-seriesMass ((1-t)*dot a x))*dot a x := by
  rw [dot_sub_left, variablePositiveGradient_pair, variablePositiveGradient_pair]
  simp only [dot_smul_right]
  have hd : dot ((1-t) • x) x = (1-t)*sqNorm x := by
    change ((1-t) • x) ⬝ᵥ x = _
    rw [smul_dotProduct]
    simp only [smul_eq_mul, dotProduct, sqNorm, pow_two]
  have hxx : dot x x = sqNorm x := by simp only [dot, sqNorm, pow_two]
  rw [hd, hxx]
  ring

theorem variable_radial_gradient_difference_hasDerivAt {n : ℕ} (a c x : Vec n)
    (hv : 0 < dot a x) :
    HasDerivAt (fun t : ℝ => dot (variablePositiveGradient a c x-
      variablePositiveGradient a c ((1-t) • x)) x)
      (sqNorm x+2*dot c x*dot a x+(dot a x)^2*density (dot a x)) 0 := by
  have harg : HasDerivAt (fun t : ℝ => (1-t)*dot a x) (-dot a x) 0 := by
    convert (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))).mul_const (dot a x)) using 1 <;> simp <;> ring
  have hm : HasDerivAt seriesMass (density (dot a x)) ((1-(0 : ℝ))*dot a x) := by
    simpa only [sub_zero, one_mul] using seriesMass_hasDerivAt_pos hv
  have hmass := hm.comp 0 harg
  have hd := ((hasDerivAt_id (0 : ℝ)).mul_const (sqNorm x+2*dot c x*dot a x)).add
    (((hasDerivAt_const (0 : ℝ) (seriesMass (dot a x))).sub hmass).mul_const (dot a x))
  convert hd using 1
  · ext t
    exact variable_radial_gradient_difference a c x t
  · ring

theorem variable_radial_difference_positive {n : ℕ} {a c : Vec n}
    (ha : sqNorm a = 1) (hc : dot a c = 0) (hcnorm : Real.sqrt (sqNorm c) < 1)
    (x : Vec n) (hv : 0 < dot a x) {t : ℝ} (ht : 0 < t) :
    0 < dot (variablePositiveGradient a c x-variablePositiveGradient a c ((1-t) • x)) x := by
  have hneq : x ≠ 0 := by intro he; subst x; simpa [dot] using hv
  have hsq : 0 < sqNorm x := lt_of_le_of_ne (sqNorm_nonneg x)
    (fun h => hneq ((CertificateGeometry.sqNorm_eq_zero_iff x).mp h.symm))
  have hb := cross_term_bound ha hc (Real.sqrt_nonneg (sqNorm c)) (Real.sq_sqrt (sqNorm_nonneg c)) x
  have hq : 0 < sqNorm x+2*dot c x*dot a x := by
    have hh := mul_pos (sub_pos.mpr hcnorm) hsq
    have hl := neg_abs_le (dot c x*dot a x)
    nlinarith
  have hm := seriesMass_monotone (show (1-t)*dot a x ≤ dot a x by nlinarith)
  rw [variable_radial_gradient_difference]
  exact add_pos_of_pos_of_nonneg (mul_pos ht hq) (mul_nonneg (sub_nonneg.mpr hm) hv.le)

theorem variable_radial_contraction_identities {n : ℕ} (a c x : Vec n) (t : ℝ) :
    secantCurvature x ((1-t) • x) (variablePositiveGradient a c x) (variablePositiveGradient a c ((1-t) • x)) =
      t*dot (variablePositiveGradient a c x-variablePositiveGradient a c ((1-t) • x)) x ∧
    radialNumerator 0 ((1-t) • x) (variablePositiveGradient a c x) (variablePositiveGradient a c ((1-t) • x)) =
      -(1-t)*dot (variablePositiveGradient a c x-variablePositiveGradient a c ((1-t) • x)) x := by
  have he : inwardPoint 0 x t = (1-t) • x := by unfold inwardPoint; module
  simpa only [he, sub_zero] using inward_secant_identities 0 x (variablePositiveGradient a c x)
    (variablePositiveGradient a c ((1-t) • x)) t

end BfgsVerification.NormalSpike
