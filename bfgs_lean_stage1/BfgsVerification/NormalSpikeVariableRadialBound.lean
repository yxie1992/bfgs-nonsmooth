import BfgsVerification.NormalSpikeVariableGradient

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike
open FixedNormal RadialCertificate

/-- A finite RS constant for a positive radial contraction family bounds the
actual directional curvature at the uncontracted point. -/
theorem variable_radial_curvature_le_of_pair_bound {n : ℕ} {a c : Vec n}
    (ha : sqNorm a = 1) (hc : dot a c = 0) (hcnorm : Real.sqrt (sqNorm c) < 1)
    (x : Vec n) (hv : 0 < dot a x)
    {C θ : ℝ} (hθ : 0 < θ) (hθhalf : θ ≤ 1/2)
    (hpair : ∀ t : ℝ, 0 < t → t ≤ θ →
      (radialNumerator 0 ((1-t) • x) (variablePositiveGradient a c x) (variablePositiveGradient a c ((1-t) • x)))^2 ≤
      C * secantCurvature x ((1-t) • x) (variablePositiveGradient a c x) (variablePositiveGradient a c ((1-t) • x))) :
    sqNorm x+2*dot c x*dot a x + (dot a x)^2 * density (dot a x) ≤ 4*C := by
  have hd := (variable_radial_gradient_difference_hasDerivAt a c x hv).tendsto_slope_zero_right
  simp only [zero_add, sub_zero, zero_smul, sub_self, dot, dotProduct_zero,
    zero_dotProduct, one_smul, sub_zero, smul_eq_mul] at hd
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero] at hd
  apply le_of_tendsto hd
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hθ).filter_mono nhdsWithin_le_nhds] with t ht0 htθ
  have htpos : 0 < t := ht0
  have hthalf : t ≤ 1/2 := htθ.le.trans hθhalf
  let A := dot (variablePositiveGradient a c x-variablePositiveGradient a c ((1-t) • x)) x
  have hA : 0 < A := variable_radial_difference_positive ha hc hcnorm x hv htpos
  obtain ⟨hcurv, hnum⟩ := variable_radial_contraction_identities a c x t
  have hp := hpair t htpos htθ.le
  rw [hcurv, hnum] at hp
  change (-(1-t)*A)^2 ≤ C*(t*A) at hp
  have hlin : (1-t)^2*A ≤ C*t := by
    apply (mul_le_mul_right hA).mp
    nlinarith [hp]
  have hfac : (1/4 : ℝ) ≤ (1-t)^2 := by nlinarith
  have hbound : A ≤ (4*C)*t := by
    nlinarith [mul_le_mul_of_nonneg_right hfac hA.le]
  change t⁻¹*A ≤ 4*C
  rw [← div_eq_inv_mul]
  exact (div_le_iff₀ htpos).mpr hbound


end BfgsVerification.NormalSpike
