import BfgsVerification.NormalSpikeGradient

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike
open FixedNormal RadialCertificate

theorem radial_difference_positive {n : ℕ} (a x : Vec n) (hv : 0 < dot a x)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    0 < dot (positiveGradient a x - positiveGradient a ((1-t) • x)) x := by
  have hx : x ≠ 0 := by
    intro he
    rw [he] at hv
    simpa [dot] using hv
  have hsq : 0 < sqNorm x := lt_of_le_of_ne (sqNorm_nonneg x)
    (fun h => hx ((CertificateGeometry.sqNorm_eq_zero_iff x).mp h.symm))
  have hm := seriesMass_monotone (show (1-t)*dot a x ≤ dot a x by nlinarith)
  rw [radial_gradient_difference]
  exact add_pos_of_pos_of_nonneg (mul_pos ht hsq) (mul_nonneg (sub_nonneg.mpr hm) hv.le)

theorem radial_contraction_identities {n : ℕ} (a x : Vec n) (t : ℝ) :
    secantCurvature x ((1-t) • x) (positiveGradient a x) (positiveGradient a ((1-t) • x)) =
      t * dot (positiveGradient a x-positiveGradient a ((1-t) • x)) x ∧
    radialNumerator 0 ((1-t) • x) (positiveGradient a x) (positiveGradient a ((1-t) • x)) =
      -(1-t) * dot (positiveGradient a x-positiveGradient a ((1-t) • x)) x := by
  have he : inwardPoint 0 x t = (1-t) • x := by unfold inwardPoint; module
  simpa only [he, sub_zero] using inward_secant_identities 0 x (positiveGradient a x)
    (positiveGradient a ((1-t) • x)) t

/-- A finite RS constant for a positive radial contraction family bounds the
actual directional curvature at the uncontracted point. -/
theorem radial_curvature_le_of_pair_bound {n : ℕ} (a x : Vec n) (hv : 0 < dot a x)
    {C θ : ℝ} (hθ : 0 < θ) (hθhalf : θ ≤ 1/2)
    (hpair : ∀ t : ℝ, 0 < t → t ≤ θ →
      (radialNumerator 0 ((1-t) • x) (positiveGradient a x) (positiveGradient a ((1-t) • x)))^2 ≤
      C * secantCurvature x ((1-t) • x) (positiveGradient a x) (positiveGradient a ((1-t) • x))) :
    sqNorm x + (dot a x)^2 * density (dot a x) ≤ 4*C := by
  have hd := (radial_gradient_difference_hasDerivAt a x hv).tendsto_slope_zero_right
  simp only [zero_add, sub_zero, zero_smul, sub_self, dot, dotProduct_zero,
    zero_dotProduct, one_smul, sub_zero, smul_eq_mul] at hd
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero] at hd
  apply le_of_tendsto hd
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hθ).filter_mono nhdsWithin_le_nhds] with t ht0 htθ
  have htpos : 0 < t := ht0
  have hthalf : t ≤ 1/2 := htθ.le.trans hθhalf
  let A := dot (positiveGradient a x-positiveGradient a ((1-t) • x)) x
  have hA : 0 < A := radial_difference_positive a x hv htpos (by linarith)
  obtain ⟨hcurv, hnum⟩ := radial_contraction_identities a x t
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
