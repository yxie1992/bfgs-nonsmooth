import BfgsVerification.ReportApplicationsTargets

noncomputable section
namespace BfgsVerification

theorem affineCertificateCovariance : AffineCertificateCovarianceTarget :=
  @AffineCertificate.hasBandCertificates_affine_iff

theorem centeredSmoothConvergence : CenteredSmoothConvergenceTarget := by
  intro n F ψ γ R star hmin U hU hψ hsmooth hγ hhom hrep hK hKU
  exact ⟨R.centered_values star hmin hU hψ hsmooth hγ hhom hrep hK hKU,
    fun hu => R.centered_iterates star hmin hu hU hψ hsmooth hγ hhom hrep hK hKU⟩

theorem centeredLocalBasin : CenteredLocalBasinTarget :=
  @CenteredSmoothSublinear.local_centered_basin

theorem quadraticGaugeRates : QuadraticGaugeRatesTarget := by
  intro m p Q hQ γ _hγ hhom μ Λ hμ hl hu R
  have hlow (v) : μ * Real.sqrt (sqNorm v) ≤ γ v := by
    simpa only [QuadraticGauge.sqrt_sqNorm_eq_euclidean_norm] using hl v
  have hupp (v) : γ v ≤ Λ * Real.sqrt (sqNorm v) := by
    simpa only [QuadraticGauge.sqrt_sqNorm_eq_euclidean_norm] using hu v
  have hr := R.quadraticGauge_euclidean_value_log_orders Q hQ γ hhom μ Λ hμ hl hu
  exact ⟨hr.1, hr.2, R.quadraticGauge_convergence Q hQ γ hhom μ Λ hμ hlow hupp⟩

theorem ellipsoidCertificateGeometry : EllipsoidCertificateGeometryTarget := by
  intro n W Z hW hZ
  exact ⟨CertificateGeometry.ellipsoid_support hW,
    CertificateGeometry.projected_ellipsoid_subset_iff hW hZ⟩

theorem pointwiseCertificateCapacity : PointwiseCertificateCapacityTarget :=
  @PointwiseFeasibility.visibility_secant_iff_source_capacity

theorem planarHomogeneousEscape : PlanarHomogeneousEscapeTarget :=
  @AdmissibleBFGSRun.maxLinear_planar_unbounded_complete

theorem parabolicDenominator : ParabolicDenominatorTarget :=
  @Parabolic.Family.exists_small_denominator_bounds

end BfgsVerification
