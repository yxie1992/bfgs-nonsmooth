import BfgsVerification.ReportFamiliesTargets

noncomputable section
namespace BfgsVerification

theorem parabolicCertificate : ParabolicCertificateTarget :=
  @Parabolic.Family.exists_bandCertificate

theorem parabolicConvergence : ParabolicConvergenceTarget :=
  @AdmissibleBFGSRun.parabolic_convergence

theorem transformedGaugeConvergence : TransformedGaugeConvergenceTarget :=
  @AdmissibleBFGSRun.transformedGauge_convergence

theorem relativeInteriorConvergence : RelativeInteriorConvergenceTarget :=
  @AdmissibleBFGSRun.maxLinear_relativeInterior_has_limit

theorem recurrentRelativeInterior : RecurrentRelativeInteriorTarget :=
  @AdmissibleBFGSRun.maxLinear_recurrent_relativeInterior_has_limit

theorem parabolicEligibleSeparation : ParabolicEligibleSeparationTarget :=
  @Parabolic.Example.eligible_radial_unbounded_on_neighborhood

theorem parabolicNonnecessity : ParabolicNonnecessityTarget :=
  @Parabolic.Example.converges_without_radial_secant

theorem accessibleActiveSeparation : AccessibleActiveSeparationTarget :=
  ShiftedAbsAccessibility.objective_level_accessibility_counterexample

end BfgsVerification
