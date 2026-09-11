import BfgsVerification.ReportGeometryTargets
import BfgsVerification.ReportCoreEndToEnd

namespace BfgsVerification

theorem certificateNormalization : CertificateNormalizationTarget := by
  intro n F K fstar c₁ c₂ hc₁ hc₂ b hb
  exact TransportedCertificate.hasBandCertificates_iff_zero_budget hc₁ hc₂ b hb

theorem recurrentAffineHull : RecurrentAffineHullTarget := by
  intro n A hA R L hlim
  exact AdmissibleBFGSRun.maxLinear_recurrent_affine_zero A hA R L hlim

theorem maxLinearAffineEscape : MaxLinearAffineEscapeTarget := by
  intro n A hA R hzero
  exact AdmissibleBFGSRun.maxLinear_escape_of_zero_not_mem_affineSpan A hA R hzero

theorem radialInterceptEquivalence : RadialInterceptEquivalenceTarget := by
  intro n F hF K hK star
  exact RadialCertificate.radial_iff_intercept_on_compact hF hK star

theorem inwardCertificateConvergence : InwardCertificateConvergenceTarget := by
  intro n F R b hK star hmin hstart hIR
  exact radialCertificateConvergence R b hK star hmin hstart
    (RadialCertificate.radial_of_inward_on_compact R.convex hK star hIR)

theorem incomingJumpObstruction : IncomingJumpObstructionTarget := by
  intro ι l hl n r F K fstar c₁ c₂ η hc₂ z h x g coeff hz hx hdiff hp hd hrep hcost
  exact TransportedCertificate.incoming_jump_no_visibility_secant
    hc₂ z h x g coeff hz hx hdiff hp hd hrep hcost

theorem scalarCertificateCharacterization : ScalarCertificateCharacterizationTarget := by
  intro F K hF star hK c₁ c₂ η hc₂ hη
  exact TransportedCertificate.scalar_certificate_iff_eligible_lipschitz hF star hK hc₂ hη

end BfgsVerification
