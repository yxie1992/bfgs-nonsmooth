import BfgsVerification.FixedNormalCompositeTargets

noncomputable section
namespace BfgsVerification

theorem tangentialCompositeConvergence : TangentialCompositeConvergenceTarget :=
  @AdmissibleBFGSRun.tangential_composite_convergence

theorem tangentialCompositeLocalBasin : TangentialCompositeLocalBasinTarget :=
  @FixedNormal.local_tangential_composite_basin

theorem strongCompositeConvergence : StrongCompositeConvergenceTarget :=
  @AdmissibleBFGSRun.strongly_convex_composite_convergence

theorem strongCompositeLocalBasin : StrongCompositeLocalBasinTarget :=
  @FixedNormal.local_strongly_convex_composite_basin

end BfgsVerification
