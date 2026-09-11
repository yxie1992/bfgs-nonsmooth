import BfgsVerification.PlanarPrincipalTargets

noncomputable section
namespace BfgsVerification

theorem planarAffineCriticalCluster : PlanarAffineCriticalClusterTarget :=
  @AdmissibleBFGSRun.planar_affineCritical_cluster_on_sublevel

theorem planarConvergence : PlanarConvergenceTarget :=
  @AdmissibleBFGSRun.planar_convergence_on_sublevel

theorem planarLocalBasin : PlanarLocalBasinTarget :=
  @PlanarConvergence.local_convergence_basin

end BfgsVerification
