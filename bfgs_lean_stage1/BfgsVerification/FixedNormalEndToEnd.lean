import BfgsVerification.FixedNormalTargets

noncomputable section
namespace BfgsVerification

theorem fixedNormalHyperplane : FixedNormalHyperplaneTarget :=
  @AdmissibleBFGSRun.fixed_normal_hyperplane_convergence

theorem parallelInterfacesCluster : ParallelInterfacesClusterTarget :=
  @AdmissibleBFGSRun.parallel_interfaces_affineCritical_cluster

theorem parallelInterfacesConvergence : ParallelInterfacesConvergenceTarget :=
  @AdmissibleBFGSRun.parallel_interfaces_convergence_of_affine_correctness

theorem fixedNormalLocalBasin : FixedNormalLocalBasinTarget :=
  @FixedNormal.local_hyperplane_convergence_basin

theorem parallelInterfacesLocalBasin : ParallelInterfacesLocalBasinTarget :=
  @FixedNormal.local_parallel_interfaces_convergence_basin

end BfgsVerification
