import BfgsVerification.ReportCoreTargets

noncomputable section
open scoped Topology
open Set Filter

namespace BfgsVerification

theorem transportedCertificateConvergence : TransportedCertificateTarget := by
  intro n F R b hK star hmin hstart hcert
  have h := R.transported_certificate_convergence_on_sublevel b hK star hmin hstart hcert
  exact ⟨h.1, euclidean_distance_to_argmin_of_values (convex_continuous R.convex)
    star hmin hK (fun k => (R.objective_le_initial k).trans hstart) h.1, h.2.2⟩

theorem homogeneousDichotomy : HomogeneousDichotomyTarget := by
  intro n F R hF
  exact R.homogeneous_value_dichotomy hF

theorem scalarMetricConvergence : ScalarMetricConvergenceTarget := by
  intro f R hK star hmin huniq
  exact R.convergence hK star hmin huniq

theorem scalarBFGSConvergence : ScalarBFGSConvergenceTarget := by
  intro F R hK star hmin huniq
  exact R.scalar_convergence hK star hmin huniq

theorem radialCertificateConvergence : RadialCertificateConvergenceTarget := by
  intro n F R b hK star hmin hstart hRS
  have h := R.radial_certificate_convergence_on_sublevel b hK star hmin hstart hRS
  exact ⟨h.1, euclidean_distance_to_argmin_of_values (convex_continuous R.convex)
    star hmin hK (fun k => (R.objective_le_initial k).trans hstart) h.1, h.2.2⟩

end BfgsVerification
