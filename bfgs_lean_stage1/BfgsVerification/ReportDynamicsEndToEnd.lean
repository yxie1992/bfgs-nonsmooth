import BfgsVerification.ReportDynamicsTargets
noncomputable section
namespace BfgsVerification

theorem exactSeedCycle : ExactSeedCycleTarget :=
  ⟨SeedCycle.source_cycle,SeedOrbit.source_metric_posDef⟩

theorem deterministicSeedFailure : DeterministicSeedFailureTarget := by
  intro c₁ c₂ hc₁ hc₁' hc hc₂
  exact SeedOrbit.actual_deterministic_seed_failure hc₁ hc₁' hc hc₂

theorem allSeedTrials : AllSeedTrialsTarget := by
  intro k q hq
  exact ⟨SeedOrbit.orbit_all_trials_differentiable k q hq,SeedOrbit.orbit_trial_point_certificate k q hq⟩

end BfgsVerification
