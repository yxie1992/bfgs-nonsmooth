import BfgsVerification.ReportConstructionTargets

noncomputable section
namespace BfgsVerification

theorem coerciveSeedFailure : CoerciveSeedFailureTarget := by
  intro c₁ c₂ hc₁ hc₁' hc hc₂
  exact SeedOrbit.actual_coercive_deterministic_failure hc₁ hc₁' hc hc₂

theorem dScalarFunction : DScalarFunctionTarget := by
  intro b hl hr
  exact DScalar.scalar_function_contract hl hr

theorem centeredSpectralConvergence : CenteredSpectralConvergenceTarget := by
  intro m n
  exact ⟨fun x => CenteredSpectral.objective_operator_norm x,
    fun R => CenteredSpectral.fullBFGS_convergence R⟩

theorem singularCurvatureCounterexample : SingularCurvatureCounterexampleTarget :=
  RadialSingularCurvature.singular_curvature_counterexample

end BfgsVerification
