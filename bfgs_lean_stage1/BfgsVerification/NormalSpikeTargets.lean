import BfgsVerification.NormalSpikeMassSupport

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike

/-- The literal integral-defined scalar in U.18, with all stated regularity,
zero-endpoint, exact-peak and curvature-divergence assertions. -/
def SourceSpikePropertiesTarget : Prop :=
  ConvexOn ℝ univ sourcePrimitive ∧ ContDiff ℝ 1 sourcePrimitive ∧
  ContDiffOn ℝ 3 sourcePrimitive ({0}ᶜ : Set ℝ) ∧
  (∀ v, 0 ≤ sourcePrimitive v) ∧ (∀ v ≤ 0, sourcePrimitive v = 0) ∧
  (∀ v ≥ 0, 0 ≤ deriv sourcePrimitive v ∧ deriv sourcePrimitive v ≤ 6*v^2 ∧
    sourcePrimitive v ≤ 6*v^3) ∧
  HasDerivAt (deriv sourcePrimitive) 0 0 ∧ deriv (deriv sourcePrimitive) 0 = 0 ∧
  (∀ N : ℕ, sourcePrimitive (scale N) = (64/315 : ℝ)*(scale N)^3 + (1/6 : ℝ)*(scale N)^7 ∧
    deriv sourcePrimitive (scale N) = (8/9 : ℝ)*(scale N)^2 ∧
    deriv (deriv sourcePrimitive) (scale N) = ((scale N)^3)⁻¹) ∧
  Tendsto (fun N => deriv (deriv sourcePrimitive) (scale N)) atTop atTop ∧
  ¬ ContinuousAt (deriv (deriv sourcePrimitive)) 0

theorem sourceSpikeProperties : SourceSpikePropertiesTarget := by
  refine ⟨sourcePrimitive_convex, sourcePrimitive_contDiff, sourcePrimitive_contDiffOn_off_zero,
    ?_, ?_, ?_, sourcePrimitive_hasSecondDerivAt_zero, sourcePrimitive_second_derivative_zero, ?_,
    sourcePrimitive_second_derivative_peaks_unbounded, sourcePrimitive_second_derivative_not_continuousAt_zero⟩
  · intro v
    rw [← seriesPrimitive_eq_source]
    exact seriesPrimitive_nonneg v
  · intro v hv
    rw [← seriesPrimitive_eq_source]
    exact seriesPrimitive_nonpos hv
  · intro v hv
    rw [(sourcePrimitive_hasDerivAt v).deriv, ← seriesPrimitive_eq_source]
    exact ⟨seriesMass_nonneg v, seriesMass_quadratic_bound hv, seriesPrimitive_cubic_bound hv⟩
  · intro N
    exact ⟨sourcePrimitive_peak N, sourcePrimitive_derivative_peak N, sourcePrimitive_second_derivative_peak N⟩

end BfgsVerification.NormalSpike
