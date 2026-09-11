import BfgsVerification.ReconstructedFourPieceSeparation

noncomputable section
open scoped BigOperators Topology
open Matrix Set Filter
namespace BfgsVerification
open ReconstructedFourPiece RadialCertificate

/-- Constructed literal four-piece objective and its actual infinite unmodified
full-BFGS failure, for the verified D Armijo–weak-Wolfe parameter range. -/
def ReconstructedFourPieceFailureTarget : Prop :=
  ConvexOn ℝ univ objective ∧
    (∀ b : ℝ, IsCompact {z | objective z ≤ b}) ∧
    optimizer = (![-1, 5] : Vec 2) ∧ objective optimizer = -1 ∧
    (∀ z, -1 ≤ objective z) ∧ (∀ z, objective z = -1 → z = optimizer) ∧
    (∀ i : Fin 3, family.branch i.castSucc optimizer = (![-1, -1, -29 / 4] : Vec 3) i) ∧
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential objective 0 ∧
    ∀ c₁ c₂ : ℝ, ∀ hc₁ : 0 < c₁, ∀ hc₁' : c₁ ≤ 1 / 3,
      ∀ hc : c₁ < c₂, ∀ hc₂ : c₂ < 1,
      let R : AdmissibleBFGSRun 2 objective := run hc₁ hc₁' hc hc₂
      R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
      (∀ k, R.x k = AffineWhitening.point coordinate (SeedOrbit.orbitPoint k)) ∧
      (∀ k, R.H k = valueScale⁻¹ • AffineWhitening.metric coordinate (SeedOrbit.orbitMetric k)) ∧
      (∀ k, R.g k = valueScale • AffineWhitening.gradient coordinate (SeedOrbit.orbitGradient k)) ∧
      (∀ k, R.α k = SeedOrbit.orbitLength k) ∧
      Tendsto R.x atTop (𝓝 0) ∧
      Tendsto (fun k => objective (R.x k)) atTop (𝓝 (valueScale - 1)) ∧
      -1 < valueScale - 1 ∧
      (∀ k, valueScale - 1 < objective (R.x k)) ∧
      (∀ k, objective (R.x (k + 1)) < objective (R.x k))

theorem reconstructedFourPieceFailure : ReconstructedFourPieceFailureTarget := by
  refine ⟨objective_convex, sublevels_compact, rfl, minimum_value, lower_bound,
    fun z hz => unique_optimizer hz, branches_at_optimizer, limit_not_stationary, ?_⟩
  intro c₁ c₂ hc₁ hc₁' hc hc₂
  refine ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    point_tendsto, point_values_tendsto, ?_, point_value_above_limit,
    (run hc₁ hc₁' hc hc₂).objective_strict_decrease⟩
  linarith [valueScale_pos]

/-- Literal repeated predictions and vanishing actual positive secant curvature;
SP and RS fail on the genuine initial sublevel, without assumed eligibility. -/
def ReconstructedSupportingPlaneTarget : Prop :=
  (∀ m : ℕ, ∀ j : Fin 3,
    optimizerIntercept objective optimizer (point (3 * m + j.val)) (gradient (3 * m + j.val)) =
      (![0, 0, 25 / 4] : Vec 3) j) ∧
    (∀ k, HasFDerivAt objective (gradientFunctional (gradient k)) (point k)) ∧
    (∀ k, 0 < secantCurvature (point k) (point (k + 1)) (gradient k) (gradient (k + 1))) ∧
    Tendsto (fun k => secantCurvature (point k) (point (k + 1)) (gradient k) (gradient (k + 1)))
      atTop (𝓝 0) ∧
    ¬ HasInterceptBounds objective {z | objective z ≤ objective (point 0)} optimizer ∧
    ¬ HasRadialSecantBounds objective {z | objective z ≤ objective (point 0)} optimizer

theorem reconstructedSupportingPlane : ReconstructedSupportingPlaneTarget :=
  ⟨point_phase_intercepts, point_hasGradient, secant_pos, secant_tendsto_zero,
    no_intercept_bounds, no_radial_bounds⟩

end BfgsVerification
