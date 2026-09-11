import BfgsVerification.Localization
import BfgsVerification.ObjectiveEnergy

/-!
# Localization consequences for objective and iterate convergence

A finite convex objective with an attained unique minimizer converts convergence
of objective values to convergence of the points, through the proved low-sublevel
basin. The full-BFGS criterion below still explicitly assumes the displayed
quadratic cumulative reference-correction budget. It is not a universal
convergence theorem for finite convex BFGS objectives.
-/

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification.Localization

/-- Converging objective values force convergence to an attained unique
minimizer. Compactness or convergence of the points is not assumed. -/
theorem tendsto_unique_minimizer_of_values
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → ℝ} (hF : ConvexOn ℝ Set.univ F) (xStar : E)
    (hmin : ∀ x, F xStar ≤ F x)
    (hunique : ∀ x, F x = F xStar → x = xStar)
    {ι : Type*} {l : Filter ι} {x : ι → E}
    (hvalues : Tendsto (fun i => F (x i)) l (𝓝 (F xStar))) :
    Tendsto x l (𝓝 xStar) := by
  apply Filter.tendsto_def.mpr
  intro U hU
  obtain ⟨δ, hδ, hsub⟩ := neighborhood_basin hF xStar hmin hunique hU
  filter_upwards [hvalues.eventually_le_const (by linarith : F xStar < F xStar + δ)]
    with i hi
  exact hsub hi

end BfgsVerification.Localization

namespace BfgsVerification.AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- Objective convergence for the actual accepted run lifts to iterate
convergence when the attained minimizer is unique. -/
theorem iterates_tendsto_unique_min_of_values (xStar : Vec n)
    (hmin : ∀ x, F xStar ≤ F x)
    (hunique : ∀ x, F x = F xStar → x = xStar)
    (hvalues : Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xStar))) :
    Tendsto R.x atTop (𝓝 xStar) :=
  Localization.tendsto_unique_minimizer_of_values R.convex xStar hmin hunique hvalues

/-- A trajectory criterion for both value and iterate convergence. The attained
unique minimizer supplies compact sublevels and bounded gradients; the quadratic
cumulative reference-correction budget remains an explicit assumption. -/
theorem convergence_of_quadratic_corrections_unique_minimizer (xStar : Vec n)
    (hmin : ∀ x, F xStar ≤ F x)
    (hunique : ∀ x, F x = F xStar → x = xStar) (C : ℝ)
    (hcor : ∀ᶠ N in atTop,
      (∑ k ∈ Finset.range N, R.referenceCorrection xStar k) ≤ C * (N : ℝ) ^ 2) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xStar)) ∧
      Tendsto R.x atTop (𝓝 xStar) := by
  have hK := R.initialSublevel_compact_of_unique_minimizer xStar hmin hunique
  obtain ⟨G, hG, hg⟩ := R.bounded_gradients_of_compact_sublevel hK
  have hvalues := R.objective_tendsto_min_of_quadratic_corrections xStar hmin G hG hg C hcor
  exact ⟨hvalues, R.iterates_tendsto_unique_min_of_values xStar hmin hunique hvalues⟩

end BfgsVerification.AdmissibleBFGSRun
