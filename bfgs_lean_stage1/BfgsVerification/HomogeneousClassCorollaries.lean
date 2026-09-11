import BfgsVerification.HomogeneousRelativeInteriorCharacterization
import Mathlib.Analysis.Seminorm

/-! Explicit H.8 class specializations and the stationary constant objective. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace Homogeneous

/-- Finite maxima that are even have nonnegative values and linear zero fibers,
so the source includes every finite polyhedral seminorm representation. -/
theorem relativeInteriorZero_of_even {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (heven : ∀ x, finiteMaxLinear A hA (-x) = finiteMaxLinear A hA x) :
    RelativeInteriorZero A := by
  have hn (x : Vec n) : 0 ≤ finiteMaxLinear A hA x := by
    have hAn := hA
    obtain ⟨a, ha⟩ := hAn
    have h1 := slope_le_finiteMaxLinear A hA ha x
    have h2 := slope_le_finiteMaxLinear A hA ha (-x)
    rw [heven] at h2
    have he : dot a (-x) = -dot a x := dotProduct_neg _ _
    rw [he] at h2
    linarith
  exact relativeInteriorZero_of_positive_on_span A hA
    (positive_on_span_of_zero_neg A hA hn (fun x hx => (heven x).trans hx))

theorem relativeInteriorZero_of_seminorm {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (p : Seminorm ℝ (Vec n)) (hrep : ∀ x, finiteMaxLinear A hA x = p x) :
    RelativeInteriorZero A := by
  apply relativeInteriorZero_of_even A hA
  intro x
  simp only [hrep, map_neg_eq_map]

end Homogeneous
namespace AdmissibleBFGSRun
open Homogeneous AffineProjection

/-- A nonnegative finite max-linear objective with an actual linear zero fiber
converges to the unique initial-metric projection onto that fiber. This proves
the noncoercive-gauge class inclusion without assuming relative interior. -/
theorem maxLinear_linear_zero_fiber_limit {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (hn : ∀ x, 0 ≤ finiteMaxLinear A hA x) (S : Submodule ℝ (Vec n))
    (hS : ∀ x, finiteMaxLinear A hA x = 0 ↔ x ∈ S) :
    ∃ xstar : Vec n, Tendsto R.x atTop (𝓝 xstar) ∧ xstar ∈ S ∧
      ∀ x ∈ S, metricEnergy (R.H 0)⁻¹ (xstar-R.x 0) ≤ metricEnergy (R.H 0)⁻¹ (x-R.x 0) ∧
      (metricEnergy (R.H 0)⁻¹ (x-R.x 0) = metricEnergy (R.H 0)⁻¹ (xstar-R.x 0) ↔ x = xstar) := by
  have hri := (relativeInteriorZero_iff_nonneg_linear_zero_fiber A hA).mpr ⟨hn, S, hS⟩
  obtain ⟨r, U, hU, hspan⟩ := exists_slope_span_coordinates A
  have h := R.maxLinear_relativeInterior_complete A hA hri U hU hspan
  refine ⟨_, h.2.1, (hS _).mp h.2.2.1, ?_⟩
  intro x hx
  exact h.2.2.2.2 x ((hS x).mpr hx)

/-- Every actual seminorm having a finite linear-max representation falls
under H.8, without compactness or an added relative-interior assumption. -/
theorem maxLinear_seminorm_has_limit {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun n (finiteMaxLinear A hA))
    (p : Seminorm ℝ (Vec n)) (hrep : ∀ x, finiteMaxLinear A hA x = p x) :
    ∃ xstar : Vec n, Tendsto R.x atTop (𝓝 xstar) ∧ p xstar = 0 := by
  obtain ⟨xstar, hx, hf⟩ := R.maxLinear_relativeInterior_has_limit A hA
    (relativeInteriorZero_of_seminorm A hA p hrep)
  exact ⟨xstar, hx, by rwa [hrep] at hf⟩

/-- The identically zero objective has no infinite nonstationary admissible
run. Its stationary case is excluded by the actual nonzero-gradient model. -/
theorem zero_objective_no_infinite_run {n : ℕ} (R : AdmissibleBFGSRun n (fun _ => 0)) : False := by
  have hh : PositiveDegreeOne (fun _ : Vec n => (0 : ℝ)) := by intro t ht x; simp
  have hp := R.homogeneous_finite_branch_positive hh 0 tendsto_const_nhds 0
  exact lt_irrefl 0 hp

/-- More generally, an objective written in any expression but identically
zero has no infinite nonzero-gradient admissible run. -/
theorem identically_zero_no_infinite_run {n : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (hzero : ∀ x, F x = 0) : False := by
  exact (R.congrObjective (funext hzero)).zero_objective_no_infinite_run

end AdmissibleBFGSRun
end BfgsVerification
