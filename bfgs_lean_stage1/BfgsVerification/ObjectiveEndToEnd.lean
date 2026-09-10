import BfgsVerification.ObjectiveRun
import BfgsVerification.ObjectiveTargets

/-!
# Objective-level reciprocal-growth exports

The accepted run has a finite convex objective and actual gradients at accepted
points, initial-only SPD, positive step lengths, and Armijo--weak-Wolfe. Matrix
invariants and the scalar hierarchy are derived. Where compactness is assumed,
the gradient and predicted-decrease budgets are also derived. No iterate or
matrix convergence is assumed, and objective optimality is not concluded.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace BfgsVerification

/-- Objective-level M.2, retaining its weaker vanishing-decrease hypothesis. -/
theorem objectiveReciprocalGrowth : ObjectiveReciprocalGrowthTarget := by
  intro n F R G hG hg hd
  exact reciprocalGrowth n R.toFullBFGSRun G (1 - R.c₂)
    hG R.wolfe_constant_pos hg R.beta_lower_bound hd

/-- Armijo derives summability from a lower bound along the actual objective run. -/
theorem objectiveLowerBoundGrowth : ObjectiveLowerBoundGrowthTarget := by
  intro n F R G L hG hg hL
  have hs := R.summable_predicted_decreases_of_lower_bound L hL
  have hm := objectiveReciprocalGrowth n F R G hG hg hs.tendsto_atTop_zero
  refine ⟨hs, hm.1, hm.2, ?_⟩
  exact superquadraticReciprocalGrowth n R.toFullBFGSRun G (1 - R.c₂)
    hG R.wolfe_constant_pos hg R.beta_lower_bound hs

/-- A compact initial sublevel discharges both the gradient-bound and budget
hypotheses for the actual infinite admissible full-BFGS run. -/
theorem compactObjectiveGrowth : CompactObjectiveGrowthTarget := by
  intro n F R hK
  obtain ⟨G, hG, hg⟩ := R.bounded_gradients_of_compact_sublevel hK
  obtain ⟨L, hL⟩ := R.lower_bound_of_compact_sublevel hK
  exact ⟨⟨G, hG, hg⟩, objectiveLowerBoundGrowth n F R G L hG hg hL⟩

/-- The exact finite-horizon estimate with its actual infinite tail sum.
Summability is derived from Armijo and the lower bound supplied here. -/
theorem objectiveFiniteHorizon_of_lower_bound {n : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (G L : ℝ) (hG : 0 < G)
    (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2) (hL : ∀ k, L ≤ F (R.x k)) :
    ObjectiveFiniteHorizonBound R G := by
  intro J m hm η hη
  exact finiteHorizon R.toFullBFGSRun G (1 - R.c₂) hG R.wolfe_constant_pos
    hg R.beta_lower_bound (R.summable_predicted_decreases_of_lower_bound L hL)
    J m hm η hη

/-- On a compact initial sublevel, a valid constant for the exact finite-horizon
bound exists as a theorem, rather than as an additional assumed bound. -/
theorem compactObjectiveFiniteHorizon : CompactObjectiveFiniteHorizonTarget := by
  intro n F R hK
  obtain ⟨G, hG, hg⟩ := R.bounded_gradients_of_compact_sublevel hK
  obtain ⟨L, hL⟩ := R.lower_bound_of_compact_sublevel hK
  exact ⟨G, hG, hg, objectiveFiniteHorizon_of_lower_bound R G L hG hg hL⟩

/-- The source's finite-limiting-value branch, with no assumed iterate or matrix
limit. The objective limit need not be the minimum. -/
theorem objectiveGrowth_of_value_limit {n : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (G ℓ : ℝ) (hG : 0 < G)
    (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2)
    (hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ)) :
    Summable R.d ∧
    Tendsto (reciprocalGeometricMean R.q) atTop atTop ∧
    Tendsto (reciprocalMean R.q) atTop atTop ∧
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, (R.q k)⁻¹) / (N : ℝ) ^ 2)
      atTop atTop := by
  apply objectiveLowerBoundGrowth n F R G ℓ hG hg
  exact DescentBudget.armijo_limit_le R.c₁_pos (fun k => (R.d_pos k).le)
    R.armijo_decrease hlim

end BfgsVerification
