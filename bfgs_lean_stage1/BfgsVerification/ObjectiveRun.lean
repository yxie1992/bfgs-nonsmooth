import BfgsVerification.ObjectiveDefinitions
import BfgsVerification.PositiveUpdate
import BfgsVerification.DescentBudget
import BfgsVerification.EndToEnd
import BfgsVerification.ConvexAnalysis

/-! Derive the matrix-run invariants and Armijo budgets of an actual accepted
objective-level run. Only initial positive definiteness is assumed. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter

namespace BfgsVerification.AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

theorem positive_invariants (k : ℕ) :
    (R.H k).PosDef ∧ 0 < R.q k ∧
      0 < dot (R.g (k + 1) - R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) :=
  fullBFGS_positive_invariants R.H R.g R.α R.c₂ R.initial_posDef
    R.gradient_nonzero R.alpha_pos R.c₂_lt_one R.weak_wolfe R.update k

theorem positive_definite (k : ℕ) : (R.H k).PosDef := (R.positive_invariants k).1

theorem q_pos (k : ℕ) : 0 < R.q k := (R.positive_invariants k).2.1

theorem curvature_pos (k : ℕ) :
    0 < dot (R.g (k + 1) - R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) :=
  (R.positive_invariants k).2.2

/-- The matrix-run specification is constructed from proved invariants,
with exactly the original matrices, gradients, and accepted lengths. -/
def toFullBFGSRun : FullBFGSRun n where
  H := R.H
  g := R.g
  α := R.α
  positive_definite := R.positive_definite
  alpha_pos := R.alpha_pos
  energy_pos := R.q_pos
  curvature_pos := R.curvature_pos
  update := R.update

@[simp] theorem toFullBFGSRun_q : R.toFullBFGSRun.q = R.q := rfl
@[simp] theorem toFullBFGSRun_d : R.toFullBFGSRun.d = R.d := rfl
@[simp] theorem toFullBFGSRun_beta : R.toFullBFGSRun.beta = R.beta := rfl

include R in
theorem dimension_pos : 0 < n := FullBFGSRun.dimension_pos R.toFullBFGSRun

theorem d_pos (k : ℕ) : 0 < R.d k := mul_pos (R.alpha_pos k) (R.q_pos k)

theorem wolfe_constant_pos : 0 < 1 - R.c₂ := sub_pos.mpr R.c₂_lt_one

theorem beta_lower_bound (k : ℕ) : 1 - R.c₂ ≤ R.beta k :=
  R.toFullBFGSRun.beta_ge_of_weakWolfe k R.c₂ (R.weak_wolfe k)

theorem dot_step_eq_neg_d (k : ℕ) :
    dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) = -R.d k :=
  dot_bfgsStep (R.H k) (R.g k) (R.α k)

theorem curvature_lower_bound (k : ℕ) :
    (1 - R.c₂) * R.d k ≤
      dot (R.g (k + 1) - R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) :=
  curvature_ge_of_weakWolfe (R.H k) (R.g k) (R.g (k + 1)) (R.α k) R.c₂
    (R.weak_wolfe k)

theorem armijo_decrease (k : ℕ) :
    R.c₁ * R.d k ≤ F (R.x k) - F (R.x (k + 1)) := by
  have h := R.armijo k
  rw [R.dot_step_eq_neg_d] at h
  linarith

theorem objective_antitone : Antitone (fun k => F (R.x k)) :=
  DescentBudget.armijo_antitone R.c₁_pos (fun k => (R.d_pos k).le) R.armijo_decrease

theorem objective_le_initial (k : ℕ) : F (R.x k) ≤ F (R.x 0) :=
  R.objective_antitone (Nat.zero_le k)

theorem iterate_mem_initialSublevel (k : ℕ) : R.x k ∈ R.initialSublevel :=
  R.objective_le_initial k

theorem objective_strict_decrease (k : ℕ) : F (R.x (k + 1)) < F (R.x k) := by
  have := R.armijo_decrease k
  have := mul_pos R.c₁_pos (R.d_pos k)
  linarith

theorem finite_budget_le (L : ℝ) (hL : ∀ k, L ≤ F (R.x k)) (J N : ℕ) :
    (∑ i ∈ Finset.range N, R.d (J + i)) ≤ (F (R.x J) - L) / R.c₁ :=
  DescentBudget.armijo_sum_budget_le R.c₁_pos R.armijo_decrease hL J N

theorem summable_predicted_decreases_of_lower_bound
    (L : ℝ) (hL : ∀ k, L ≤ F (R.x k)) : Summable R.d :=
  DescentBudget.armijo_summable R.c₁_pos (fun k => (R.d_pos k).le) R.armijo_decrease hL

theorem predicted_decreases_tendsto_zero_of_lower_bound
    (L : ℝ) (hL : ∀ k, L ≤ F (R.x k)) : Tendsto R.d atTop (𝓝 0) :=
  (R.summable_predicted_decreases_of_lower_bound L hL).tendsto_atTop_zero

theorem tail_budget_le (L : ℝ) (hL : ∀ k, L ≤ F (R.x k)) (J : ℕ) :
    (∑' i, R.d (J + i)) ≤ (F (R.x J) - L) / R.c₁ :=
  DescentBudget.armijo_tail_tsum_le R.c₁_pos (fun k => (R.d_pos k).le)
    R.armijo_decrease hL J

/-- The other side of the basic decrease inequality uses only convexity and
the actual derivative at the current accepted iterate. -/
theorem convexity_decrease_upper (k : ℕ) :
    F (R.x k) - F (R.x (k + 1)) ≤ R.d k := by
  have h := convex_supporting_inequality R.convex (R.hasGradient k) (R.x (k + 1))
  have hs : R.x (k + 1) - R.x k = bfgsStep (R.H k) (R.g k) (R.α k) := by
    rw [R.step]
    abel
  rw [hs, R.dot_step_eq_neg_d] at h
  linarith

/-- Module M's two-sided bound for the actual objective decrease. -/
theorem predicted_decrease_bounds (k : ℕ) :
    R.c₁ * R.d k ≤ F (R.x k) - F (R.x (k + 1)) ∧
      F (R.x k) - F (R.x (k + 1)) ≤ R.d k :=
  ⟨R.armijo_decrease k, R.convexity_decrease_upper k⟩

theorem lower_bound_of_compact_set (K : Set (Vec n)) (hK : IsCompact K)
    (hx : ∀ k, R.x k ∈ K) : ∃ L : ℝ, ∀ k, L ≤ F (R.x k) := by
  obtain ⟨L, hL⟩ := convex_boundedBelow_on_compact R.convex hK
  exact ⟨L, fun k => hL (R.x k) (hx k)⟩

theorem bounded_gradients_of_compact_set (K : Set (Vec n)) (hK : IsCompact K)
    (hx : ∀ k, R.x k ∈ K) : ∃ G : ℝ, 0 < G ∧ ∀ k, sqNorm (R.g k) ≤ G ^ 2 := by
  obtain ⟨G, hG, hbound⟩ := convex_gradient_bound_on_compact R.convex hK
  exact ⟨G, hG, fun k => hbound (R.x k) (hx k) (R.g k) (R.hasGradient k)⟩

theorem lower_bound_of_compact_sublevel (hK : IsCompact R.initialSublevel) :
    ∃ L : ℝ, ∀ k, L ≤ F (R.x k) :=
  R.lower_bound_of_compact_set R.initialSublevel hK R.iterate_mem_initialSublevel

theorem bounded_gradients_of_compact_sublevel (hK : IsCompact R.initialSublevel) :
    ∃ G : ℝ, 0 < G ∧ ∀ k, sqNorm (R.g k) ≤ G ^ 2 :=
  R.bounded_gradients_of_compact_set R.initialSublevel hK R.iterate_mem_initialSublevel

theorem summable_predicted_decreases_of_compact_sublevel
    (hK : IsCompact R.initialSublevel) : Summable R.d := by
  obtain ⟨L, hL⟩ := R.lower_bound_of_compact_sublevel hK
  exact R.summable_predicted_decreases_of_lower_bound L hL

theorem summable_predicted_decreases_of_value_limit (ℓ : ℝ)
    (hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ)) : Summable R.d :=
  DescentBudget.armijo_summable_of_tendsto R.c₁_pos (fun k => (R.d_pos k).le)
    R.armijo_decrease hlim

end BfgsVerification.AdmissibleBFGSRun
