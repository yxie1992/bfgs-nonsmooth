import BfgsVerification.LFlattenRun

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.LFlatten
open SeedOrbit SeedCycle LNormalizedReturn LNormalizedOracle DeterministicLineSearch
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem tendsto_finite_choice {α β E : Type*} [Finite β] [TopologicalSpace E]
    {l : Filter α} {f : β → α → E} {b : E} (hf : ∀ j, Tendsto (f j) l (𝓝 b)) (p : α → β) :
    Tendsto (fun k => f (p k) k) l (𝓝 b) := by
  rw [tendsto_def]
  intro S hS
  exact (eventually_all.mpr (fun j => hf j hS)).mono (fun k hk => hk (p k))

theorem physicalPoint_continuous_seed (μ : ℝ) (j : Fin 3) :
    ContinuousAt (fun w => physicalPoint μ w j) seed :=
  (analytic_scale seed).continuousAt.smul (analytic_phasePoint_seed μ j).continuousAt

theorem physicalMetric_continuous_seed (μ : ℝ) (j : Fin 3) :
    ContinuousAt (fun w => physicalMetric μ w j) seed :=
  (analytic_scale seed).continuousAt.smul (analytic_phaseMetric_seed μ j).continuousAt

def physicalQuery (μ : ℝ) (w : State) (q : Fin 9) : Vec 2 :=
  scale w • trialPoint μ w (trialPhase q) (trialLength q)

theorem physicalQuery_continuous_seed (μ : ℝ) (q : Fin 9) :
    ContinuousAt (fun w => physicalQuery μ w q) seed :=
  (analytic_scale seed).continuousAt.smul (analytic_trialPoint_seed μ (trialPhase q) (trialLength q)).continuousAt

namespace Data
variable {μ c₁ c₂ : ℝ}

theorem point_tendsto (D : Data μ c₁ c₂) (ht : Tendsto D.state atTop (𝓝 seed)) :
    Tendsto D.x atTop (𝓝 0) := by
  apply tendsto_finite_choice (f:=fun j k => physicalPoint μ (D.state (period k)) j) (p:=phase)
  intro j
  simpa only [physicalPoint,seed_scale,zero_smul] using
    (physicalPoint_continuous_seed μ j).tendsto.comp (ht.comp period_tendsto)

theorem metric_tendsto (D : Data μ c₁ c₂) (ht : Tendsto D.state atTop (𝓝 seed)) :
    Tendsto D.H atTop (𝓝 0) := by
  apply tendsto_finite_choice (f:=fun j k => physicalMetric μ (D.state (period k)) j) (p:=phase)
  intro j
  simpa only [physicalMetric,seed_scale,zero_smul] using
    (physicalMetric_continuous_seed μ j).tendsto.comp (ht.comp period_tendsto)

theorem value_tendsto (D : Data μ c₁ c₂) (hμ : 0≤μ) (ht : Tendsto D.state atTop (𝓝 seed)) :
    Tendsto (fun k => LQuadraticSeed.objective μ (D.x k)) atTop (𝓝 0) := by
  simpa only [LQuadraticSeed.objective_zero] using
    (convex_continuous (LQuadraticSeed.objective_convex hμ)).continuousAt.tendsto.comp (D.point_tendsto ht)

theorem queries_tendsto (D : Data μ c₁ c₂) (ht : Tendsto D.state atTop (𝓝 seed))
    (q : ℕ → Fin 9) :
    Tendsto (fun k => physicalQuery μ (D.state (period k)) (q k)) atTop (𝓝 0) := by
  apply tendsto_finite_choice (f:=fun j k => physicalQuery μ (D.state (period k)) j) (p:=q)
  intro j
  simpa only [physicalQuery,seed_scale,zero_smul] using
    (physicalQuery_continuous_seed μ j).tendsto.comp (ht.comp period_tendsto)

theorem actual_trial_eq (D : Data μ c₁ c₂) (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    D.x k+trialLength q • bfgsStep (D.H k) (D.g k) 1=
      physicalQuery μ (D.state (period k)) q := by
  rw [D.gradient_eq]
  change physicalPoint μ (D.state (period k)) (phase k)+trialLength q •
    bfgsStep (physicalMetric μ (D.state (period k)) (phase k))
      (phaseGradient μ (D.state (period k)) (phase k)) 1=_
  rw [physical_trial]
  simp only [physicalQuery,hq]

theorem actual_trials_tendsto (D : Data μ c₁ c₂) (ht : Tendsto D.state atTop (𝓝 seed))
    (q : ℕ → Fin 9) (hq : ∀ k, trialPhase (q k)=phase k) :
    Tendsto (fun k => D.x k+trialLength (q k) • bfgsStep (D.H k) (D.g k) 1) atTop (𝓝 0) := by
  simp_rw [D.actual_trial_eq _ _ (hq _)]
  exact D.queries_tendsto ht q

end Data
end BfgsVerification.LFlatten
