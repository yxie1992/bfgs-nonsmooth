import BfgsVerification.LGlobalFailure
import BfgsVerification.LEmbeddingGeometryTargets
import BfgsVerification.LTrialHistory
import BfgsVerification.ScaledCopyQueries

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.LSeedCopies
open SeedOrbit SeedCycle LNormalizedReturn DeterministicLineSearch
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Actual normalized source existence is proved from the literal return map
and Jacobian. This constant selects its witness; it adds no mathematical premise. -/
def data : LFlatten.Data LEmbedding.mu (1/10000) (1/2) :=
  Classical.choose (LGlobalFailure.actual_orbit_data LEmbedding.mu (1/10000) (1/2)
    (by norm_num) (by norm_num) (by norm_num) LEmbedding.localDomain LEmbedding.localDomain_nhds)

theorem data_spec : Tendsto data.state atTop (𝓝 seed) ∧
    (∀k,data.x k∈LEmbedding.localDomain) ∧
    (∀k q,trialPhase q=phase k →
      data.x k+trialLength q • bfgsStep (data.H k) (data.g k) 1∈LEmbedding.localDomain) :=
  Classical.choose_spec (LGlobalFailure.actual_orbit_data LEmbedding.mu (1/10000) (1/2)
    (by norm_num) (by norm_num) (by norm_num) LEmbedding.localDomain LEmbedding.localDomain_nhds)

def run : AdmissibleBFGSRun 2 (LQuadraticSeed.objective LEmbedding.mu) :=
  data.run LEmbedding.mu_pos.le (by norm_num) (by norm_num) (by norm_num)

theorem point_in (k : ℕ) : run.x k∈LEmbedding.localDomain := data_spec.2.1 k

theorem run_point_limit : Tendsto run.x atTop (𝓝 0) := data.point_tendsto data_spec.1

theorem run_matrix_limit : Tendsto run.H atTop (𝓝 0) := data.metric_tendsto data_spec.1

theorem run_value_limit : Tendsto (fun k => LQuadraticSeed.objective LEmbedding.mu (run.x k)) atTop (𝓝 0) :=
  data.value_tendsto LEmbedding.mu_pos.le data_spec.1

theorem run_value_positive (k : ℕ) : 0<LQuadraticSeed.objective LEmbedding.mu (run.x k) := data.value_positive k

theorem run_search (k : ℕ) :
    fromMetric (LQuadraticSeed.objective LEmbedding.mu) (run.x k) (run.H k) run.c₁ run.c₂ 5=
      (some (run.α k),trialHistory (phase k)) := data.actual_search k

theorem run_query_conditions (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    run.x k+trialLength q • bfgsStep (run.H k) (run.g k) 1∈LEmbedding.localDomain ∧
    DifferentiableAt ℝ (LQuadraticSeed.objective LEmbedding.mu)
      (run.x k+trialLength q • bfgsStep (run.H k) (run.g k) 1) :=
  ⟨data_spec.2.2 k q hq,(data.all_trial_derivatives k q hq).differentiableAt⟩

theorem history_query_conditions (k : ℕ)
    (a : ℝ) (ha : a∈(fromMetric (LQuadraticSeed.objective LEmbedding.mu) (run.x k) (run.H k) run.c₁ run.c₂ 5).2) :
    run.x k+a • bfgsStep (run.H k) (run.g k) 1∈LEmbedding.localDomain ∧
    DifferentiableAt ℝ (LQuadraticSeed.objective LEmbedding.mu)
      (run.x k+a • bfgsStep (run.H k) (run.g k) 1) := by
  rw [run_search] at ha
  obtain ⟨q,hq,rfl⟩ := trial_history_witness (phase k) ha
  exact run_query_conditions k q hq

theorem history_query_norm (k : ℕ)
    (a : ℝ) (ha : a∈(fromMetric (LQuadraticSeed.objective LEmbedding.mu) (run.x k) (run.H k) run.c₁ run.c₂ 5).2) :
    ‖run.x k+a • bfgsStep (run.H k) (run.g k) 1‖≤1 :=
  (history_query_conditions k a ha).1.1.le

theorem query_tendsto (q : ℕ → Fin 9) (hq : ∀k,trialPhase (q k)=phase k) :
    Tendsto (fun k => run.x k+trialLength (q k) • bfgsStep (run.H k) (run.g k) 1) atTop (𝓝 0) :=
  data.actual_trials_tendsto data_spec.1 q hq

end BfgsVerification.LSeedCopies
