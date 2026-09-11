import BfgsVerification.LSeedCopies
import BfgsVerification.LStepEmbeddingTargets

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.LActualCopies
open SeedOrbit SeedCycle LScalarGeometric DeterministicLineSearch
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev CopyData (F : Vec 2 → ℝ) := ScaledCopy.Data (LQuadraticSeed.objective LEmbedding.mu) F
  LEmbedding.center LEmbedding.offset LEmbedding.localDomain

def smoothData : CopyData LEmbedding.objective where
  convex := LEmbedding.objective_convex
  open_domain := LEmbedding.localDomain_open
  model m y hy := LEmbedding.local_model m hy

def stepData : CopyData LStepEmbedding.objective where
  convex := LStepEmbedding.objective_convex
  open_domain := LEmbedding.localDomain_open
  model m y hy := LStepEmbedding.objective_copy m (LStepEmbedding.copyNeighborhood_of_norm hy.1 hy.2)

def family {F : Vec 2 → ℝ} (D : CopyData F) (m : ℕ) : AdmissibleBFGSRun 2 F :=
  D.run LSeedCopies.run LSeedCopies.point_in m

theorem point_formula {F : Vec 2 → ℝ} (D : CopyData F) (m k : ℕ) :
    (family D m).x k=LEmbedding.copyCenter m+scale m • LSeedCopies.run.x k := rfl

theorem matrix_formula {F : Vec 2 → ℝ} (D : CopyData F) (m k : ℕ) :
    (family D m).H k=LSeedCopies.run.H k := rfl

theorem gradient_formula {F : Vec 2 → ℝ} (D : CopyData F) (m k : ℕ) :
    (family D m).g k=scale m • LSeedCopies.run.g k := rfl

theorem actual_parameters {F : Vec 2 → ℝ} (D : CopyData F) (m : ℕ) :
    (family D m).c₁=1/10000 ∧ (family D m).c₂=1/2 ∧
    ∀k,(family D m).α k=length (phase k) := ⟨rfl,rfl,fun _ => rfl⟩

theorem point_limit {F : Vec 2 → ℝ} (D : CopyData F) (m : ℕ) :
    Tendsto (family D m).x atTop (𝓝 (LEmbedding.copyCenter m)) :=
  D.run_tendsto LSeedCopies.run LSeedCopies.point_in LSeedCopies.run_point_limit m

theorem matrix_limit {F : Vec 2 → ℝ} (D : CopyData F) (m : ℕ) :
    Tendsto (family D m).H atTop (𝓝 0) := LSeedCopies.run_matrix_limit

theorem value_limit {F : Vec 2 → ℝ} (D : CopyData F) (m : ℕ) :
    Tendsto (fun k => F ((family D m).x k)) atTop (𝓝 ((scale m)^2*LEmbedding.offset)) :=
  D.run_values_tendsto LSeedCopies.run LSeedCopies.point_in LSeedCopies.run_value_limit m

theorem values_above_limit {F : Vec 2 → ℝ} (D : CopyData F) (m k : ℕ) :
    (scale m)^2*LEmbedding.offset<F ((family D m).x k) :=
  D.run_values_above_limit LSeedCopies.run LSeedCopies.point_in LSeedCopies.run_value_positive m k

theorem starts_tendsto {F : Vec 2 → ℝ} (D : CopyData F) :
    Tendsto (fun m => (family D m).x 0) atTop (𝓝 (0 : Vec 2)) :=
  D.starts_tendsto_zero LSeedCopies.run LSeedCopies.point_in

theorem actual_search {F : Vec 2 → ℝ} (D : CopyData F) (m k : ℕ) :
    fromMetric F ((family D m).x k) ((family D m).H k) (1/10000) (1/2) 5=
      (some ((family D m).α k),trialHistory (phase k)) := by
  have hh := D.search_transfer LSeedCopies.run LSeedCopies.point_in 5 LSeedCopies.history_query_conditions m k
  exact hh.trans (LSeedCopies.run_search k)

theorem trial_hasGradient {F : Vec 2 → ℝ} (D : CopyData F) (m k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    HasFDerivAt F (gradientFunctional (scale m • coordinateGradient (LQuadraticSeed.objective LEmbedding.mu)
      (LSeedCopies.run.x k+trialLength q • bfgsStep (LSeedCopies.run.H k) (LSeedCopies.run.g k) 1)))
      ((family D m).x k+trialLength q • bfgsStep ((family D m).H k) ((family D m).g k) 1) := by
  obtain ⟨hU,hd⟩ := LSeedCopies.run_query_conditions k q hq
  exact D.query_hasGradient LSeedCopies.run LSeedCopies.point_in m k (trialLength q) hU hd

theorem trial_value_positive {F : Vec 2 → ℝ} (D : CopyData F) (m k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    0<F ((family D m).x k+trialLength q • bfgsStep ((family D m).H k) ((family D m).g k) 1) := by
  have hh := D.query_value LSeedCopies.run LSeedCopies.point_in m k (trialLength q)
    (LSeedCopies.run_query_conditions k q hq).1
  unfold family
  rw [hh]
  have hp := LSeedCopies.data.all_trial_values_positive k q hq
  exact mul_pos (sq_pos_of_pos (scale_pos m)) (add_pos LEmbedding.offset_pos hp)

theorem trials_limit {F : Vec 2 → ℝ} (D : CopyData F) (m : ℕ) (q : ℕ → Fin 9)
    (hq : ∀k,trialPhase (q k)=phase k) :
    Tendsto (fun k => (family D m).x k+trialLength (q k) •
      bfgsStep ((family D m).H k) ((family D m).g k) 1) atTop (𝓝 (LEmbedding.copyCenter m)) :=
  D.queries_tendsto LSeedCopies.run LSeedCopies.point_in m (fun k => trialLength (q k))
    (LSeedCopies.query_tendsto q hq)

theorem strict_accept {F : Vec 2 → ℝ} (D : CopyData F) (m k : ℕ) :
    F ((family D m).x (k+1))<F ((family D m).x k)+
      (1/10000)*dot ((family D m).g k) (bfgsStep ((family D m).H k) ((family D m).g k) ((family D m).α k)) ∧
    (1/2)*dot ((family D m).g k) (bfgsStep ((family D m).H k) ((family D m).g k) ((family D m).α k))<
      dot ((family D m).g (k+1)) (bfgsStep ((family D m).H k) ((family D m).g k) ((family D m).α k)) := by
  have hv (j : ℕ) : F ((family D m).x j)=(scale m)^2*(LEmbedding.offset+
      LQuadraticSeed.objective LEmbedding.mu (LSeedCopies.run.x j)) :=
    D.run_value LSeedCopies.run LSeedCopies.point_in m j
  have hp (j : ℕ) : dot ((family D m).g j)
      (bfgsStep ((family D m).H k) ((family D m).g k) ((family D m).α k))=
      (scale m)^2*dot (LSeedCopies.run.g j)
        (bfgsStep (LSeedCopies.run.H k) (LSeedCopies.run.g k) (LSeedCopies.run.α k)) :=
    TranslatedRun.scaled_pairing LSeedCopies.run (scale m) j k
  obtain ⟨ha,hw⟩ := LSeedCopies.data.strict_accept k
  rw [hv,hv,hp,hp]
  constructor
  · have hh := mul_lt_mul_of_pos_left ha (sq_pos_of_pos (scale_pos m))
    change (scale m)^2*LQuadraticSeed.objective LEmbedding.mu (LSeedCopies.run.x (k+1))<
      (scale m)^2*(LQuadraticSeed.objective LEmbedding.mu (LSeedCopies.run.x k)+
        (1/10000)*dot (LSeedCopies.run.g k) (bfgsStep (LSeedCopies.run.H k) (LSeedCopies.run.g k) (LSeedCopies.run.α k))) at hh
    nlinarith
  · have hh := mul_lt_mul_of_pos_left hw (sq_pos_of_pos (scale_pos m))
    change (scale m)^2*((1/2)*dot (LSeedCopies.run.g k)
      (bfgsStep (LSeedCopies.run.H k) (LSeedCopies.run.g k) (LSeedCopies.run.α k)))<
      (scale m)^2*dot (LSeedCopies.run.g (k+1))
        (bfgsStep (LSeedCopies.run.H k) (LSeedCopies.run.g k) (LSeedCopies.run.α k)) at hh
    nlinarith

theorem centers_nonstationary {F : Vec 2 → ℝ} (D : CopyData F) (hF0 : F 0=0) (m : ℕ) :
    (0 : Vec 2)∉ConvexSubdifferential.subdifferential F (LEmbedding.copyCenter m) := by
  have hv : F (LEmbedding.copyCenter m)=(scale m)^2*LEmbedding.offset := by
    simpa only [smul_zero,add_zero,LQuadraticSeed.objective_zero] using
      D.model m (0 : Vec 2) LEmbedding.zero_mem_localDomain
  intro hh
  have hm := ConvexSubdifferential.zero_mem_iff_global_minimum.mp hh (0 : Vec 2)
  rw [hv,hF0] at hm
  exact (not_le_of_gt (mul_pos (sq_pos_of_pos (scale_pos m)) LEmbedding.offset_pos)) hm

end BfgsVerification.LActualCopies
