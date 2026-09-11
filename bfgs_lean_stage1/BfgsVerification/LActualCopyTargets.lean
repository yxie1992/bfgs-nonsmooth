import BfgsVerification.LActualCopyLocality
import BfgsVerification.LEmbeddingSourceDetails

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.LActualCopies
open SeedOrbit SeedCycle LScalarGeometric DeterministicLineSearch
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The literal infinite local-copy failure, with one fixed SPD initial matrix
for all starts. Identity initialization is a further fixed affine normalization. -/
def FixedMetricFailureTarget (F : Vec 2 → ℝ) : Prop :=
  ∃B : Mat 2,B.PosDef ∧ ∃R : ℕ → AdmissibleBFGSRun 2 F,
    (∀m,(R m).H 0=B) ∧ Tendsto (fun m => (R m).x 0) atTop (𝓝 (0 : Vec 2)) ∧
    (∀m,(R m).c₁=1/10000 ∧ (R m).c₂=1/2 ∧
      Tendsto (R m).x atTop (𝓝 (LEmbedding.copyCenter m)) ∧
      Tendsto (R m).H atTop (𝓝 0) ∧
      Tendsto (fun k => F ((R m).x k)) atTop (𝓝 ((scale m)^2*LEmbedding.offset)) ∧
      0<(scale m)^2*LEmbedding.offset ∧
      (0 : Vec 2)∉ConvexSubdifferential.subdifferential F (LEmbedding.copyCenter m) ∧
      (∀k,(scale m)^2*LEmbedding.offset<F ((R m).x k) ∧
        F ((R m).x (k+1))<F ((R m).x k) ∧ (R m).α k=length (phase k) ∧
        fromMetric F ((R m).x k) ((R m).H k) (1/10000) (1/2) 5=
          (some ((R m).α k),trialHistory (phase k)) ∧
        F ((R m).x (k+1))<F ((R m).x k)+
          (1/10000)*dot ((R m).g k) (bfgsStep ((R m).H k) ((R m).g k) ((R m).α k)) ∧
        (1/2)*dot ((R m).g k) (bfgsStep ((R m).H k) ((R m).g k) ((R m).α k))<
          dot ((R m).g (k+1)) (bfgsStep ((R m).H k) ((R m).g k) ((R m).α k))) ∧
      (∀k q,trialPhase q=phase k →
        DifferentiableAt ℝ F ((R m).x k+trialLength q • bfgsStep ((R m).H k) ((R m).g k) 1) ∧
        0<F ((R m).x k+trialLength q • bfgsStep ((R m).H k) ((R m).g k) 1)) ∧
      ∀q : ℕ → Fin 9,(∀k,trialPhase (q k)=phase k) →
        Tendsto (fun k => (R m).x k+trialLength (q k) • bfgsStep ((R m).H k) ((R m).g k) 1)
          atTop (𝓝 (LEmbedding.copyCenter m))) ∧
    ∀U : Set (Vec 2),U∈𝓝 (0 : Vec 2) → ∃N : ℕ,∀m≥N,∀k,(R m).x k∈U ∧
      ∀q : Fin 9,trialPhase q=phase k →
        (R m).x k+trialLength q • bfgsStep ((R m).H k) ((R m).g k) 1∈U

theorem fixed_metric_failure {F : Vec 2 → ℝ} (D : CopyData F) (hF0 : F 0=0) : FixedMetricFailureTarget F := by
  refine ⟨LSeedCopies.run.H 0,LSeedCopies.run.initial_posDef,family D,fun _ => rfl,
    starts_tendsto D,?_,uniform_locality D⟩
  intro m
  refine ⟨rfl,rfl,point_limit D m,matrix_limit D m,value_limit D m,
    mul_pos (sq_pos_of_pos (scale_pos m)) LEmbedding.offset_pos,centers_nonstationary D hF0 m,?_,?_,trials_limit D m⟩
  · intro k
    exact ⟨values_above_limit D m k,(family D m).objective_strict_decrease k,rfl,
      actual_search D m k,(strict_accept D m k).1,(strict_accept D m k).2⟩
  · intro k q hq
    exact ⟨(trial_hasGradient D m k q hq).differentiableAt,trial_value_positive D m k q hq⟩

/-- Literal four-C1,1-branch objective; all geometric and trajectory premises
have been discharged by actual proofs. -/
def SmoothFailureTarget : Prop := FixedMetricFailureTarget LEmbedding.objective

theorem smoothFailure : SmoothFailureTarget := fixed_metric_failure smoothData LEmbedding.objective_zero

/-- Literal countably affine residual objective; its actual Hessian is mu*I
at every differentiability point, as separately established in its geometry. -/
def StepFailureTarget : Prop := FixedMetricFailureTarget LStepEmbedding.objective

theorem stepFailure : StepFailureTarget := fixed_metric_failure stepData LStepEmbedding.objective_zero

end BfgsVerification.LActualCopies
