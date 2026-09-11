import BfgsVerification.LIdentityRuns

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.LWhitening
open AffineWhitening SeedOrbit LScalarGeometric DeterministicLineSearch
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- One fixed objective and identity initialization for every member of the
actual infinite family; complete line-search traces and uniform locality are
included, with no assumed orbit or matrix convergence. -/
def IdentityFailureTarget (F : Vec 2 → ℝ) : Prop :=
  ∃R : ℕ → AdmissibleBFGSRun 2 F,
    (∀m,(R m).H 0=1) ∧ Tendsto (fun m => (R m).x 0) atTop (𝓝 (0 : Vec 2)) ∧
    (∀m,(R m).c₁=1/10000 ∧ (R m).c₂=1/2 ∧
      Tendsto (R m).x atTop (𝓝 (failureCenter m)) ∧
      Tendsto (R m).H atTop (𝓝 0) ∧
      Tendsto (fun k => F ((R m).x k)) atTop (𝓝 ((scale m)^2*LEmbedding.offset)) ∧
      0<(scale m)^2*LEmbedding.offset ∧
      (0 : Vec 2)∉ConvexSubdifferential.subdifferential F (failureCenter m) ∧
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
          atTop (𝓝 (failureCenter m))) ∧
    ∀U : Set (Vec 2),U∈𝓝 (0 : Vec 2) → ∃N : ℕ,∀m≥N,∀k,(R m).x k∈U ∧
      ∀q : Fin 9,trialPhase q=phase k →
        (R m).x k+trialLength q • bfgsStep ((R m).H k) ((R m).g k) 1∈U


theorem identity_failure {F : Vec 2 → ℝ} (D : LActualCopies.CopyData F) (hF0 : F 0=0) :
    IdentityFailureTarget (AffineWhitening.objective coordinateMatrix F) := by
  refine ⟨failureFamily D,failure_initial D,failure_starts D,?_,failure_uniform_locality D⟩
  intro m
  refine ⟨rfl,rfl,failure_point_limit D m,failure_matrix_limit D m,failure_value_limit D m,
    mul_pos (sq_pos_of_pos (scale_pos m)) LEmbedding.offset_pos,
    failure_centers_nonstationary D hF0 m,?_,failure_trial D m,failure_trials_limit D m⟩
  intro k
  exact ⟨failure_values_above D m k,(failureFamily D m).objective_strict_decrease k,rfl,
    failure_search D m k,(failure_strict_accept D m k).1,(failure_strict_accept D m k).2⟩

def SmoothIdentityFailureTarget : Prop := IdentityFailureTarget smoothObjective

theorem smoothIdentityFailure : SmoothIdentityFailureTarget :=
  identity_failure LActualCopies.smoothData LEmbedding.objective_zero

def StepIdentityFailureTarget : Prop := IdentityFailureTarget stepObjective

theorem stepIdentityFailure : StepIdentityFailureTarget :=
  identity_failure LActualCopies.stepData LStepEmbedding.objective_zero

end BfgsVerification.LWhitening
