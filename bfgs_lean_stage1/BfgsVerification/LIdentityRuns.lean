import BfgsVerification.LWhiteningGeometry
import BfgsVerification.AffineWhiteningLimits
import BfgsVerification.LActualCopyTargets

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.LWhitening
open AffineWhitening SeedOrbit LScalarGeometric DeterministicLineSearch
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {F : Vec 2 → ℝ}

def failureFamily (D : LActualCopies.CopyData F) (m : ℕ) :
    AdmissibleBFGSRun 2 (objective coordinateMatrix F) :=
  run coordinateMatrix coordinateMatrix_invertible (LActualCopies.family D m)

def failureCenter (m : ℕ) : Vec 2 := point coordinateMatrix (LEmbedding.copyCenter m)

theorem failure_initial (D : LActualCopies.CopyData F) (m : ℕ) : (failureFamily D m).H 0=1 :=
  fixed_initial_whitening initialMetric initialMetric_posDef (LActualCopies.family D m) rfl

theorem failure_point_limit (D : LActualCopies.CopyData F) (m : ℕ) :
    Tendsto (failureFamily D m).x atTop (𝓝 (failureCenter m)) :=
  point_limit coordinateMatrix (LActualCopies.point_limit D m)

theorem failure_matrix_limit (D : LActualCopies.CopyData F) (m : ℕ) :
    Tendsto (failureFamily D m).H atTop (𝓝 0) :=
  metric_limit_zero coordinateMatrix (LActualCopies.matrix_limit D m)

theorem failure_value_limit (D : LActualCopies.CopyData F) (m : ℕ) :
    Tendsto (fun k => objective coordinateMatrix F ((failureFamily D m).x k))
      atTop (𝓝 ((scale m)^2*LEmbedding.offset)) := by
  simpa only [failureFamily,run_value] using LActualCopies.value_limit D m

theorem failure_values_above (D : LActualCopies.CopyData F) (m k : ℕ) :
    (scale m)^2*LEmbedding.offset<objective coordinateMatrix F ((failureFamily D m).x k) := by
  simpa only [failureFamily,run_value] using LActualCopies.values_above_limit D m k

theorem failure_starts (D : LActualCopies.CopyData F) :
    Tendsto (fun m => (failureFamily D m).x 0) atTop (𝓝 (0 : Vec 2)) :=
  starts_limit_zero coordinateMatrix coordinateMatrix_invertible (LActualCopies.family D)
    (LActualCopies.starts_tendsto D)

theorem failure_centers_nonstationary (D : LActualCopies.CopyData F) (hF0 : F 0=0) (m : ℕ) :
    (0 : Vec 2)∉ConvexSubdifferential.subdifferential (objective coordinateMatrix F) (failureCenter m) :=
  nonstationary_whitening coordinateMatrix coordinateMatrix_invertible _
    (LActualCopies.centers_nonstationary D hF0 m)

theorem failure_search (D : LActualCopies.CopyData F) (m k : ℕ) :
    fromMetric (objective coordinateMatrix F) ((failureFamily D m).x k) ((failureFamily D m).H k)
      (1/10000) (1/2) 5=(some ((failureFamily D m).α k),trialHistory (phase k)) := by
  change fromMetric (objective coordinateMatrix F) (point coordinateMatrix ((LActualCopies.family D m).x k))
    (metric coordinateMatrix ((LActualCopies.family D m).H k)) _ _ _=_
  rw [fromMetric_equiv _ coordinateMatrix_invertible]
  exact LActualCopies.actual_search D m k

theorem failure_strict_accept (D : LActualCopies.CopyData F) (m k : ℕ) :
    objective coordinateMatrix F ((failureFamily D m).x (k+1))<
      objective coordinateMatrix F ((failureFamily D m).x k)+
      (1/10000)*dot ((failureFamily D m).g k)
        (bfgsStep ((failureFamily D m).H k) ((failureFamily D m).g k) ((failureFamily D m).α k)) ∧
    (1/2)*dot ((failureFamily D m).g k)
      (bfgsStep ((failureFamily D m).H k) ((failureFamily D m).g k) ((failureFamily D m).α k))<
      dot ((failureFamily D m).g (k+1))
        (bfgsStep ((failureFamily D m).H k) ((failureFamily D m).g k) ((failureFamily D m).α k)) :=
  (strict_accept_equiv coordinateMatrix coordinateMatrix_invertible (LActualCopies.family D m) k).mpr
    (LActualCopies.strict_accept D m k)

theorem failure_trial (D : LActualCopies.CopyData F) (m k : ℕ) (q : Fin 9)
    (hq : trialPhase q=phase k) :
    DifferentiableAt ℝ (objective coordinateMatrix F)
      ((failureFamily D m).x k+trialLength q • bfgsStep ((failureFamily D m).H k) ((failureFamily D m).g k) 1) ∧
    0<objective coordinateMatrix F
      ((failureFamily D m).x k+trialLength q • bfgsStep ((failureFamily D m).H k) ((failureFamily D m).g k) 1) := by
  change DifferentiableAt ℝ (objective coordinateMatrix F)
    (point coordinateMatrix ((LActualCopies.family D m).x k)+trialLength q •
      bfgsStep (metric coordinateMatrix ((LActualCopies.family D m).H k))
        (gradient coordinateMatrix ((LActualCopies.family D m).g k)) 1) ∧ _
  rw [query_equiv _ coordinateMatrix_invertible]
  constructor
  · exact (differentiableAt_equiv coordinateMatrix coordinateMatrix_invertible F _).mpr
      (LActualCopies.trial_hasGradient D m k q hq).differentiableAt
  · simpa only [failureFamily,run_x,run_H,run_g,query_equiv _ coordinateMatrix_invertible,
      AffineWhitening.objective,map_point _ coordinateMatrix_invertible] using LActualCopies.trial_value_positive D m k q hq

theorem failure_trials_limit (D : LActualCopies.CopyData F) (m : ℕ) (q : ℕ → Fin 9)
    (hq : ∀k,trialPhase (q k)=phase k) :
    Tendsto (fun k => (failureFamily D m).x k+trialLength (q k) •
      bfgsStep ((failureFamily D m).H k) ((failureFamily D m).g k) 1) atTop (𝓝 (failureCenter m)) :=
  queries_limit coordinateMatrix coordinateMatrix_invertible _ _ _ _ _ (LActualCopies.trials_limit D m q hq)

theorem failure_uniform_locality (D : LActualCopies.CopyData F) (U : Set (Vec 2)) (hU : U∈𝓝 (0 : Vec 2)) :
    ∃N : ℕ,∀m≥N,∀k,(failureFamily D m).x k∈U ∧ ∀q : Fin 9,trialPhase q=phase k →
      (failureFamily D m).x k+trialLength q • bfgsStep ((failureFamily D m).H k) ((failureFamily D m).g k) 1∈U :=
  uniform_locality coordinateMatrix coordinateMatrix_invertible (LActualCopies.family D)
    trialLength (fun k q => trialPhase q=phase k) (LActualCopies.uniform_locality D) U hU

end BfgsVerification.LWhitening
