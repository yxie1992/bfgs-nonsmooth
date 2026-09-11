import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Analytic.Basic

noncomputable section
open scoped Topology BigOperators BoundedContinuousFunction
open Set Filter
namespace BfgsVerification.BoundedAnalytic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficient_bound {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (v : Fin n → (ℕ →ᵇ E)) (k : ℕ) :
    ‖p (fun i => v i k)‖≤‖p‖*∏ i, ‖v i‖ := by
  apply (p.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg p)
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (v i).norm_coe_le_norm k)

def coefficientValue {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (v : Fin n → (ℕ →ᵇ E)) : ℕ →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun k => p (fun i => v i k)) (‖p‖*∏ i, ‖v i‖) (coefficient_bound p v)

theorem coefficientValue_apply {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (v : Fin n → (ℕ →ᵇ E)) (k : ℕ) : coefficientValue p v k=p (fun i => v i k) := rfl

theorem coefficientValue_norm {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (v : Fin n → (ℕ →ᵇ E)) : ‖coefficientValue p v‖≤‖p‖*∏ i, ‖v i‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  exact coefficient_bound p v

theorem eval_update {n : ℕ} [DecidableEq (Fin n)] (v : Fin n → (ℕ →ᵇ E)) (i : Fin n) (a : ℕ →ᵇ E) (k : ℕ) :
    (fun j => (Function.update v i a j) k)=Function.update (fun j => v j k) i (a k) := by
  funext j
  by_cases hj : j=i
  · subst j; simp
  · simp [Function.update_of_ne hj]

def coefficientMap {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) :
    MultilinearMap ℝ (fun _ : Fin n => (ℕ →ᵇ E)) (ℕ →ᵇ F) where
  toFun := coefficientValue p
  map_update_add' v i a b := by
    ext k
    simp only [coefficientValue_apply,eval_update,BoundedContinuousFunction.add_apply]
    exact p.map_update_add _ _ _ _
  map_update_smul' v i c a := by
    ext k
    simp only [coefficientValue_apply,eval_update,BoundedContinuousFunction.smul_apply]
    exact p.map_update_smul _ _ _ _

def coefficientLift {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => (ℕ →ᵇ E)) (ℕ →ᵇ F) :=
  (coefficientMap p).mkContinuous ‖p‖ (coefficientValue_norm p)

theorem coefficientLift_apply {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (v : Fin n → (ℕ →ᵇ E)) (k : ℕ) : coefficientLift p v k=p (fun i => v i k) := rfl

theorem coefficientLift_norm {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) :
    ‖coefficientLift p‖≤‖p‖ :=
  MultilinearMap.mkContinuous_norm_le _ (norm_nonneg p) _

def seriesLift (p : FormalMultilinearSeries ℝ E F) :
    FormalMultilinearSeries ℝ (ℕ →ᵇ E) (ℕ →ᵇ F) := fun n => coefficientLift (p n)

theorem seriesLift_radius (p : FormalMultilinearSeries ℝ E F) : p.radius≤(seriesLift p).radius :=
  FormalMultilinearSeries.radius_le_of_le (fun n => coefficientLift_norm (p n))

end BfgsVerification.BoundedAnalytic
