import BfgsVerification.QuadraticGaugeGeometry

/-! Restricting the actual accepted Fréchet derivative gives the genuine gauge
derivative at the accepted right coordinate. No differentiability of rejected
trial points, or of the gauge at its nonsmooth center, is required. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace QuadraticGauge

def rightEmbedding {m p : ℕ} : Vec p →L[ℝ] Vec (m + p) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => Fin.append 0 v
    map_add' := by
      intro u v
      ext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    map_smul' := by
      intro a v
      ext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp }

@[simp] theorem rightEmbedding_apply {m p : ℕ} (v : Vec p) :
    rightEmbedding (m := m) v = Fin.append (0 : Vec m) v := rfl

theorem right_slice_hasFDerivAt {m p : ℕ} (x : Vec (m + p)) :
    HasFDerivAt (fun v : Vec p => Fin.append (left x) v) rightEmbedding (right x) := by
  convert rightEmbedding.hasFDerivAt.const_add (Fin.append (left x) (0 : Vec p)) using 1
  funext v
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem gradientFunctional_comp_rightEmbedding {m p : ℕ} (g : Vec (m + p)) :
    (gradientFunctional g).comp rightEmbedding = gradientFunctional (right g) := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, gradientFunctional_apply, rightEmbedding_apply,
    dot_split, left_append, right_append]
  simp [dot]

/-- Actual differentiability of the full objective entails actual differentiability
of the gauge at the accepted coordinate, with exactly the right gradient block. -/
theorem hasGradient_right {m p : ℕ} (Q : Mat m) (γ : Vec p → ℝ)
    (x g : Vec (m + p)) (hg : HasFDerivAt (objective Q γ) (gradientFunctional g) x) :
    HasFDerivAt γ (gradientFunctional (right g)) (right x) := by
  have hgx : HasFDerivAt (objective Q γ) (gradientFunctional g)
      (Fin.append (left x) (right x)) := by simpa only [append_left_right] using hg
  have hc := (hgx.comp (right x) (right_slice_hasFDerivAt x)).sub_const
    (metricEnergy Q (left x) / 2)
  rw [gradientFunctional_comp_rightEmbedding] at hc
  convert hc using 1
  funext v
  simp [Function.comp_def, objective]

end QuadraticGauge
namespace AdmissibleBFGSRun
open QuadraticGauge

/-- The actual accepted gradient splits into Q u and the actual gauge derivative.
The run's ordinary differentiability premise is sufficient for both statements. -/
theorem quadraticGauge_gradient_split {m p : ℕ} (Q : Mat m) (hQ : Q.IsSymm)
    (γ : Vec p → ℝ) (R : AdmissibleBFGSRun (m + p) (objective Q γ)) (k : ℕ) :
    left (R.g k) = Q.mulVec (left (R.x k)) ∧
      HasFDerivAt γ (gradientFunctional (right (R.g k))) (right (R.x k)) :=
  ⟨supports_left_eq Q hQ γ _ _ (convex_supporting_inequality R.convex (R.hasGradient k)),
    hasGradient_right Q γ _ _ (R.hasGradient k)⟩

end AdmissibleBFGSRun
end BfgsVerification
