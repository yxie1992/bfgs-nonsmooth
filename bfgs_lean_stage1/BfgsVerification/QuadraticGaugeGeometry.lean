import BfgsVerification.QuadraticGaugeCorrection
import BfgsVerification.ObjectiveLogRates

/-! Compactness and uniqueness for the actual quadratic-plus-coercive-gauge
objective. The displayed square root is precisely the Euclidean norm, independently
of Lean's default finite-Pi norm. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace QuadraticGauge

@[simp] theorem append_left_right {m p : ℕ} (x : Vec (m + p)) :
    Fin.append (left x) (right x) = x := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact Fin.append_left _ _ j
  · exact Fin.append_right _ _ j

theorem sqrt_sqNorm_eq_euclidean_norm {n : ℕ} (x : Vec n) :
    Real.sqrt (sqNorm x) = ‖euclideanVector x‖ := by
  have h : ‖euclideanVector x‖ ^ 2 = sqNorm x :=
    FrameNorms.euclidean_norm_sq (euclideanVector x)
  rw [← h, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

@[simp] theorem objective_zero {m p : ℕ} (Q : Mat m) (γ : Vec p → ℝ)
    (hh : Homogeneous.PositiveDegreeOne γ) : objective Q γ 0 = 0 := by
  change metricEnergy Q 0 / 2 + γ 0 = 0
  simp [metricEnergy, dot, Homogeneous.value_zero hh]

theorem objective_nonneg {m p : ℕ} (Q : Mat m) (hQ : Q.PosSemidef)
    (γ : Vec p → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hlower : ∀ v, μ * Real.sqrt (sqNorm v) ≤ γ v) (x : Vec (m + p)) :
    0 ≤ objective Q γ x :=
  add_nonneg (div_nonneg (metricEnergy_nonneg hQ _) (by norm_num))
    ((mul_nonneg hμ.le (Real.sqrt_nonneg _)).trans (hlower _))

/-- Positive definiteness and the coercive gauge lower bound derive the unique
minimizer; neither compactness nor boundedness of a run is an assumption. -/
theorem objective_eq_zero_iff {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef)
    (γ : Vec p → ℝ) (hh : Homogeneous.PositiveDegreeOne γ) (μ : ℝ) (hμ : 0 < μ)
    (hlower : ∀ v, μ * Real.sqrt (sqNorm v) ≤ γ v) (x : Vec (m + p)) :
    objective Q γ x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have he := metricEnergy_nonneg hQ.posSemidef (left x)
    have hlow := hlower (right x)
    have hv := mul_nonneg hμ.le (Real.sqrt_nonneg (sqNorm (right x)))
    have hleft : left x = 0 := by
      by_contra hn
      have hp := metricEnergy_pos hQ hn
      unfold objective at hx
      linarith
    have hroot : Real.sqrt (sqNorm (right x)) = 0 := by
      have hne : Real.sqrt (sqNorm (right x)) ≤ 0 := by
        apply (mul_le_mul_left hμ).mp
        unfold objective at hx
        nlinarith
      exact le_antisymm hne (Real.sqrt_nonneg _)
    have hn : ‖euclideanVector (right x)‖ = 0 := by
      rwa [sqrt_sqNorm_eq_euclidean_norm] at hroot
    have hright : right x = 0 := by
      have hz := norm_eq_zero.mp hn
      exact congrArg (fun y : EuclideanSpace ℝ (Fin p) => fun i => y i) hz
    rw [← append_left_right x, hleft, hright]
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · rintro rfl
    exact objective_zero Q γ hh

/-- Every sublevel is compact. Finite convexity and the derived unique minimizer
supply compactness; no spectral bounds or iterate bounds are imposed. -/
theorem sublevel_compact {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef)
    (γ : Vec p → ℝ) (hh : Homogeneous.PositiveDegreeOne γ)
    (hconv : ConvexOn ℝ univ (objective Q γ)) (μ : ℝ) (hμ : 0 < μ)
    (hlower : ∀ v, μ * Real.sqrt (sqNorm v) ≤ γ v) (a : ℝ) :
    IsCompact {x | objective Q γ x ≤ a} := by
  apply Localization.sublevel_compact hconv 0
  · intro x
    rw [objective_zero Q γ hh]
    exact objective_nonneg Q hQ.posSemidef γ μ hμ hlower x
  · intro x hx
    rw [objective_zero Q γ hh] at hx
    exact (objective_eq_zero_iff Q hQ γ hh μ hμ hlower x).mp hx

end QuadraticGauge
namespace AdmissibleBFGSRun
open QuadraticGauge

theorem quadraticGauge_initialSublevel_compact {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef)
    (γ : Vec p → ℝ) (hh : Homogeneous.PositiveDegreeOne γ) (μ : ℝ) (hμ : 0 < μ)
    (hlower : ∀ v, μ * Real.sqrt (sqNorm v) ≤ γ v)
    (R : AdmissibleBFGSRun (m + p) (objective Q γ)) : IsCompact R.initialSublevel :=
  sublevel_compact Q hQ γ hh R.convex μ hμ hlower _

end AdmissibleBFGSRun
end BfgsVerification
