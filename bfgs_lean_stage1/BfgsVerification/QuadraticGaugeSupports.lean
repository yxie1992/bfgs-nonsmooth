import BfgsVerification.QuadraticGaugeAlgebra

/-! Actual supporting-vector decomposition and homogeneous gauge secants. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace QuadraticGauge

/-- Restrict an actual objective support to the quadratic coordinate slice. -/
theorem supports_left {m p : ℕ} (Q : Mat m) (γ : Vec p → ℝ)
    (x g : Vec (m + p)) (hg : Homogeneous.Supports (objective Q γ) x g) :
    Homogeneous.Supports (fun u => metricEnergy Q u / 2) (left x) (left g) := by
  intro u
  have h := hg (Fin.append u (right x))
  rw [dot_split, left_sub, right_sub, left_append, right_append, sub_self] at h
  simp only [objective, left_append, right_append, dot, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero] at h
  change dot (left g) (u - left x) ≤ _
  change dot (left g) (u - left x) ≤
    metricEnergy Q u / 2 + γ (right x) - (metricEnergy Q (left x) / 2 + γ (right x)) at h
  linarith

/-- The quadratic part of an actual supporting vector is its true gradient. -/
theorem supports_left_eq {m p : ℕ} (Q : Mat m) (hQ : Q.IsSymm) (γ : Vec p → ℝ)
    (x g : Vec (m + p)) (hg : Homogeneous.Supports (objective Q γ) x g) :
    left g = Q.mulVec (left x) :=
  supporting_vector_eq_gradient (supports_left Q γ x g hg) (quadratic_hasGradient Q hQ (left x))

/-- Restrict an actual objective support to the gauge coordinate slice. -/
theorem supports_right {m p : ℕ} (Q : Mat m) (γ : Vec p → ℝ)
    (x g : Vec (m + p)) (hg : Homogeneous.Supports (objective Q γ) x g) :
    Homogeneous.Supports γ (right x) (right g) := by
  intro v
  have h := hg (Fin.append (left x) v)
  rw [dot_split, left_sub, right_sub, left_append, right_append, sub_self] at h
  simp only [objective, left_append, right_append, dot, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add] at h
  change dot (right g) (v - right x) ≤ _
  change dot (right g) (v - right x) ≤
    metricEnergy Q (left x) / 2 + γ v - (metricEnergy Q (left x) / 2 + γ (right x)) at h
  linarith

def correctionConstant (μ Λ : ℝ) : ℝ := max 2 (1 + Λ / μ)

theorem correctionConstant_ge_two (μ Λ : ℝ) : 2 ≤ correctionConstant μ Λ := le_max_left _ _

theorem correctionConstant_nonneg (μ Λ : ℝ) : 0 ≤ correctionConstant μ Λ :=
  (by norm_num : (0 : ℝ) ≤ 2).trans (correctionConstant_ge_two μ Λ)

/-- The homogeneous gauge contribution has the exact source comparison bound.
No sign condition on the upper constant Λ is added, including dimension zero. -/
theorem gauge_pairing_bounds {p : ℕ} {γ : Vec p → ℝ}
    (hh : Homogeneous.PositiveDegreeOne γ) (μ Λ : ℝ) (hμ : 0 < μ)
    (hlower : ∀ v, μ * Real.sqrt (sqNorm v) ≤ γ v)
    (hupper : ∀ v, γ v ≤ Λ * Real.sqrt (sqNorm v))
    (v w h j : Vec p) (hv : Homogeneous.Supports γ v h) (hw : Homogeneous.Supports γ w j) :
    0 ≤ dot (j - h) w ∧ dot (j - h) w ≤ dot (j - h) (w - v) ∧
    dot (j - h) w ≤ correctionConstant μ Λ * γ w := by
  have hew := Homogeneous.supporting_euler hh hw
  have hev := Homogeneous.supporting_euler hh hv
  have how := Homogeneous.supporting_linear_le hh hv w
  have hjv := Homogeneous.supporting_linear_le hh hw v
  have hw0 : 0 ≤ γ w := (mul_nonneg hμ.le (Real.sqrt_nonneg _)).trans (hlower w)
  have hz : dot (j - h) w = γ w - dot h w := by
    change (j - h) ⬝ᵥ w = _
    rw [sub_dotProduct]
    change dot j w - dot h w = _
    rw [hew]
  have hold : dot (j - h) v ≤ 0 := by
    change (j - h) ⬝ᵥ v ≤ 0
    rw [sub_dotProduct]
    change dot j v - dot h v ≤ 0
    rw [hev]
    linarith
  have hnonneg : 0 ≤ dot (j - h) w := by rw [hz]; linarith
  refine ⟨hnonneg, ?_, ?_⟩
  · change _ ≤ (j - h) ⬝ᵥ (w - v)
    rw [dotProduct_sub]
    change _ ≤ dot (j - h) w - dot (j - h) v
    linarith
  · have hneg := (Homogeneous.supporting_linear_le hh hv (-w)).trans (hupper (-w))
    have hn : sqNorm (-w) = sqNorm w := by simp only [sqNorm, Pi.neg_apply, neg_sq]
    rw [hn] at hneg
    have hdneg : dot h (-w) = -dot h w := dotProduct_neg _ _
    rw [hdneg] at hneg
    have hC : 0 ≤ correctionConstant μ Λ - 1 := by
      linarith [correctionConstant_ge_two μ Λ]
    have hΛ : Λ ≤ (correctionConstant μ Λ - 1) * μ := by
      apply (div_le_iff₀ hμ).mp
      have h := le_max_right (2 : ℝ) (1 + Λ / μ)
      change 1 + Λ / μ ≤ correctionConstant μ Λ at h
      linarith
    have h1 := mul_le_mul_of_nonneg_right hΛ (Real.sqrt_nonneg (sqNorm w))
    have h2 := mul_le_mul_of_nonneg_left (hlower w) hC
    rw [hz]
    nlinarith

end QuadraticGauge
end BfgsVerification
