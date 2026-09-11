import BfgsVerification.QuadraticGaugeSupports

/-! Exact actual quadratic-plus-gauge reference correction, with source constant. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace QuadraticGauge

/-- Source F's correction bound is derived from actual supporting vectors.
The zero quadratic/gauge curvature cases are included in the proved estimate. -/
theorem pair_correction_bound {m p : ℕ} (Q : Mat m) (hQ : Q.PosSemidef)
    (γ : Vec p → ℝ) (hh : Homogeneous.PositiveDegreeOne γ)
    (μ Λ : ℝ) (hμ : 0 < μ)
    (hlower : ∀ v, μ * Real.sqrt (sqNorm v) ≤ γ v)
    (hupper : ∀ v, γ v ≤ Λ * Real.sqrt (sqNorm v))
    (x z g h : Vec (m + p))
    (hg : Homogeneous.Supports (objective Q γ) x g)
    (hhg : Homogeneous.Supports (objective Q γ) z h)
    (ht : 0 < dot (h - g) (z - x)) :
    (dot (h - g) z) ^ 2 / dot (h - g) (z - x) ≤
      correctionConstant μ Λ * objective Q γ z := by
  have hsym : Q.IsSymm := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian.eq
  let a := metricEnergy Q (left z - left x)
  let b := dot (right h - right g) (right z - right x)
  let ξ := dot (Q.mulVec (left z - left x)) (left z)
  let ζ := dot (right h - right g) (right z)
  let U := metricEnergy Q (left z)
  let V := γ (right z)
  let C := correctionConstant μ Λ
  have ha : 0 ≤ a := metricEnergy_nonneg hQ _
  have hU : 0 ≤ U := metricEnergy_nonneg hQ _
  have hV : 0 ≤ V := (mul_nonneg hμ.le (Real.sqrt_nonneg _)).trans (hlower _)
  have hC : 0 ≤ C := correctionConstant_nonneg μ Λ
  have hC2 : 2 ≤ C := correctionConstant_ge_two μ Λ
  have hz := gauge_pairing_bounds hh μ Λ hμ hlower hupper
    (right x) (right z) (right g) (right h)
    (supports_right Q γ x g hg) (supports_right Q γ z h hhg)
  change 0 ≤ ζ ∧ ζ ≤ b ∧ ζ ≤ C * V at hz
  have hb : 0 ≤ b := hz.1.trans hz.2.1
  have hξ : ξ ^ 2 ≤ a * U := metric_cauchy_schwarz hQ _ _
  have hζ : ζ ^ 2 ≤ b * (C * V) := by
    have h1 := mul_le_mul_of_nonneg_left hz.2.1 hz.1
    have h2 := mul_le_mul_of_nonneg_left hz.2.2 hb
    nlinarith
  have hw := weighted_square_bound ha hb hU (mul_nonneg hC hV) hξ hζ
  have hy : left (h - g) = Q.mulVec (left z - left x) := by
    rw [left_sub, supports_left_eq Q hsym γ z h hhg, supports_left_eq Q hsym γ x g hg,
      Matrix.mulVec_sub]
  have hnum : dot (h - g) z = ξ + ζ := by
    rw [dot_split, hy, right_sub]
  have hden : dot (h - g) (z - x) = a + b := by
    rw [dot_split, hy, left_sub, right_sub, right_sub]
    congr 1
    exact dotProduct_comm _ _
  rw [hnum, hden]
  rw [hden] at ht
  apply (div_le_iff₀ ht).2
  change (ξ + ζ) ^ 2 ≤ C * (U / 2 + V) * (a + b)
  have hc : U + C * V ≤ C * (U / 2 + V) := by
    have hprod := mul_nonneg (sub_nonneg.mpr hC2) hU
    nlinarith
  exact hw.trans (by nlinarith [mul_le_mul_of_nonneg_right hc ht.le])

end QuadraticGauge
namespace AdmissibleBFGSRun
open QuadraticGauge

/-- The full actual BFGS reference correction for uᵀQu/2+γ(v), with the source's
exact max(2,1+Λ/μ). No correction premise or gradient-split assumption is added. -/
theorem quadraticGauge_referenceCorrection {m p : ℕ} (Q : Mat m) (hQ : Q.PosSemidef)
    (γ : Vec p → ℝ) (hh : Homogeneous.PositiveDegreeOne γ)
    (μ Λ : ℝ) (hμ : 0 < μ)
    (hlower : ∀ v, μ * Real.sqrt (sqNorm v) ≤ γ v)
    (hupper : ∀ v, γ v ≤ Λ * Real.sqrt (sqNorm v))
    (R : AdmissibleBFGSRun (m + p) (objective Q γ)) (k : ℕ) :
    R.referenceCorrection 0 k ≤ correctionConstant μ Λ * objective Q γ (R.x (k + 1)) := by
  have hs : R.displacement k = R.x (k + 1) - R.x k := by
    rw [R.step]
    simp only [add_sub_cancel_left]
    rfl
  have ht : 0 < dot (R.g (k + 1) - R.g k) (R.x (k + 1) - R.x k) := by
    rw [← hs]
    exact R.curvature_pos k
  have h := pair_correction_bound Q hQ γ hh μ Λ hμ hlower hupper
    (R.x k) (R.x (k + 1)) (R.g k) (R.g (k + 1))
    (convex_supporting_inequality R.convex (R.hasGradient k))
    (convex_supporting_inequality R.convex (R.hasGradient (k + 1))) ht
  simpa only [referenceCorrection, curvature, gradientChange, hs, sub_zero] using h

end AdmissibleBFGSRun
end BfgsVerification
