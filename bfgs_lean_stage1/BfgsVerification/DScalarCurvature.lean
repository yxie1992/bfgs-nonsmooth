import BfgsVerification.DScalarSeries

/-! Actual convexity and sharp pointwise curvature bound from disjoint ramp supports. -/

noncomputable section
open scoped Topology BigOperators
open Set Filter
namespace BfgsVerification.DScalar
open DScalarGeometric

theorem slopeComponent_nonpos {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : x ≤ 0) (n : ℕ) :
    slopeComponent b n x = 0 := by
  have hc : coordinate b (scale n) x ≤ 0 :=
    (coordinate_nonpos_iff (by linarith) (scale_pos n)).mpr
      (hx.trans (by have := scale_pos n; norm_num [theta]; positivity))
  simp only [slopeComponent,
    DScalarRamp.ramp_eq_zero (hc.trans (DScalarRamp.transition_inside hl hr).1.le), mul_zero]

theorem curvatureComponent_nonpos {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : x ≤ 0) (n : ℕ) :
    curvatureComponent b n x = 0 := by
  have hc : coordinate b (scale n) x ≤ 0 :=
    (coordinate_nonpos_iff (by linarith) (scale_pos n)).mpr
      (hx.trans (by have := scale_pos n; norm_num [theta]; positivity))
  simp only [curvatureComponent,
    DScalarRamp.rampDerivative_eq_zero_left (hc.trans (DScalarRamp.transition_inside hl hr).1.le), mul_zero]

theorem positivePart_nonpos {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : x ≤ 0) :
    positivePart b x = 0 := by
  simp only [positivePart, component_nonpos hl hr hx, tsum_zero]

theorem positiveSlope_nonpos {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : x ≤ 0) :
    positiveSlope b x = 0 := by
  simp only [positiveSlope, slopeComponent_nonpos hl hr hx, tsum_zero]

theorem positiveCurvature_nonpos {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : x ≤ 0) :
    positiveCurvature b x = 0 := by
  simp only [positiveCurvature, curvatureComponent_nonpos hl hr hx, tsum_zero]

theorem positivePart_nonnegative {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    0 ≤ positivePart b x := by
  apply tsum_nonneg
  intro n
  apply mul_nonneg
  · have := scale_pos n
    norm_num [theta]
    positivity
  · exact DScalarRamp.primitive_nonnegative hl hr _

theorem positiveCurvature_nonnegative {b : ℝ} (hb : 0 < b) (x : ℝ) :
    0 ≤ positiveCurvature b x := tsum_nonneg (fun n => (curvatureComponent_bounds hb n x).1)

theorem positiveSlope_monotone {b : ℝ} (hb : 0 < b) : Monotone (positiveSlope b) := by
  apply monotone_of_deriv_nonneg (fun x => (positiveSlope_hasDerivAt hb x).differentiableAt)
  intro x
  rw [(positiveSlope_hasDerivAt hb x).deriv]
  exact positiveCurvature_nonnegative hb x

theorem positivePart_convex {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) :
    ConvexOn ℝ univ (positivePart b) := by
  apply Monotone.convexOn_univ_of_deriv (fun x => (positivePart_hasDerivAt hl hr x).differentiableAt)
  rw [funext (fun x => (positivePart_hasDerivAt hl hr x).deriv)]
  exact positiveSlope_monotone (by linarith)

theorem curvatureComponent_outer_zero {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (n : ℕ)
    (hx : b*scale n ≤ x) : curvatureComponent b n x = 0 := by
  have hc := (coordinate_ge_one_iff (by linarith : 0 < b) (scale_pos n)).mpr hx
  simp only [curvatureComponent, DScalarRamp.rampDerivative_eq_zero_right
    ((DScalarRamp.transition_inside hl hr).2.2.le.trans hc), mul_zero]

theorem positiveCurvature_outer {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : b ≤ x) :
    positiveCurvature b x = 0 := by
  have he (n : ℕ) : curvatureComponent b n x = 0 :=
    curvatureComponent_outer_zero hl hr n
      ((mul_le_of_le_one_right (by linarith : 0 ≤ b) (scale_le_one n)).trans hx)
  simp only [positiveCurvature, he, tsum_zero]

theorem curvatureComponent_other_zero {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) {m n : ℕ}
    (hnm : n ≠ m) (hxlo : b*theta*scale m ≤ x) (hxhi : x ≤ b*scale m) :
    curvatureComponent b n x = 0 := by
  rcases lt_or_gt_of_ne hnm with h | h
  · have hc := earlier_coordinate_nonpos (by linarith : 0 < b) h hxhi
    simp only [curvatureComponent,
      DScalarRamp.rampDerivative_eq_zero_left (hc.trans (DScalarRamp.transition_inside hl hr).1.le), mul_zero]
  · apply curvatureComponent_outer_zero hl hr
    exact (coordinate_ge_one_iff (by linarith) (scale_pos n)).mp
      (later_coordinate_ge_one (by linarith) h hxlo)

theorem positiveCurvature_interval {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hxlo : b*theta*scale m ≤ x) (hxhi : x ≤ b*scale m) :
    positiveCurvature b x = curvatureComponent b m x := by
  exact tsum_eq_single m (fun n hnm => curvatureComponent_other_zero hl hr hnm hxlo hxhi)

theorem positiveCurvature_bounds {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    0 ≤ positiveCurvature b x ∧ positiveCurvature b x ≤ 102/b := by
  have hb : 0 < b := by linarith
  refine ⟨positiveCurvature_nonnegative hb x, ?_⟩
  by_cases hx : x ≤ 0
  · rw [positiveCurvature_nonpos hl hr hx]
    positivity
  by_cases hxb : b ≤ x
  · rw [positiveCurvature_outer hl hr hxb]
    positivity
  obtain ⟨m, hmlo, hmhi⟩ := positive_interval_cover hb (lt_of_not_ge hx) (le_of_not_ge hxb)
  rw [positiveCurvature_interval hl hr m hmlo.le hmhi]
  exact (curvatureComponent_bounds hb m x).2.trans
    (mul_le_of_le_one_right (by positivity : 0 ≤ 102/b) (scale_le_one m))

end BfgsVerification.DScalar
