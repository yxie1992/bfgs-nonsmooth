import BfgsVerification.DScalarIntervals
import BfgsVerification.DScalarCurvature

/-! Strict positivity and the exact value, slope and curvature at every geometric node in D. -/

noncomputable section
open scoped Topology BigOperators
open Set Filter
namespace BfgsVerification.DScalar
open DScalarGeometric

theorem coordinate_node {b : ℝ} (hb : 0 < b) (m : ℕ) :
    coordinate b (scale m) (b*scale m) = 1 := by
  rw [coordinate, div_self (mul_ne_zero hb.ne' (scale_pos m).ne')]
  exact div_self (sub_pos.mpr theta_lt_one).ne'

theorem positivePart_node {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ) :
    positivePart b (b*scale m) = (scale m)^3 := by
  have hb : 0 < b := by linarith
  rw [positivePart_interval hl hr m (by
    nlinarith [mul_pos hb (scale_pos m), theta_lt_one]) (le_refl _), coordinate_node hb]
  rw [DScalarRamp.primitive_eq_affine (DScalarRamp.transition_inside hl hr).2.2.le,
    DScalarRamp.center_formula hb.ne']
  have ha := (scale_pos m).ne'
  generalize scale m = a at *
  dsimp [theta]
  field_simp [hb.ne']
  ring

theorem positivePart_positive {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : 0 < x) :
    0 < positivePart b x := by
  have hb : 0 < b := by linarith
  by_cases hxb : b ≤ x
  · rw [positivePart_outer hl hr hxb]
    linarith
  obtain ⟨m, hmlo, hmhi⟩ := positive_interval_cover hb hx (le_of_not_ge hxb)
  rw [positivePart_interval hl hr m hmlo.le hmhi]
  have hc : 0 ≤ coordinate b (scale m) x := by
    apply div_nonneg
    · apply sub_nonneg.mpr
      apply (le_div_iff₀ (mul_pos hb (scale_pos m))).mpr
      convert hmlo.le using 1 <;> ring
    · exact (sub_pos.mpr theta_lt_one).le
  have hJ := DScalarRamp.primitive_nonnegative hl hr (coordinate b (scale m) x)
  have hA : 0 < (theta*scale m)^3 := by have := scale_pos m; norm_num [theta]; positivity
  have hB : 0 ≤ b*(scale m)^3*(1-theta)*
      (theta^2*coordinate b (scale m) x +
        (1-theta^2)*DScalarRamp.primitive b (coordinate b (scale m) x)) := by
    have := scale_pos m
    norm_num [theta]
    positivity
  linarith

theorem earlier_slope_zero {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) {m n : ℕ}
    (hnm : n < m) (hx : x ≤ b*scale m) : slopeComponent b n x = 0 := by
  have hc := earlier_coordinate_nonpos (by linarith : 0 < b) hnm hx
  simp only [slopeComponent,
    DScalarRamp.ramp_eq_zero (hc.trans (DScalarRamp.transition_inside hl hr).1.le), mul_zero]

theorem later_slope_constant {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) {m n : ℕ}
    (hmn : m < n) (hx : b*theta*scale m ≤ x) :
    slopeComponent b n x = (scale n)^2*(1-theta^2) := by
  have hc := later_coordinate_ge_one (by linarith : 0 < b) hmn hx
  simp only [slopeComponent,
    DScalarRamp.ramp_eq_one ((DScalarRamp.transition_inside hl hr).2.2.le.trans hc), mul_one]

theorem positiveSlope_interval {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hxlo : b*theta*scale m ≤ x) (hxhi : x ≤ b*scale m) :
    positiveSlope b x = (scale m)^2*(theta^2 +
      (1-theta^2)*DScalarRamp.ramp b (coordinate b (scale m) x)) := by
  have he := (summable_slopeComponent b x).sum_add_tsum_nat_add (m+1)
  have hzero : ∑ n ∈ Finset.range m, slopeComponent b n x = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact earlier_slope_zero hl hr (Finset.mem_range.mp hn) hxhi
  have ht : (∑' n : ℕ, slopeComponent b (n+(m+1)) x) = (theta*scale m)^2 := by
    have he (n : ℕ) := later_slope_constant hl hr (show m < n+(m+1) by omega) hxlo
    simp_rw [he]
    rw [tsum_mul_right, tsum_tail_power (by omega : 0 < 2), scale_succ]
    norm_num [theta]
  rw [Finset.sum_range_succ, hzero, zero_add, ht] at he
  change _ = positiveSlope b x at he
  rw [← he]
  dsimp [slopeComponent]
  ring

theorem positiveSlope_node {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ) :
    positiveSlope b (b*scale m) = (scale m)^2 := by
  have hb : 0 < b := by linarith
  rw [positiveSlope_interval hl hr m (by
    nlinarith [mul_pos hb (scale_pos m), theta_lt_one]) (le_refl _), coordinate_node hb,
    DScalarRamp.ramp_eq_one (DScalarRamp.transition_inside hl hr).2.2.le]
  ring

theorem positiveCurvature_node {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ) :
    positiveCurvature b (b*scale m) = 0 := by
  have hb : 0 < b := by linarith
  rw [positiveCurvature_interval hl hr m (by
    nlinarith [mul_pos hb (scale_pos m), theta_lt_one]) (le_refl _)]
  exact curvatureComponent_outer_zero hl hr m (le_refl _)

end BfgsVerification.DScalar
