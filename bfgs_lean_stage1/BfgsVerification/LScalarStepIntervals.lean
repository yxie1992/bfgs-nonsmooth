import BfgsVerification.LScalarStepSeries

/-! Exact equality of the ramp series with every printed positive interval in L. -/

noncomputable section
set_option maxHeartbeats 1600000
open scoped Topology BigOperators
open Set Filter
namespace BfgsVerification.LScalarStep
open LScalarGeometric

theorem earlier_component_zero {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) {m n : ℕ}
    (hnm : n < m) (hx : x ≤ b*scale m) : component b n x = 0 := by
  have hc := earlier_coordinate_nonpos (by linarith : 0 < b) hnm hx
  have hzero := component_zero_of_coordinate (by linarith) n (hc.trans (by have := (LScalarRamp.center_bounds hl hr).1; norm_num [LScalarRamp.epsilon] at this; linarith))
  exact hzero

theorem component_affine {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ)
    (hx : b*scale n ≤ x) :
    component b n x = (1-theta^1)*(scale n)^1*x +
      (1-b)*(1-theta^2)*(scale n)^2 := by
  simpa only [pow_one] using component_affine_of_peak (by linarith : 0 < b) n
    ((LScalar.peak_interval hl hr n).2.le.trans hx)

theorem later_component_affine {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) {m n : ℕ}
    (hmn : m < n) (hx : b*theta*scale m ≤ x) :
    component b n x = (1-theta^1)*(scale n)^1*x +
      (1-b)*(1-theta^2)*(scale n)^2 := by
  apply component_affine hl hr
  exact (coordinate_ge_one_iff (by linarith) (scale_pos n)).mp
    (later_coordinate_ge_one (by linarith) hmn hx)

theorem tail_components {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hx : b*theta*scale m ≤ x) :
    (∑' n : ℕ, component b (n+(m+1)) x) =
      (theta*scale m)^1*x + (1-b)*(theta*scale m)^2 := by
  have hs2 : Summable (fun n : ℕ => (scale (n+(m+1)))^1) :=
    (summable_nat_add_iff (m+1)).mpr (summable_scale_power (by omega : 0 < 1))
  have hs3 : Summable (fun n : ℕ => (scale (n+(m+1)))^2) :=
    (summable_nat_add_iff (m+1)).mpr (summable_scale_power (by omega : 0 < 2))
  have he (n : ℕ) := later_component_affine hl hr (show m < n+(m+1) by omega) hx
  simp_rw [he]
  rw [Summable.tsum_add ((hs2.mul_left _).mul_right _) (hs3.mul_left _),
    tsum_mul_right, tsum_mul_left, tsum_mul_left,
    tsum_tail_power (by omega : 0 < 1), tsum_tail_power (by omega : 0 < 2), scale_succ]
  norm_num [theta]
  ring

theorem positivePart_interval {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hxlo : b*theta*scale m ≤ x) (hxhi : x ≤ b*scale m) :
    positivePart b x = (theta*scale m)^2 + b*(scale m)^2*(1-theta)*
      (theta^1*coordinate b (scale m) x +
        (1-theta^1)*primitive b (coordinate b (scale m) x)) := by
  have he := (summable_component hl hr x).sum_add_tsum_nat_add (m+1)
  have hzero : ∑ n ∈ Finset.range m, component b n x = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact earlier_component_zero hl hr (Finset.mem_range.mp hn) hxhi
  rw [Finset.sum_range_succ, hzero, zero_add, tail_components hl hr m hxlo] at he
  change _ = positivePart b x at he
  rw [← he]
  rw [component_source_formula (by linarith)]
  generalize primitive b (coordinate b (scale m) x) = u
  have ha := (scale_pos m).ne'
  generalize scale m = a at *
  dsimp [coordinate, theta]
  field_simp [(by linarith : b ≠ 0), ha]
  ring

theorem positivePart_outer {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : b ≤ x) :
    positivePart b x = 1+x-b := by
  have he (n : ℕ) : component b n x = (1-theta^1)*(scale n)^1*x +
      (1-b)*(1-theta^2)*(scale n)^2 :=
    component_affine hl hr n ((mul_le_of_le_one_right (by linarith : 0 ≤ b) (scale_le_one n)).trans hx)
  unfold positivePart
  simp_rw [he]
  rw [Summable.tsum_add (((summable_scale_power (by omega : 0 < 1)).mul_left _).mul_right _)
      ((summable_scale_power (by omega : 0 < 2)).mul_left _),
    tsum_mul_right, tsum_mul_left, tsum_mul_left,
    tsum_scale_power (by omega : 0 < 1), tsum_scale_power (by omega : 0 < 2)]
  norm_num [theta]
  ring

end BfgsVerification.LScalarStep
