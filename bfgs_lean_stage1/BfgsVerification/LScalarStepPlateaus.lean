import BfgsVerification.LScalarStepIntervals

noncomputable section
set_option maxHeartbeats 1600000
open scoped Topology BigOperators
open Set Filter
namespace BfgsVerification.LScalarStep
open LScalarGeometric

theorem plateau_earlier_component {b h : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hh : |h| ≤ scale m/2) {n : ℕ} (hnm : n < m) : component b n (b*scale m+h) = 0 := by
  apply component_zero_of_coordinate (by linarith)
  have hc := LScalar.plateau_earlier_coordinate hl hr m hh hnm
  have he : 0 < LScalarRamp.epsilon := by norm_num [LScalarRamp.epsilon]
  linarith

theorem component_affine_plateau {b h : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hh : |h| ≤ scale m/2) {n : ℕ} (hmn : m ≤ n) :
    component b n (b*scale m+h) = (1-theta^1)*(scale n)^1*(b*scale m+h) +
      (1-b)*(1-theta^2)*(scale n)^2 := by
  have hc := LScalar.plateau_later_coordinate hl hr m hh hmn
  have he : 0 < LScalarRamp.epsilon := by norm_num [LScalarRamp.epsilon]
  simpa only [pow_one] using component_affine_of_coordinate (by linarith : 0 < b) n
    (show LScalarRamp.center b ≤ coordinate b (scale n) (b*scale m+h) by linarith)

theorem positivePart_plateau {b h : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hh : |h| ≤ scale m/2) :
    positivePart b (b*scale m+h) = (scale m)^2+(scale m)^1*h := by
  have hb : 0 < b := by linarith
  have he := (summable_component hl hr (b*scale m+h)).sum_add_tsum_nat_add m
  have hzero : ∑ n ∈ Finset.range m, component b n (b*scale m+h) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact plateau_earlier_component hl hr m hh (Finset.mem_range.mp hn)
  have hs2 : Summable (fun n : ℕ => (scale (n+m))^1) :=
    (summable_nat_add_iff m).mpr (summable_scale_power (by omega : 0 < 1))
  have hs3 : Summable (fun n : ℕ => (scale (n+m))^2) :=
    (summable_nat_add_iff m).mpr (summable_scale_power (by omega : 0 < 2))
  have ht : (∑' n : ℕ, component b (n+m) (b*scale m+h)) =
      (scale m)^1*(b*scale m+h)+(1-b)*(scale m)^2 := by
    have he (n : ℕ) := component_affine_plateau hl hr m hh (show m ≤ n+m by omega)
    simp_rw [he]
    rw [Summable.tsum_add ((hs2.mul_left _).mul_right _) (hs3.mul_left _),
      tsum_mul_right, tsum_mul_left, tsum_mul_left,
      tsum_tail_power (by omega : 0 < 1), tsum_tail_power (by omega : 0 < 2)]
    norm_num [theta]
    ring
  rw [hzero, zero_add, ht] at he
  change _ = positivePart b (b*scale m+h) at he
  rw [← he]
  ring


theorem positivePart_node {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) :
    positivePart b (b*scale n) = (scale n)^2 := by
  have h := positivePart_plateau hl hr n (h := 0) (by rw [abs_zero]; have := scale_pos n; positivity)
  simpa using h

theorem positivePart_positive {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : 0 < x) :
    0 < positivePart b x := by
  have hb : 0 < b := by linarith
  by_cases hxb : b ≤ x
  · rw [positivePart_outer hl hr hxb]
    linarith
  obtain ⟨m,hmlo,hmhi⟩ := positive_interval_cover hb hx (le_of_not_ge hxb)
  rw [positivePart_interval hl hr m hmlo.le hmhi]
  have hc : 0 ≤ coordinate b (scale m) x := by
    apply div_nonneg
    · apply sub_nonneg.mpr
      apply (le_div_iff₀ (mul_pos hb (scale_pos m))).mpr
      convert hmlo.le using 1 <;> ring
    · exact (sub_pos.mpr theta_lt_one).le
  have hJ : 0 ≤ primitive b (coordinate b (scale m) x) := le_max_left _ _
  have hs := scale_pos m
  norm_num [theta]
  positivity

end BfgsVerification.LScalarStep
