import BfgsVerification.LScalarIntervals

/-! Exact affine plateaus on the full closed half-scale neighborhoods in L. -/

noncomputable section
set_option maxHeartbeats 1600000
open scoped Topology BigOperators
open Set Filter
namespace BfgsVerification.LScalar
open LScalarGeometric

theorem coordinate_le_iff {b a x : ℝ} (hb : 0 < b) (ha : 0 < a) (q : ℝ) :
    coordinate b a x ≤ q ↔ x ≤ b*a*(theta+(1-theta)*q) := by
  have he : coordinate b a x ≤ q ↔ x/(b*a) ≤ theta+(1-theta)*q := by
    rw [coordinate, div_le_iff₀ (sub_pos.mpr theta_lt_one)]
    constructor <;> intro h <;> linarith
  rw [he, div_le_iff₀ (mul_pos hb ha)]
  congr 1 <;> ring

theorem coordinate_ge_iff {b a x : ℝ} (hb : 0 < b) (ha : 0 < a) (q : ℝ) :
    q ≤ coordinate b a x ↔ b*a*(theta+(1-theta)*q) ≤ x := by
  have he : q ≤ coordinate b a x ↔ theta+(1-theta)*q ≤ x/(b*a) := by
    rw [coordinate, le_div_iff₀ (sub_pos.mpr theta_lt_one)]
    constructor <;> intro h <;> linarith
  rw [he, le_div_iff₀ (mul_pos hb ha)]
  congr 1 <;> ring

theorem lower_threshold_identity (b a : ℝ) :
    b*a*(theta+(1-theta)*(LScalarRamp.center b+LScalarRamp.epsilon)) =
      (b-LScalarRamp.lowerLength b)*a := by
  dsimp [LScalarRamp.lowerLength, theta, LScalarRamp.theta]
  ring

theorem upper_threshold_identity (b : ℝ) (n : ℕ) :
    b*scale n*(theta+(1-theta)*(LScalarRamp.center b-LScalarRamp.epsilon)) =
      (b+LScalarRamp.upperLength b)*scale (n+1) := by
  rw [scale_succ]
  dsimp [LScalarRamp.upperLength, theta, LScalarRamp.theta]
  ring

theorem lower_threshold_positive {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    0 < b-LScalarRamp.lowerLength b := by
  have hb : 0 < b := by linarith
  have ht := LScalarRamp.transition_inside hl hr
  have hc : 0 < LScalarRamp.center b+LScalarRamp.epsilon := ht.1.trans ht.2.1
  have he := lower_threshold_identity b 1
  rw [mul_one, mul_one] at he
  rw [← he]
  exact mul_pos hb (add_pos theta_pos (mul_pos (sub_pos.mpr theta_lt_one) hc))

theorem plateau_earlier_coordinate {b h : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hh : |h| ≤ scale m/2) {n : ℕ} (hnm : n < m) :
    coordinate b (scale n) (b*scale m+h) ≤ LScalarRamp.center b-LScalarRamp.epsilon := by
  have hb : 0 < b := by linarith
  have hu := (LScalarRamp.plateau_lengths hl hr).2
  have hlen : 0 ≤ b+LScalarRamp.upperLength b := by linarith
  apply (coordinate_le_iff hb (scale_pos n) _).mpr
  rw [upper_threshold_identity]
  calc b*scale m+h ≤ (b+LScalarRamp.upperLength b)*scale m := by
         have hs := scale_pos m
         have hh' := (abs_le.mp hh).2
         nlinarith
       _ ≤ (b+LScalarRamp.upperLength b)*scale (n+1) :=
         mul_le_mul_of_nonneg_left (scale_antitone hnm) hlen

theorem plateau_later_coordinate {b h : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hh : |h| ≤ scale m/2) {n : ℕ} (hmn : m ≤ n) :
    LScalarRamp.center b+LScalarRamp.epsilon ≤ coordinate b (scale n) (b*scale m+h) := by
  have hb : 0 < b := by linarith
  have hell := (LScalarRamp.plateau_lengths hl hr).1
  apply (coordinate_ge_iff hb (scale_pos n) _).mpr
  rw [lower_threshold_identity]
  calc (b-LScalarRamp.lowerLength b)*scale n ≤ (b-LScalarRamp.lowerLength b)*scale m :=
         mul_le_mul_of_nonneg_left (scale_antitone hmn) (lower_threshold_positive hl hr).le
       _ ≤ b*scale m+h := by
         have hs := scale_pos m
         have hh' := (abs_le.mp hh).1
         nlinarith

theorem plateau_earlier_component {b h : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hh : |h| ≤ scale m/2) {n : ℕ} (hnm : n < m) : component b n (b*scale m+h) = 0 := by
  simp only [component, LScalarRamp.primitive_eq_zero (plateau_earlier_coordinate hl hr m hh hnm), mul_zero]

theorem component_affine_of_coordinate {b x : ℝ} (hb : 0 < b) (n : ℕ)
    (hx : LScalarRamp.center b+LScalarRamp.epsilon ≤ coordinate b (scale n) x) :
    component b n x = (1-theta^1)*(scale n)^1*x +
      (1-b)*(1-theta^2)*(scale n)^2 := by
  rw [component, LScalarRamp.primitive_eq_affine hx, LScalarRamp.center_formula hb.ne']
  have ha := (scale_pos n).ne'
  generalize scale n = a at *
  dsimp [coordinate, theta]
  field_simp [hb.ne', ha]
  ring

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
    have he (n : ℕ) := component_affine_of_coordinate hb (n+m)
      (plateau_later_coordinate hl hr m hh (show m ≤ n+m by omega))
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

end BfgsVerification.LScalar
