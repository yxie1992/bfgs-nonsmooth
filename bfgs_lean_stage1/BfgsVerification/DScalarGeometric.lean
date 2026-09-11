import Mathlib

/-! Exact geometric scales, tail sums, and interval coverage in Module D. -/

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.DScalarGeometric

def theta : ℝ := 1/16
def scale (n : ℕ) : ℝ := theta ^ n
def coordinate (b a x : ℝ) : ℝ := (x / (b*a) - theta) / (1-theta)

theorem theta_pos : 0 < theta := by norm_num [theta]
theorem theta_lt_one : theta < 1 := by norm_num [theta]
theorem scale_pos (n : ℕ) : 0 < scale n := pow_pos theta_pos n
theorem scale_le_one (n : ℕ) : scale n ≤ 1 :=
  pow_le_one₀ theta_pos.le theta_lt_one.le
theorem scale_zero : scale 0 = 1 := by simp [scale]
theorem scale_add (m n : ℕ) : scale (m+n) = scale m * scale n := pow_add _ _ _
theorem scale_succ (n : ℕ) : scale (n+1) = theta * scale n := by
  simp [scale, pow_succ, mul_comm]
theorem scale_antitone : Antitone scale := by
  exact antitone_nat_of_succ_le (fun n => by
    rw [scale_succ]
    exact mul_le_of_le_one_left (scale_pos n).le theta_lt_one.le)

theorem summable_scale_power {p : ℕ} (hp : 0 < p) :
    Summable (fun n => (scale n)^p) := by
  have he (n : ℕ) : (scale n)^p = (theta^p)^n := by
    simp only [scale, ← pow_mul, Nat.mul_comm n p]
  simp_rw [he]
  apply summable_geometric_of_abs_lt_one
  rw [abs_of_nonneg (pow_nonneg theta_pos.le p)]
  exact pow_lt_one₀ theta_pos.le theta_lt_one (by omega)

theorem tsum_scale_power {p : ℕ} (hp : 0 < p) :
    (∑' n : ℕ, (scale n)^p) = (1-theta^p)⁻¹ := by
  have he (n : ℕ) : (scale n)^p = (theta^p)^n := by
    simp only [scale, ← pow_mul, Nat.mul_comm n p]
  simp_rw [he]
  apply tsum_geometric_of_abs_lt_one
  rw [abs_of_nonneg (pow_nonneg theta_pos.le p)]
  exact pow_lt_one₀ theta_pos.le theta_lt_one (by omega)

theorem tsum_tail_power {p : ℕ} (hp : 0 < p) (k : ℕ) :
    (∑' n : ℕ, (scale (n+k))^p) = (scale k)^p / (1-theta^p) := by
  simp_rw [scale_add, mul_pow]
  rw [tsum_mul_right, tsum_scale_power hp]
  ring

theorem positive_interval_cover {b x : ℝ} (hb : 0 < b) (hx : 0 < x) (hxb : x ≤ b) :
    ∃ n : ℕ, b * theta * scale n < x ∧ x ≤ b * scale n := by
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hx hb) ((div_le_one hb).mpr hxb) theta_pos theta_lt_one
  refine ⟨n, ?_, ?_⟩
  · have h := (lt_div_iff₀ hb).mp hn1
    simpa [scale, pow_succ, mul_comm, mul_left_comm, mul_assoc] using h
  · exact (div_le_iff₀ hb).mp hn2 |>.trans_eq (mul_comm _ _)

theorem coordinate_nonpos_iff {b a x : ℝ} (hb : 0 < b) (ha : 0 < a) :
    coordinate b a x ≤ 0 ↔ x ≤ b*theta*a := by
  rw [coordinate, div_le_iff₀ (sub_pos.mpr theta_lt_one), zero_mul, sub_nonpos,
    div_le_iff₀ (mul_pos hb ha)]
  congr 1 <;> ring

theorem coordinate_ge_one_iff {b a x : ℝ} (hb : 0 < b) (ha : 0 < a) :
    1 ≤ coordinate b a x ↔ b*a ≤ x := by
  rw [coordinate, le_div_iff₀ (sub_pos.mpr theta_lt_one)]
  have he : 1 * (1-theta) ≤ x/(b*a)-theta ↔ 1 ≤ x/(b*a) := by constructor <;> intro h <;> linarith
  rw [he, le_div_iff₀ (mul_pos hb ha), one_mul]

theorem earlier_coordinate_nonpos {b x : ℝ} (hb : 0 < b) {m n : ℕ}
    (hnm : n < m) (hx : x ≤ b*scale m) : coordinate b (scale n) x ≤ 0 := by
  apply (coordinate_nonpos_iff hb (scale_pos n)).mpr
  calc x ≤ b*scale m := hx
       _ ≤ b*scale (n+1) := mul_le_mul_of_nonneg_left (scale_antitone hnm) hb.le
       _ = b*theta*scale n := by rw [scale_succ]; ring

theorem later_coordinate_ge_one {b x : ℝ} (hb : 0 < b) {m n : ℕ}
    (hmn : m < n) (hx : b*theta*scale m ≤ x) : 1 ≤ coordinate b (scale n) x := by
  apply (coordinate_ge_one_iff hb (scale_pos n)).mpr
  calc b*scale n ≤ b*scale (m+1) := mul_le_mul_of_nonneg_left (scale_antitone hmn) hb.le
       _ = b*theta*scale m := by rw [scale_succ]; ring
       _ ≤ x := hx

end BfgsVerification.DScalarGeometric
