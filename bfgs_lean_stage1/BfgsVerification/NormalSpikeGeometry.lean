import BfgsVerification.NormalSpikeSeries

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike

theorem scale_add (j N : ℕ) : scale (j+N) = (1/2 : ℝ)^j * scale N := by
  unfold scale
  rw [← pow_add]
  congr 1

theorem scale_succ (j : ℕ) : scale (j+1) = scale j / 2 := by
  rw [show j+1 = 1+j by omega, scale_add]
  norm_num
  ring

theorem scale_antitone : Antitone scale := by
  apply antitone_nat_of_succ_le
  intro j
  rw [scale_succ]
  linarith [scale_pos j]

theorem scale_tendsto_zero : Tendsto scale atTop (𝓝 0) := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).mul_const (1/4 : ℝ)
  convert ht using 1
  · ext j
    unfold scale
    rw [pow_add]
    norm_num
  · norm_num

theorem exists_scale_lt {v : ℝ} (hv : 0 < v) : ∃ N, scale N < v :=
  (scale_tendsto_zero.eventually (gt_mem_nhds hv)).exists

theorem scale_width_le_half (j : ℕ) : (scale j)^5 ≤ scale j / 2 := by
  have hfour : (scale j)^4 ≤ (1/4 : ℝ)^4 := pow_le_pow_left₀ (scale_pos j).le (scale_le_quarter j) 4
  have hs := mul_le_mul_of_nonneg_right hfour (scale_pos j).le
  nlinarith [scale_pos j]

theorem scaledPrimitive_below {a v : ℝ} (ha : 0 < a) (hv : v ≤ a-a^5) :
    scaledPrimitive a v = 0 := by
  have ht : (v-a)/a^5 ≤ -1 := (div_le_iff₀ (pow_pos ha 5)).mpr (by linarith)
  simp only [scaledPrimitive, primitive, if_pos ht, mul_zero]

theorem scaledMass_below {a v : ℝ} (ha : 0 < a) (hv : v ≤ a-a^5) :
    scaledMass a v = 0 := by
  have ht : (v-a)/a^5 ≤ -1 := (div_le_iff₀ (pow_pos ha 5)).mpr (by linarith)
  simp only [scaledMass, cumulativeMass, if_pos ht, mul_zero]

theorem scaledDensity_below {a v : ℝ} (ha : 0 < a) (hv : v ≤ a-a^5) :
    scaledDensity a v = 0 := by
  have ht : (v-a)/a^5 ≤ -1 := (div_le_iff₀ (pow_pos ha 5)).mpr (by linarith)
  simp only [scaledDensity, bump, if_pos ht, mul_zero]

theorem scaledMass_above {a v : ℝ} (ha : 0 < a) (hv : a+a^5 < v) :
    scaledMass a v = (16/15)*a^2 := by
  have ht : 1 < (v-a)/a^5 := (lt_div_iff₀ (pow_pos ha 5)).mpr (by linarith)
  simp only [scaledMass, cumulativeMass, if_neg (by linarith : ¬ (v-a)/a^5 ≤ -1),
    if_neg (not_le.mpr ht)]
  ring

theorem scaledDensity_above {a v : ℝ} (ha : 0 < a) (hv : a+a^5 < v) :
    scaledDensity a v = 0 := by
  have ht : 1 < (v-a)/a^5 := (lt_div_iff₀ (pow_pos ha 5)).mpr (by linarith)
  simp only [scaledDensity, bump, if_neg (by linarith : ¬ (v-a)/a^5 ≤ -1),
    if_neg (not_le.mpr ht), mul_zero]

theorem scaledPrimitive_above {a v : ℝ} (ha : 0 < a) (hv : a+a^5 < v) :
    scaledPrimitive a v = ((16/15)*a^2)*v - (16/15)*a^3 := by
  have ht : 1 < (v-a)/a^5 := (lt_div_iff₀ (pow_pos ha 5)).mpr (by linarith)
  simp only [scaledPrimitive, primitive, if_neg (by linarith : ¬ (v-a)/a^5 ≤ -1),
    if_neg (not_le.mpr ht)]
  field_simp
  ring

theorem exists_tail_below_neighborhood {v : ℝ} (hv : 0 < v) :
    ∃ N, ∀ᶠ u in 𝓝 v, ∀ j, N ≤ j → scale j + (scale j)^5 < u := by
  obtain ⟨N, hN⟩ := exists_scale_lt (half_pos (half_pos hv))
  refine ⟨N, ?_⟩
  filter_upwards [eventually_gt_nhds (half_lt_self hv)] with u hu j hj
  have hscale := scale_antitone hj
  have hwidth := scale_width_le_half j
  linarith

theorem scale_tail_power_tsum {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∑' j : ℕ, (scale (j+N))^p) = (scale N)^p / (1-(1/2 : ℝ)^p) := by
  simp_rw [scale_add, mul_pow, ← pow_mul, Nat.mul_comm _ p, pow_mul]
  rw [tsum_mul_right, tsum_geometric_of_abs_lt_one]
  · ring
  · rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1/2 : ℝ)^p)]
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

theorem summable_tail_scale_power {p : ℕ} (hp : 0 < p) (N : ℕ) :
    Summable (fun j => (scale (j+N))^p) :=
  (summable_scale_power hp).comp_injective (fun _ _ h => Nat.add_right_cancel h)

theorem earlier_bump_below_peak {j N : ℕ} (hj : j < N) :
    scale N ≤ scale j - (scale j)^5 := by
  have h := scale_antitone (Nat.succ_le_of_lt hj)
  rw [Nat.succ_eq_add_one, scale_succ] at h
  linarith [scale_width_le_half j]

theorem later_bump_above_peak {j N : ℕ} (hj : N < j) :
    scale j + (scale j)^5 < scale N := by
  have h := scale_antitone (Nat.succ_le_of_lt hj)
  rw [Nat.succ_eq_add_one, scale_succ] at h
  linarith [scale_width_le_half j, scale_pos N]

end BfgsVerification.NormalSpike
