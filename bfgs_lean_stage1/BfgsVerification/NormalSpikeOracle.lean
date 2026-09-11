import BfgsVerification.NormalSpikeRegularity
import BfgsVerification.NormalSpikeBounds

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike

theorem scale_width_le_quarter (j : ℕ) : (scale j)^5 ≤ scale j / 4 := by
  have hfour : (scale j)^4 ≤ (1/4 : ℝ)^4 := pow_le_pow_left₀ (scale_pos j).le (scale_le_quarter j) 4
  have hs := mul_le_mul_of_nonneg_right hfour (scale_pos j).le
  nlinarith [scale_pos j]

theorem earlier_bump_below_query {j N : ℕ} (hj : j < N) {v : ℝ}
    (hv : v ≤ scale N + (scale N)^5) : v ≤ scale j - (scale j)^5 := by
  have h := scale_antitone (Nat.succ_le_of_lt hj)
  rw [Nat.succ_eq_add_one, scale_succ] at h
  linarith [scale_width_le_quarter j, scale_width_le_quarter N, scale_pos j]

theorem later_bump_above_query {j N : ℕ} (hj : N < j) {v : ℝ}
    (hv : scale N - (scale N)^5 ≤ v) : scale j + (scale j)^5 < v := by
  have h := scale_antitone (Nat.succ_le_of_lt hj)
  rw [Nat.succ_eq_add_one, scale_succ] at h
  linarith [scale_width_le_quarter j, scale_width_le_quarter N, scale_pos N]

theorem smaller_tail_mass (N : ℕ) : tailMass (N+1) = (16/45 : ℝ)*(scale N)^2 := by
  rw [tailMass_eq, scale_succ]
  ring

theorem smaller_tail_moment (N : ℕ) : tailMoment (N+1) = (16/105 : ℝ)*(scale N)^3 := by
  rw [tailMoment_eq, scale_succ]
  ring

theorem query_primitive_oracle (N : ℕ) {v : ℝ}
    (hv : v ∈ Icc (scale N-(scale N)^5) (scale N+(scale N)^5)) :
    seriesPrimitive v = scaledPrimitive (scale N) v +
      ((16/45 : ℝ)*(scale N)^2)*v - (16/105 : ℝ)*(scale N)^3 := by
  rw [seriesPrimitive_tail_formula (N+1) v
    (fun j hj => later_bump_above_query (by omega) hv.1), smaller_tail_mass, smaller_tail_moment,
    Finset.sum_range_succ]
  have hz : (∑ j ∈ Finset.range N, scaledPrimitive (scale j) v) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact scaledPrimitive_below (scale_pos j) (earlier_bump_below_query (Finset.mem_range.mp hj) hv.2)
  rw [hz, zero_add]

theorem query_mass_oracle (N : ℕ) {v : ℝ}
    (hv : v ∈ Icc (scale N-(scale N)^5) (scale N+(scale N)^5)) :
    seriesMass v = scaledMass (scale N) v + (16/45 : ℝ)*(scale N)^2 := by
  rw [seriesMass_tail_formula (N+1) v
    (fun j hj => later_bump_above_query (by omega) hv.1), smaller_tail_mass, Finset.sum_range_succ]
  have hz : (∑ j ∈ Finset.range N, scaledMass (scale j) v) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact scaledMass_below (scale_pos j) (earlier_bump_below_query (Finset.mem_range.mp hj) hv.2)
  rw [hz, zero_add]

theorem cumulativeMass_on_bump {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    cumulativeMass t = massPoly t + 8/15 := by
  by_cases hl : t ≤ -1
  · have he : t = -1 := le_antisymm hl ht.1
    norm_num [he, cumulativeMass, massPoly]
  · simp only [cumulativeMass, if_neg hl, if_pos ht.2]

theorem primitive_on_bump {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    primitive t = primitivePoly t := by
  by_cases hl : t ≤ -1
  · have he : t = -1 := le_antisymm hl ht.1
    norm_num [he, primitive, primitivePoly, massPoly, momentPoly]
  · simp only [primitive, if_neg hl, if_pos ht.2]

theorem scaledMass_partial {a v : ℝ} (ha : 0 < a)
    (hv : v ∈ Icc (a-a^5) (a+a^5)) :
    scaledMass a v = a^2*(massPoly ((v-a)/a^5)+8/15) := by
  unfold scaledMass
  rw [cumulativeMass_on_bump]
  constructor
  · apply (le_div_iff₀ (pow_pos ha 5)).mpr
    linarith [hv.1]
  · apply (div_le_iff₀ (pow_pos ha 5)).mpr
    linarith [hv.2]

theorem scaledMoment_partial {a v : ℝ} (ha : 0 < a)
    (hv : v ∈ Icc (a-a^5) (a+a^5)) :
    scaledMoment a v = a^3*(massPoly ((v-a)/a^5)+8/15) +
      a^7*(momentPoly ((v-a)/a^5)-1/6) := by
  have ht : (v-a)/a^5 ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · exact (le_div_iff₀ (pow_pos ha 5)).mpr (by linarith [hv.1])
    · exact (div_le_iff₀ (pow_pos ha 5)).mpr (by linarith [hv.2])
  unfold scaledMoment
  rw [scaledMass_partial ha hv]
  simp only [scaledPrimitive, primitive_on_bump ht, primitivePoly]
  field_simp
  ring

theorem seriesMass_peak (N : ℕ) : seriesMass (scale N) = (8/9 : ℝ)*(scale N)^2 := by
  have hv : scale N ∈ Icc (scale N-(scale N)^5) (scale N+(scale N)^5) := by
    constructor <;> linarith [pow_pos (scale_pos N) 5]
  rw [query_mass_oracle N hv]
  simp only [scaledMass, sub_self, zero_div, cumulativeMass_at_zero]
  ring

theorem seriesPrimitive_peak (N : ℕ) :
    seriesPrimitive (scale N) = (64/315 : ℝ)*(scale N)^3 + (1/6 : ℝ)*(scale N)^7 := by
  have hv : scale N ∈ Icc (scale N-(scale N)^5) (scale N+(scale N)^5) := by
    constructor <;> linarith [pow_pos (scale_pos N) 5]
  rw [query_primitive_oracle N hv]
  simp only [scaledPrimitive, sub_self, zero_div, primitive_at_zero]
  ring

theorem density_peak (N : ℕ) : density (scale N) = ((scale N)^3)⁻¹ := by
  have he : density (scale N) = scaledDensity (scale N) (scale N) := by
    apply tsum_eq_single N
    intro j hj
    rcases lt_or_gt_of_ne hj with hj | hj
    · exact scaledDensity_below (scale_pos j) (earlier_bump_below_peak hj)
    · exact scaledDensity_above (scale_pos j) (later_bump_above_peak hj)
  rw [he]
  norm_num [scaledDensity, bump]

theorem sourcePrimitive_peak (N : ℕ) :
    sourcePrimitive (scale N) = (64/315 : ℝ)*(scale N)^3 + (1/6 : ℝ)*(scale N)^7 := by
  rw [← seriesPrimitive_eq_source]
  exact seriesPrimitive_peak N

theorem sourcePrimitive_derivative_peak (N : ℕ) :
    deriv sourcePrimitive (scale N) = (8/9 : ℝ)*(scale N)^2 := by
  rw [(sourcePrimitive_hasDerivAt _).deriv, seriesMass_peak]

theorem sourcePrimitive_second_derivative_peak (N : ℕ) :
    deriv (deriv sourcePrimitive) (scale N) = ((scale N)^3)⁻¹ := by
  have he : deriv sourcePrimitive = seriesMass := funext fun v => (sourcePrimitive_hasDerivAt v).deriv
  rw [he, (seriesMass_hasDerivAt_pos (scale_pos N)).deriv, density_peak]

theorem sourcePrimitive_second_derivative_peaks_unbounded :
    Tendsto (fun N => deriv (deriv sourcePrimitive) (scale N)) atTop atTop := by
  simp_rw [sourcePrimitive_second_derivative_peak]
  apply tendsto_inv_nhdsGT_zero.comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [zero_pow (by omega : 3 ≠ 0)] using scale_tendsto_zero.pow 3
  · exact Eventually.of_forall (fun N => pow_pos (scale_pos N) 3)

theorem sourcePrimitive_second_derivative_not_continuousAt_zero :
    ¬ ContinuousAt (deriv (deriv sourcePrimitive)) 0 := by
  intro hc
  have ht := hc.tendsto.comp scale_tendsto_zero
  exact not_tendsto_nhds_of_tendsto_atTop sourcePrimitive_second_derivative_peaks_unbounded _ ht

end BfgsVerification.NormalSpike
