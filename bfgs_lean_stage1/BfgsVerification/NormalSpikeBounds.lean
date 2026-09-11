import BfgsVerification.NormalSpikeGeometry

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike

theorem seriesMass_quadratic_bound {v : ℝ} (hv : 0 ≤ v) : seriesMass v ≤ 6*v^2 := by
  rcases hv.eq_or_lt with he | hv
  · subst v
    rw [seriesMass_nonpos le_rfl]
    norm_num
  have hex : ∃ N, scale N < 2*v := exists_scale_lt (by linarith)
  let N := Nat.find hex
  have hN : scale N < 2*v := Nat.find_spec hex
  have hbefore (j : ℕ) (hj : j < N) : scaledMass (scale j) v = 0 := by
    have hscale : 2*v ≤ scale j := le_of_not_gt (Nat.find_min hex hj)
    exact scaledMass_below (scale_pos j) (by linarith [scale_width_le_half j])
  have hprefix : (∑ j ∈ Finset.range N, scaledMass (scale j) v) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact hbefore j (Finset.mem_range.mp hj)
  have he := (summable_scaledMass v).sum_add_tsum_nat_add N
  rw [hprefix, zero_add] at he
  have hsum := (summable_tail_scale_power (by omega : 0 < 2) N).mul_left (16/15 : ℝ)
  calc
    seriesMass v = ∑' j : ℕ, scaledMass (scale (j+N)) v := he.symm
    _ ≤ ∑' j : ℕ, (16/15 : ℝ)*(scale (j+N))^2 :=
      tsum_le_tsum (fun j => (scaledMass_bounds _ _).2)
        ((summable_scaledMass v).comp_injective (fun _ _ h => Nat.add_right_cancel h)) hsum
    _ = (64/45 : ℝ)*(scale N)^2 := by
      rw [tsum_mul_left, scale_tail_power_tsum (by omega : 0 < 2)]
      norm_num
      ring
    _ ≤ 6*v^2 := by nlinarith [sq_nonneg (2*v-scale N), scale_pos N]

theorem seriesMass_abs_quadratic_bound (v : ℝ) : |seriesMass v| ≤ 6*v^2 := by
  rw [abs_of_nonneg (seriesMass_nonneg v)]
  by_cases hv : 0 ≤ v
  · exact seriesMass_quadratic_bound hv
  · rw [seriesMass_nonpos (le_of_not_ge hv)]
    positivity

theorem seriesPrimitive_cubic_bound {v : ℝ} (hv : 0 ≤ v) : seriesPrimitive v ≤ 6*v^3 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => seriesPrimitive_hasDerivAt t) (seriesMass_continuous.intervalIntegrable 0 v)
  rw [seriesPrimitive_nonpos le_rfl, sub_zero] at he
  have hb : (∫ t in (0 : ℝ)..v, seriesMass t) ≤ ∫ _ in (0 : ℝ)..v, 6*v^2 := by
    apply intervalIntegral.integral_mono_on hv
      (seriesMass_continuous.intervalIntegrable 0 v) (intervalIntegrable_const)
    intro t ht
    exact (seriesMass_monotone ht.2).trans (seriesMass_quadratic_bound hv)
  rw [he, intervalIntegral.integral_const] at hb
  simp only [sub_zero, smul_eq_mul] at hb
  nlinarith [hb]

theorem seriesMass_hasDerivAt_zero : HasDerivAt seriesMass 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add, seriesMass_nonpos le_rfl, sub_zero, smul_eq_mul]
  have hb (t : ℝ) : ‖t⁻¹*seriesMass t‖ ≤ 6*|t| := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv]
    calc
      |t|⁻¹*|seriesMass t| ≤ |t|⁻¹*(6*t^2) :=
        mul_le_mul_of_nonneg_left (seriesMass_abs_quadratic_bound t) (inv_nonneg.mpr (abs_nonneg t))
      _ ≤ 6*|t| := by
        by_cases ht : t = 0
        · simp [ht]
        · have hab : |t| ≠ 0 := abs_ne_zero.mpr ht
          have hp : 0 < |t| := abs_pos.mpr ht
          rw [← div_eq_inv_mul]
          apply (div_le_iff₀ hp).mpr
          nlinarith [sq_abs t]
  apply squeeze_zero_norm (fun t => hb t)
  have h := (show Continuous (fun t : ℝ => 6*|t|) from continuous_const.mul continuous_abs).tendsto 0
  simpa using h.mono_left nhdsWithin_le_nhds

theorem sourcePrimitive_hasDerivAt (v : ℝ) : HasDerivAt sourcePrimitive (seriesMass v) v := by
  have he : sourcePrimitive = seriesPrimitive := funext fun t => (seriesPrimitive_eq_source t).symm
  rw [he]
  exact seriesPrimitive_hasDerivAt v

theorem sourcePrimitive_hasSecondDerivAt_zero : HasDerivAt (deriv sourcePrimitive) 0 0 := by
  have he : deriv sourcePrimitive = seriesMass := funext fun v => (sourcePrimitive_hasDerivAt v).deriv
  rw [he]
  exact seriesMass_hasDerivAt_zero

theorem sourcePrimitive_second_derivative_zero : deriv (deriv sourcePrimitive) 0 = 0 :=
  sourcePrimitive_hasSecondDerivAt_zero.deriv

end BfgsVerification.NormalSpike
