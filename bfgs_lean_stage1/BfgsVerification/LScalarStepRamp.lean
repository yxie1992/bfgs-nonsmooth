import BfgsVerification.LScalarStepSeries

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.LScalarStep

def ramp (b x : ℝ) : ℝ := if LScalarRamp.center b < x then 1 else 0

theorem ramp_monotone (b : ℝ) : Monotone (ramp b) := by
  intro x y hxy
  unfold ramp
  split_ifs <;> norm_num <;> linarith

theorem integral_ramp_zero {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    (hx : x ≤ LScalarRamp.center b) : (∫ t in (0 : ℝ)..x, ramp b t) = 0 := by
  have hc : 0 ≤ LScalarRamp.center b := by
    have h := (LScalarRamp.center_bounds hl hr).1
    norm_num [LScalarRamp.epsilon] at h
    linarith
  calc
    (∫ t in (0 : ℝ)..x, ramp b t) = ∫ _ in (0 : ℝ)..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ≤ max 0 x := ht.2
      have htc := ht'.trans (max_le hc hx)
      simp [ramp, not_lt.mpr htc]
    _ = 0 := intervalIntegral.integral_zero

theorem integral_ramp_right {b x : ℝ} (hx : LScalarRamp.center b ≤ x) :
    (∫ t in LScalarRamp.center b..x, ramp b t) = x-LScalarRamp.center b := by
  calc
    (∫ t in LScalarRamp.center b..x, ramp b t) = ∫ _ in LScalarRamp.center b..x, (1 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      apply Eventually.of_forall
      intro t ht
      have ht' : LScalarRamp.center b < t := by
        rw [uIoc_of_le hx] at ht
        exact ht.1
      simp [ramp, ht']
    _ = x-LScalarRamp.center b := by simp

theorem primitive_eq_integral {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    primitive b x = ∫ t in (0 : ℝ)..x, ramp b t := by
  by_cases hx : x ≤ LScalarRamp.center b
  · rw [primitive_eq_zero hx, integral_ramp_zero hl hr hx]
  · have hx' : LScalarRamp.center b ≤ x := le_of_not_ge hx
    have hsum := intervalIntegral.integral_add_adjacent_intervals
      ((ramp_monotone b).intervalIntegrable (μ := MeasureTheory.volume) (a := 0) (b := LScalarRamp.center b))
      ((ramp_monotone b).intervalIntegrable (μ := MeasureTheory.volume) (a := LScalarRamp.center b) (b := x))
    rw [integral_ramp_zero hl hr (le_refl _), integral_ramp_right hx', zero_add] at hsum
    rw [primitive_eq_affine hx']
    exact hsum

end BfgsVerification.LScalarStep
