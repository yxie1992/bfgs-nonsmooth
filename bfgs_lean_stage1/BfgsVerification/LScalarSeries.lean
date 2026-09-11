import BfgsVerification.LScalarGeometric
import BfgsVerification.LScalarRamp

/-! Actual infinite ramp series and differentiable summation for Module L. -/

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.LScalar
open LScalarGeometric

def component (b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  b*(scale n)^2*(1-theta)*(1-theta^1)*LScalarRamp.primitive b (coordinate b (scale n) x)
def slopeComponent (b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (scale n)^1*(1-theta^1)*LScalarRamp.ramp b (coordinate b (scale n) x)
def curvatureComponent (b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  1/b*LScalarRamp.rampDerivative b (coordinate b (scale n) x)
def positivePart (b x : ℝ) : ℝ := ∑' n : ℕ, component b n x
def positiveSlope (b x : ℝ) : ℝ := ∑' n : ℕ, slopeComponent b n x
def positiveCurvature (b x : ℝ) : ℝ := ∑' n : ℕ, curvatureComponent b n x

theorem component_hasDerivAt {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) :
    HasDerivAt (component b n) (slopeComponent b n x) x := by
  have h := ((LScalarRamp.primitive_hasDerivAt b (coordinate b (scale n) x)).comp x
    (LScalarRamp.intervalCoordinate_hasDerivAt b (scale n) x)).const_mul
    (b*(scale n)^2*(1-theta)*(1-theta^1))
  convert h using 1
  dsimp [slopeComponent, theta, LScalarRamp.theta]
  field_simp [hb.ne', (scale_pos n).ne']
  <;> ring

theorem slopeComponent_hasDerivAt {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) :
    HasDerivAt (slopeComponent b n) (curvatureComponent b n x) x := by
  have h := ((LScalarRamp.ramp_hasDerivAt b (coordinate b (scale n) x)).comp x
    (LScalarRamp.intervalCoordinate_hasDerivAt b (scale n) x)).const_mul
    ((scale n)^1*(1-theta^1))
  convert h using 1
  dsimp [curvatureComponent, theta, LScalarRamp.theta]
  field_simp [hb.ne', (scale_pos n).ne']
  <;> ring

theorem slopeComponent_bounds (b : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ slopeComponent b n x ∧ slopeComponent b n x ≤ (scale n)^1*(1-theta^1) := by
  have hp : 0 ≤ (scale n)^1*(1-theta^1) := by have := scale_pos n; norm_num [theta]; positivity
  exact ⟨mul_nonneg hp (LScalarRamp.ramp_bounds b _).1,
    mul_le_of_le_one_right hp (LScalarRamp.ramp_bounds b _).2⟩

theorem curvatureComponent_bounds {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) :
    0 ≤ curvatureComponent b n x ∧ curvatureComponent b n x ≤ 768/b := by
  obtain ⟨h0,h1⟩ := LScalarRamp.rampDerivative_bounds b (coordinate b (scale n) x)
  dsimp [curvatureComponent]
  constructor
  · positivity
  · calc (1/b)*LScalarRamp.rampDerivative b (coordinate b (scale n) x)
         ≤ (1/b)*768 := mul_le_mul_of_nonneg_left h1 (by positivity)
         _ = 768/b := by ring

theorem summable_slope_majorant : Summable (fun n => (scale n)^1*(1-theta^1)) :=
  (summable_scale_power (by omega : 0 < 1)).mul_right _

theorem component_nonpos {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : x ≤ 0) (n : ℕ) :
    component b n x = 0 := by
  have hc : coordinate b (scale n) x ≤ 0 :=
    (coordinate_nonpos_iff (by linarith) (scale_pos n)).mpr
      (hx.trans (by have := scale_pos n; norm_num [theta]; positivity))
  have hzero := LScalarRamp.primitive_eq_zero (hc.trans (LScalarRamp.transition_inside hl hr).1.le)
  simp only [component, hzero, mul_zero]

theorem summable_slopeComponent (b x : ℝ) : Summable (fun n => slopeComponent b n x) := by
  apply Summable.of_norm_bounded _ summable_slope_majorant
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (slopeComponent_bounds b n x).1]
  exact (slopeComponent_bounds b n x).2

theorem component_norm_bound {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) (x : ℝ) :
    ‖component b n x‖ ≤ (scale n)^1*(1-theta^1)*‖x‖ := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := (univ : Set ℝ)) (fun y _ => (component_hasDerivAt (by linarith) n y).differentiableAt)
    (fun y _ => show ‖deriv (component b n) y‖ ≤ (scale n)^1*(1-theta^1) from by
      rw [(component_hasDerivAt (by linarith) n y).deriv, Real.norm_eq_abs,
        abs_of_nonneg (slopeComponent_bounds b n y).1]
      exact (slopeComponent_bounds b n y).2)
    convex_univ (mem_univ 0) (mem_univ x)
  simpa only [component_nonpos hl hr (le_refl 0) n, sub_zero] using h

theorem summable_component {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    Summable (fun n => component b n x) :=
  Summable.of_norm_bounded _ (summable_slope_majorant.mul_right ‖x‖)
    (fun n => component_norm_bound hl hr n x)

theorem positivePart_hasDerivAt {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    HasDerivAt (positivePart b) (positiveSlope b x) x := by
  apply hasDerivAt_tsum summable_slope_majorant
    (fun n y => component_hasDerivAt (by linarith) n y)
    (fun n y => ?_) (summable_component hl hr 0) x
  rw [Real.norm_eq_abs, abs_of_nonneg (slopeComponent_bounds b n y).1]
  exact (slopeComponent_bounds b n y).2

theorem positiveSlope_continuous (b : ℝ) : Continuous (positiveSlope b) := by
  apply continuous_tsum (fun n => ?_) summable_slope_majorant (fun n x => ?_)
  · exact continuous_const.mul ((LScalarRamp.ramp_contDiff b).continuous.comp (by unfold coordinate; fun_prop))
  · rw [Real.norm_eq_abs, abs_of_nonneg (slopeComponent_bounds b n x).1]
    exact (slopeComponent_bounds b n x).2

theorem positivePart_contDiff {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) : ContDiff ℝ 1 (positivePart b) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (positivePart_hasDerivAt hl hr x).differentiableAt, ?_⟩
  rw [funext (fun x => (positivePart_hasDerivAt hl hr x).deriv)]
  exact positiveSlope_continuous b

end BfgsVerification.LScalar
