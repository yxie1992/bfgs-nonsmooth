import BfgsVerification.DScalarGeometric
import BfgsVerification.DScalarRamp

/-! Actual infinite ramp series and twice-differentiable summation for Module D. -/

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.DScalar
open DScalarGeometric

def component (b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  b*(scale n)^3*(1-theta)*(1-theta^2)*DScalarRamp.primitive b (coordinate b (scale n) x)
def slopeComponent (b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (scale n)^2*(1-theta^2)*DScalarRamp.ramp b (coordinate b (scale n) x)
def curvatureComponent (b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  scale n*(1+theta)/b*DScalarRamp.rampDerivative b (coordinate b (scale n) x)
def positivePart (b x : ℝ) : ℝ := ∑' n : ℕ, component b n x
def positiveSlope (b x : ℝ) : ℝ := ∑' n : ℕ, slopeComponent b n x
def positiveCurvature (b x : ℝ) : ℝ := ∑' n : ℕ, curvatureComponent b n x

theorem component_hasDerivAt {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) :
    HasDerivAt (component b n) (slopeComponent b n x) x := by
  have h := ((DScalarRamp.primitive_hasDerivAt b (coordinate b (scale n) x)).comp x
    (DScalarRamp.intervalCoordinate_hasDerivAt b (scale n) x)).const_mul
    (b*(scale n)^3*(1-theta)*(1-theta^2))
  convert h using 1
  dsimp [slopeComponent, theta, DScalarRamp.theta]
  field_simp [hb.ne', (scale_pos n).ne']
  <;> ring

theorem slopeComponent_hasDerivAt {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) :
    HasDerivAt (slopeComponent b n) (curvatureComponent b n x) x := by
  have h := ((DScalarRamp.ramp_hasDerivAt b (coordinate b (scale n) x)).comp x
    (DScalarRamp.intervalCoordinate_hasDerivAt b (scale n) x)).const_mul
    ((scale n)^2*(1-theta^2))
  convert h using 1
  dsimp [curvatureComponent, theta, DScalarRamp.theta]
  field_simp [hb.ne', (scale_pos n).ne']
  <;> ring

theorem slopeComponent_bounds (b : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ slopeComponent b n x ∧ slopeComponent b n x ≤ (scale n)^2*(1-theta^2) := by
  have hp : 0 ≤ (scale n)^2*(1-theta^2) := by norm_num [theta]; positivity
  exact ⟨mul_nonneg hp (DScalarRamp.ramp_bounds b _).1,
    mul_le_of_le_one_right hp (DScalarRamp.ramp_bounds b _).2⟩

theorem curvatureComponent_bounds {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) :
    0 ≤ curvatureComponent b n x ∧ curvatureComponent b n x ≤ (102/b)*scale n := by
  have h := DScalarRamp.intervalCurvature_bounds hb (scale_pos n).le x
  change 0 ≤ curvatureComponent b n x ∧ curvatureComponent b n x ≤ 102*scale n/b at h
  convert h using 1 <;> ring

theorem summable_slope_majorant : Summable (fun n => (scale n)^2*(1-theta^2)) :=
  (summable_scale_power (by omega : 0 < 2)).mul_right _

theorem summable_curvature_majorant (b : ℝ) : Summable (fun n => (102/b)*scale n) := by
  simpa only [pow_one] using (summable_scale_power (by omega : 0 < 1)).mul_left (102/b)

theorem component_nonpos {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : x ≤ 0) (n : ℕ) :
    component b n x = 0 := by
  have hc : coordinate b (scale n) x ≤ 0 :=
    (coordinate_nonpos_iff (by linarith) (scale_pos n)).mpr
      (hx.trans (by have := scale_pos n; norm_num [theta]; positivity))
  have hzero := DScalarRamp.primitive_eq_zero (hc.trans (DScalarRamp.transition_inside hl hr).1.le)
  simp only [component, hzero, mul_zero]

theorem summable_slopeComponent (b x : ℝ) : Summable (fun n => slopeComponent b n x) := by
  apply Summable.of_norm_bounded _ summable_slope_majorant
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (slopeComponent_bounds b n x).1]
  exact (slopeComponent_bounds b n x).2

theorem summable_curvatureComponent {b : ℝ} (hb : 0 < b) (x : ℝ) :
    Summable (fun n => curvatureComponent b n x) := by
  apply Summable.of_norm_bounded _ (summable_curvature_majorant b)
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (curvatureComponent_bounds hb n x).1]
  exact (curvatureComponent_bounds hb n x).2

theorem component_norm_bound {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (n : ℕ) (x : ℝ) :
    ‖component b n x‖ ≤ (scale n)^2*(1-theta^2)*‖x‖ := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := (univ : Set ℝ)) (fun y _ => (component_hasDerivAt (by linarith) n y).differentiableAt)
    (fun y _ => show ‖deriv (component b n) y‖ ≤ (scale n)^2*(1-theta^2) from by
      rw [(component_hasDerivAt (by linarith) n y).deriv, Real.norm_eq_abs,
        abs_of_nonneg (slopeComponent_bounds b n y).1]
      exact (slopeComponent_bounds b n y).2)
    convex_univ (mem_univ 0) (mem_univ x)
  simpa only [component_nonpos hl hr (le_refl 0) n, sub_zero] using h

theorem summable_component {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    Summable (fun n => component b n x) :=
  Summable.of_norm_bounded _ (summable_slope_majorant.mul_right ‖x‖)
    (fun n => component_norm_bound hl hr n x)

theorem positivePart_hasDerivAt {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    HasDerivAt (positivePart b) (positiveSlope b x) x := by
  apply hasDerivAt_tsum summable_slope_majorant
    (fun n y => component_hasDerivAt (by linarith) n y)
    (fun n y => ?_) (summable_component hl hr 0) x
  rw [Real.norm_eq_abs, abs_of_nonneg (slopeComponent_bounds b n y).1]
  exact (slopeComponent_bounds b n y).2

theorem positiveSlope_hasDerivAt {b : ℝ} (hb : 0 < b) (x : ℝ) :
    HasDerivAt (positiveSlope b) (positiveCurvature b x) x := by
  apply hasDerivAt_tsum (summable_curvature_majorant b)
    (fun n y => slopeComponent_hasDerivAt hb n y)
    (fun n y => ?_) (summable_slopeComponent b 0) x
  rw [Real.norm_eq_abs, abs_of_nonneg (curvatureComponent_bounds hb n y).1]
  exact (curvatureComponent_bounds hb n y).2

theorem positiveCurvature_continuous {b : ℝ} (hb : 0 < b) : Continuous (positiveCurvature b) := by
  apply continuous_tsum (fun n => ?_) (summable_curvature_majorant b)
    (fun n y => ?_)
  · have h : Continuous (DScalarRamp.rampDerivative b) := (DScalarRamp.rampDerivative_lipschitz b).continuous
    exact continuous_const.mul (h.comp (by unfold coordinate; fun_prop))
  · rw [Real.norm_eq_abs, abs_of_nonneg (curvatureComponent_bounds hb n y).1]
    exact (curvatureComponent_bounds hb n y).2

theorem positivePart_contDiff {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) : ContDiff ℝ 2 (positivePart b) := by
  rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (positivePart_hasDerivAt hl hr x).differentiableAt, by norm_num, ?_⟩
  rw [funext (fun x => (positivePart_hasDerivAt hl hr x).deriv), contDiff_one_iff_deriv]
  refine ⟨fun x => (positiveSlope_hasDerivAt (by linarith) x).differentiableAt, ?_⟩
  rw [funext (fun x => (positiveSlope_hasDerivAt (by linarith : 0 < b) x).deriv)]
  exact positiveCurvature_continuous (by linarith)

end BfgsVerification.DScalar
