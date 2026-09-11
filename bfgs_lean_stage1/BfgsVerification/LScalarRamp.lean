import BfgsVerification.DScalarRamp

open Set Filter
open scoped Topology
namespace BfgsVerification.LScalarRamp
open DScalarRamp
noncomputable section

def theta : ℝ := 1/128

def epsilon : ℝ := 1/1024

def center (b : ℝ) : ℝ := (1-(1+theta)/b)/(1-theta)

def rampCoordinate (b x : ℝ) : ℝ := (x-center b+epsilon)/(2*epsilon)

def ramp (b x : ℝ) : ℝ := unitRamp (rampCoordinate b x)

def rampDerivative (b x : ℝ) : ℝ := 512 * unitDerivative (rampCoordinate b x)

def primitive (b x : ℝ) : ℝ := 2*epsilon * unitPrimitive (rampCoordinate b x)

theorem rampCoordinate_hasDerivAt (b x : ℝ) :
    HasDerivAt (rampCoordinate b) 512 x := by
  convert (((hasDerivAt_id x).sub_const (center b)).add_const epsilon).div_const (2*epsilon)
    using 1 <;> norm_num [rampCoordinate, epsilon]

theorem ramp_hasDerivAt (b x : ℝ) : HasDerivAt (ramp b) (rampDerivative b x) x := by
  convert (unitRamp_hasDerivAt (rampCoordinate b x)).comp x (rampCoordinate_hasDerivAt b x)
    using 1 <;> simp [ramp, rampDerivative] <;> ring

theorem primitive_hasDerivAt (b x : ℝ) : HasDerivAt (primitive b) (ramp b x) x := by
  convert ((unitPrimitive_hasDerivAt (rampCoordinate b x)).comp x
    (rampCoordinate_hasDerivAt b x)).const_mul (2*epsilon) using 1 <;>
    simp [primitive, ramp, epsilon] <;> ring

theorem ramp_contDiff (b : ℝ) : ContDiff ℝ 1 (ramp b) := by
  exact unitRamp_contDiff.comp (by unfold rampCoordinate; simp only [div_eq_mul_inv]; fun_prop)

theorem primitive_contDiff (b : ℝ) : ContDiff ℝ 2 (primitive b) := by
  have h : ContDiff ℝ 2 (fun x => unitPrimitive (rampCoordinate b x)) :=
    unitPrimitive_contDiff.comp (by unfold rampCoordinate; simp only [div_eq_mul_inv]; fun_prop)
  exact contDiff_const.mul h

theorem ramp_bounds (b x : ℝ) : 0 ≤ ramp b x ∧ ramp b x ≤ 1 := unitRamp_bounds _

theorem rampDerivative_bounds (b x : ℝ) : 0 ≤ rampDerivative b x ∧ rampDerivative b x ≤ 768 := by
  obtain ⟨h0,h1⟩ := unitDerivative_bounds (rampCoordinate b x)
  dsimp [rampDerivative]
  constructor <;> linarith


theorem ramp_eq_zero {b x : ℝ} (hx : x ≤ center b-epsilon) : ramp b x = 0 := by
  have ht : rampCoordinate b x ≤ 0 := by
    norm_num [rampCoordinate, epsilon] at *
    linarith
  have ht1 : rampCoordinate b x ≤ 1 := by linarith
  simp [ramp, unitRamp, DScalarRamp.join, ht, ht1]

theorem ramp_eq_one {b x : ℝ} (hx : center b+epsilon ≤ x) : ramp b x = 1 := by
  have ht : 1 ≤ rampCoordinate b x := by
    norm_num [rampCoordinate, epsilon] at *
    linarith
  rcases eq_or_lt_of_le ht with h | h
  · rw [ramp, ← h]
    norm_num [unitRamp, DScalarRamp.join, cubic]
  · simp [ramp, unitRamp, DScalarRamp.join, not_le.mpr h]

theorem ramp_eq_cubic {b x : ℝ} (hl : center b-epsilon < x)
    (hr : x < center b+epsilon) : ramp b x = cubic (rampCoordinate b x) := by
  have ht0 : 0 < rampCoordinate b x := by norm_num [rampCoordinate, epsilon] at *; linarith
  have ht1 : rampCoordinate b x < 1 := by norm_num [rampCoordinate, epsilon] at *; linarith
  simp [ramp, unitRamp, DScalarRamp.join, ht1.le, not_le.mpr ht0]

theorem primitive_eq_zero {b x : ℝ} (hx : x ≤ center b-epsilon) : primitive b x = 0 := by
  have ht : rampCoordinate b x ≤ 0 := by norm_num [rampCoordinate, epsilon] at *; linarith
  have ht1 : rampCoordinate b x ≤ 1 := by linarith
  simp [primitive, unitPrimitive, DScalarRamp.join, ht, ht1]

theorem primitive_eq_affine {b x : ℝ} (hx : center b+epsilon ≤ x) :
    primitive b x = x-center b := by
  have ht : 1 ≤ rampCoordinate b x := by norm_num [rampCoordinate, epsilon] at *; linarith
  have hu : unitPrimitive (rampCoordinate b x) = rampCoordinate b x-1/2 := by
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]; norm_num [unitPrimitive, DScalarRamp.join, quartic]
    · simp [unitPrimitive, DScalarRamp.join, not_le.mpr h]
  rw [primitive, hu]
  dsimp [rampCoordinate, epsilon]
  ring

theorem primitive_eq_quartic {b x : ℝ} (hl : center b-epsilon < x)
    (hr : x < center b+epsilon) :
    primitive b x = 2*epsilon*quartic (rampCoordinate b x) := by
  have ht0 : 0 < rampCoordinate b x := by norm_num [rampCoordinate, epsilon] at *; linarith
  have ht1 : rampCoordinate b x < 1 := by norm_num [rampCoordinate, epsilon] at *; linarith
  simp [primitive, unitPrimitive, DScalarRamp.join, ht1.le, not_le.mpr ht0]

def lowerLength (b : ℝ) : ℝ := b*(1-theta)*(1-center b-epsilon)

def upperLength (b : ℝ) : ℝ := b*(1-theta)*(center b-epsilon)/theta

theorem center_formula {b : ℝ} (hb : b ≠ 0) : center b = (128*b-129)/(127*b) := by
  dsimp [center, theta]
  field_simp
  <;> ring

theorem center_bounds {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    epsilon < center b ∧ center b < 1-epsilon := by
  have hb : 0 < b := by linarith
  rw [center_formula hb.ne']
  dsimp [epsilon]
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith

theorem transition_inside {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    0 < center b-epsilon ∧ center b-epsilon < center b+epsilon ∧ center b+epsilon < 1 := by
  obtain ⟨h0,h1⟩ := center_bounds hl hr
  dsimp [epsilon] at *
  constructor
  · linarith
  constructor <;> linarith

theorem lowerLength_formula {b : ℝ} (hb : b ≠ 0) :
    lowerLength b = 129/128 - 1151*b/131072 := by
  rw [lowerLength, center_formula hb]
  dsimp [theta, epsilon]
  field_simp
  <;> ring

theorem upperLength_formula {b : ℝ} (hb : b ≠ 0) :
    upperLength b = 130945*b/1024 - 129 := by
  rw [upperLength, center_formula hb]
  dsimp [theta, epsilon]
  field_simp
  <;> ring

theorem plateau_lengths {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    1/2 < lowerLength b ∧ 1/2 < upperLength b := by
  have hb : b ≠ 0 := by linarith
  rw [lowerLength_formula hb, upperLength_formula hb]
  constructor <;> nlinarith

theorem matching_identity {b : ℝ} (hb : b ≠ 0) :
    theta+(1-theta)*(1-center b) = (1+theta)/b := by
  dsimp [center, theta]
  field_simp
  <;> ring

theorem primitive_eq_integral {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    primitive b x = ∫ t in (0 : ℝ)..x, ramp b t := by
  have hz : primitive b 0 = 0 := primitive_eq_zero (transition_inside hl hr).1.le
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => primitive_hasDerivAt b t) ((ramp_contDiff b).continuous.intervalIntegrable 0 x), hz,
    sub_zero]

theorem integral_ramp {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    ∫ t in (0 : ℝ)..1, ramp b t = 1-center b := by
  rw [← primitive_eq_integral hl hr, primitive_eq_affine (transition_inside hl hr).2.2.le]

theorem ramp_monotone (b : ℝ) : Monotone (ramp b) :=
  monotone_of_hasDerivAt_nonneg (ramp_hasDerivAt b) (fun x => (rampDerivative_bounds b x).1)

theorem deriv_ramp_bounds (b x : ℝ) : 0 ≤ deriv (ramp b) x ∧ deriv (ramp b) x ≤ 768 := by
  rw [(ramp_hasDerivAt b x).deriv]
  exact rampDerivative_bounds b x

theorem rampDerivative_eq_zero_left {b x : ℝ} (hx : x ≤ center b-epsilon) :
    rampDerivative b x = 0 := by
  have ht : rampCoordinate b x ≤ 0 := by norm_num [rampCoordinate, epsilon] at *; linarith
  have ht1 : rampCoordinate b x ≤ 1 := by linarith
  simp [rampDerivative, unitDerivative, DScalarRamp.join, ht, ht1]

theorem rampDerivative_eq_zero_right {b x : ℝ} (hx : center b+epsilon ≤ x) :
    rampDerivative b x = 0 := by
  have ht : 1 ≤ rampCoordinate b x := by norm_num [rampCoordinate, epsilon] at *; linarith
  rcases eq_or_lt_of_le ht with h | h
  · rw [rampDerivative, ← h]; norm_num [unitDerivative, DScalarRamp.join, cubicDerivative]
  · simp [rampDerivative, unitDerivative, DScalarRamp.join, not_le.mpr h]

theorem endpoint_data {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    ramp b 0 = 0 ∧ ramp b 1 = 1 ∧ rampDerivative b 0 = 0 ∧ rampDerivative b 1 = 0 ∧
    primitive b 0 = 0 ∧ primitive b 1 = 1-center b := by
  obtain ⟨h0,_,h1⟩ := transition_inside hl hr
  exact ⟨ramp_eq_zero h0.le, ramp_eq_one h1.le, rampDerivative_eq_zero_left h0.le,
    rampDerivative_eq_zero_right h1.le, primitive_eq_zero h0.le, primitive_eq_affine h1.le⟩

theorem primitive_monotone (b : ℝ) : Monotone (primitive b) :=
  monotone_of_hasDerivAt_nonneg (primitive_hasDerivAt b) (fun x => (ramp_bounds b x).1)

theorem identity_sub_primitive_monotone (b : ℝ) : Monotone (fun x => x-primitive b x) := by
  apply monotone_of_hasDerivAt_nonneg
    (fun x => (hasDerivAt_id x).sub (primitive_hasDerivAt b x))
  intro x
  exact sub_nonneg.mpr (ramp_bounds b x).2

theorem primitive_nonnegative {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    0 ≤ primitive b x := by
  have hz := (endpoint_data hl hr).2.2.2.2.1
  by_cases hx : x ≤ 0
  · rw [primitive_eq_zero (hx.trans (transition_inside hl hr).1.le)]
  · have h := primitive_monotone b (le_of_not_ge hx)
    simpa only [hz] using h

theorem primitive_linear_upper_bound {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    primitive b x ≤ max 0 x := by
  have hz := (endpoint_data hl hr).2.2.2.2.1
  by_cases hx : x ≤ 0
  · rw [primitive_eq_zero (hx.trans (transition_inside hl hr).1.le)]
    exact le_max_left _ _
  · have h := identity_sub_primitive_monotone b (le_of_not_ge hx)
    dsimp only at h
    rw [hz] at h
    rw [max_eq_right (le_of_not_ge hx)]
    linarith

theorem primitive_abs_bound {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    |primitive b x| ≤ |x| := by
  rw [abs_of_nonneg (primitive_nonnegative hl hr x)]
  exact (primitive_linear_upper_bound hl hr x).trans (max_le (abs_nonneg x) (le_abs_self x))


def intervalCoordinate (b a x : ℝ) : ℝ := (x/(b*a)-theta)/(1-theta)

theorem intervalCoordinate_hasDerivAt (b a x : ℝ) :
    HasDerivAt (intervalCoordinate b a) (1/(b*a*(1-theta))) x := by
  convert (((hasDerivAt_id x).div_const (b*a)).sub_const theta).div_const (1-theta) using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring


end
end BfgsVerification.LScalarRamp
