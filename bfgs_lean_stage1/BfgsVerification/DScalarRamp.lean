import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Piecewise
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace BfgsVerification.DScalarRamp

noncomputable section

def join (a : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ := if x ≤ a then f x else g x

theorem join_hasDerivAt {a : ℝ} {f g f' g' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hv : f a = g a) (hd : f' a = g' a) (x : ℝ) :
    HasDerivAt (join a f g) (join a f' g' x) x := by
  rcases lt_trichotomy x a with hx | hx | hx
  · simp only [join, if_pos hx.le]
    exact (hf x).congr_of_eventuallyEq (by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [join, le_of_lt (show y < a from hy)])
  · subst x
    have hl : HasDerivWithinAt (join a f g) (f' a) (Iic a) a :=
      (hf a).hasDerivWithinAt.congr (fun y hy => by simp [join, show y ≤ a from hy]) (by simp [join])
    have hr : HasDerivWithinAt (join a f g) (f' a) (Ioi a) a := by
      rw [hd]
      exact (hg a).hasDerivWithinAt.congr (fun y hy => by simp [join, not_le.mpr (show a < y from hy)])
        (by simp [join, hv])
    simpa [join] using hl.union hr
  · simp only [join, if_neg (not_le.mpr hx)]
    exact (hg x).congr_of_eventuallyEq (by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [join, not_le.mpr (show a < y from hy)])

def cubic (t : ℝ) : ℝ := 3*t^2-2*t^3

def cubicDerivative (t : ℝ) : ℝ := 6*t-6*t^2

def quartic (t : ℝ) : ℝ := t^3-t^4/2

def unitRamp : ℝ → ℝ := join 1 (join 0 (fun _ => 0) cubic) (fun _ => 1)

def unitDerivative : ℝ → ℝ :=
  join 1 (join 0 (fun _ => 0) cubicDerivative) (fun _ => 0)

def unitPrimitive : ℝ → ℝ :=
  join 1 (join 0 (fun _ => 0) quartic) (fun t => t-1/2)

theorem cubic_hasDerivAt (t : ℝ) : HasDerivAt cubic (cubicDerivative t) t := by
  convert (((hasDerivAt_id t).pow 2).const_mul 3).sub
    (((hasDerivAt_id t).pow 3).const_mul 2) using 1 <;> simp [cubic, cubicDerivative] <;> ring

theorem quartic_hasDerivAt (t : ℝ) : HasDerivAt quartic (cubic t) t := by
  convert ((hasDerivAt_id t).pow 3).sub (((hasDerivAt_id t).pow 4).div_const 2)
    using 1 <;> simp [cubic, quartic] <;> ring

theorem unitRamp_hasDerivAt (t : ℝ) :
    HasDerivAt unitRamp (unitDerivative t) t := by
  apply join_hasDerivAt
  · exact join_hasDerivAt (fun x => hasDerivAt_const x 0) cubic_hasDerivAt
      (by norm_num [cubic]) (by norm_num [cubicDerivative])
  · exact fun x => hasDerivAt_const x 1
  · norm_num [join, cubic]
  · norm_num [join, cubicDerivative]

theorem unitPrimitive_hasDerivAt (t : ℝ) :
    HasDerivAt unitPrimitive (unitRamp t) t := by
  apply join_hasDerivAt
  · exact join_hasDerivAt (fun x => hasDerivAt_const x 0) quartic_hasDerivAt
      (by norm_num [quartic]) (by norm_num [cubic])
  · exact fun x => (hasDerivAt_id x).sub_const (1/2)
  · norm_num [join, quartic]
  · norm_num [join, cubic]

def clip (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clip_mem (t : ℝ) : 0 ≤ clip t ∧ clip t ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem unitDerivative_eq (t : ℝ) : unitDerivative t = 6*clip t*(1-clip t) := by
  by_cases h0 : t ≤ 0
  · have h1 : t ≤ 1 := by linarith
    simp [unitDerivative, join, clip, h0, h1, min_eq_right h1, max_eq_left h0]
  · by_cases h1 : t ≤ 1
    · simp [unitDerivative, join, clip, h0, h1, min_eq_right h1,
        max_eq_right (le_of_not_ge h0), cubicDerivative]
      ring
    · have ht : 1 ≤ t := le_of_not_ge h1
      simp [unitDerivative, join, h1, clip, min_eq_left ht]

theorem unitDerivative_continuous : Continuous unitDerivative := by
  have he : unitDerivative = fun t => 6*clip t*(1-clip t) := funext unitDerivative_eq
  rw [he]
  unfold clip
  fun_prop

theorem unitRamp_contDiff : ContDiff ℝ 1 unitRamp := by
  rw [contDiff_one_iff_deriv]
  exact ⟨fun x => (unitRamp_hasDerivAt x).differentiableAt,
    by simpa only [funext (fun x => (unitRamp_hasDerivAt x).deriv)] using
      unitDerivative_continuous⟩

theorem unitPrimitive_contDiff : ContDiff ℝ 2 unitPrimitive := by
  rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (unitPrimitive_hasDerivAt x).differentiableAt, ?_, ?_⟩
  · norm_num
  · simpa only [funext (fun x => (unitPrimitive_hasDerivAt x).deriv)] using unitRamp_contDiff

theorem unitDerivative_bounds (t : ℝ) : 0 ≤ unitDerivative t ∧ unitDerivative t ≤ 3/2 := by
  rw [unitDerivative_eq]
  obtain ⟨h0,h1⟩ := clip_mem t
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) h0) (sub_nonneg.mpr h1)
  · nlinarith [sq_nonneg (clip t - 1/2)]

theorem unitRamp_bounds (t : ℝ) : 0 ≤ unitRamp t ∧ unitRamp t ≤ 1 := by
  by_cases h0 : t ≤ 0
  · have h1 : t ≤ 1 := by linarith
    simp [unitRamp, join, h0, h1]
  · by_cases h1 : t ≤ 1
    · simp only [unitRamp, join, if_pos h1, if_neg h0, cubic]
      have h : 0 ≤ t := le_of_not_ge h0
      constructor
      · nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 3-2*t by linarith)]
      · nlinarith [mul_nonneg (sq_nonneg (1-t)) (show 0 ≤ 1+2*t by linarith)]
    · simp [unitRamp, join, h1]

def theta : ℝ := 1/16

def epsilon : ℝ := 1/128

def center (b : ℝ) : ℝ := (1-(1+theta+theta^2)/b)/(1-theta^2)

def rampCoordinate (b x : ℝ) : ℝ := (x-center b+epsilon)/(2*epsilon)

def ramp (b x : ℝ) : ℝ := unitRamp (rampCoordinate b x)

def rampDerivative (b x : ℝ) : ℝ := 64 * unitDerivative (rampCoordinate b x)

def primitive (b x : ℝ) : ℝ := 2*epsilon * unitPrimitive (rampCoordinate b x)

theorem rampCoordinate_hasDerivAt (b x : ℝ) :
    HasDerivAt (rampCoordinate b) 64 x := by
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

theorem rampDerivative_bounds (b x : ℝ) : 0 ≤ rampDerivative b x ∧ rampDerivative b x ≤ 96 := by
  obtain ⟨h0,h1⟩ := unitDerivative_bounds (rampCoordinate b x)
  dsimp [rampDerivative]
  constructor <;> linarith


theorem ramp_eq_zero {b x : ℝ} (hx : x ≤ center b-epsilon) : ramp b x = 0 := by
  have ht : rampCoordinate b x ≤ 0 := by
    norm_num [rampCoordinate, epsilon] at *
    linarith
  have ht1 : rampCoordinate b x ≤ 1 := by linarith
  simp [ramp, unitRamp, join, ht, ht1]

theorem ramp_eq_one {b x : ℝ} (hx : center b+epsilon ≤ x) : ramp b x = 1 := by
  have ht : 1 ≤ rampCoordinate b x := by
    norm_num [rampCoordinate, epsilon] at *
    linarith
  rcases eq_or_lt_of_le ht with h | h
  · rw [ramp, ← h]
    norm_num [unitRamp, join, cubic]
  · simp [ramp, unitRamp, join, not_le.mpr h]

theorem ramp_eq_cubic {b x : ℝ} (hl : center b-epsilon < x)
    (hr : x < center b+epsilon) : ramp b x = cubic (rampCoordinate b x) := by
  have ht0 : 0 < rampCoordinate b x := by norm_num [rampCoordinate, epsilon] at *; linarith
  have ht1 : rampCoordinate b x < 1 := by norm_num [rampCoordinate, epsilon] at *; linarith
  simp [ramp, unitRamp, join, ht1.le, not_le.mpr ht0]

theorem primitive_eq_zero {b x : ℝ} (hx : x ≤ center b-epsilon) : primitive b x = 0 := by
  have ht : rampCoordinate b x ≤ 0 := by norm_num [rampCoordinate, epsilon] at *; linarith
  have ht1 : rampCoordinate b x ≤ 1 := by linarith
  simp [primitive, unitPrimitive, join, ht, ht1]

theorem primitive_eq_affine {b x : ℝ} (hx : center b+epsilon ≤ x) :
    primitive b x = x-center b := by
  have ht : 1 ≤ rampCoordinate b x := by norm_num [rampCoordinate, epsilon] at *; linarith
  have hu : unitPrimitive (rampCoordinate b x) = rampCoordinate b x-1/2 := by
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]; norm_num [unitPrimitive, join, quartic]
    · simp [unitPrimitive, join, not_le.mpr h]
  rw [primitive, hu]
  dsimp [rampCoordinate, epsilon]
  ring

theorem primitive_eq_quartic {b x : ℝ} (hl : center b-epsilon < x)
    (hr : x < center b+epsilon) :
    primitive b x = 2*epsilon*quartic (rampCoordinate b x) := by
  have ht0 : 0 < rampCoordinate b x := by norm_num [rampCoordinate, epsilon] at *; linarith
  have ht1 : rampCoordinate b x < 1 := by norm_num [rampCoordinate, epsilon] at *; linarith
  simp [primitive, unitPrimitive, join, ht1.le, not_le.mpr ht0]

def lowerLength (b : ℝ) : ℝ := b*(1-theta)*(1-center b-epsilon)

def upperLength (b : ℝ) : ℝ := b*(1-theta)*(center b-epsilon)/theta

theorem center_formula {b : ℝ} (hb : b ≠ 0) : center b = (256*b-273)/(255*b) := by
  dsimp [center, theta]
  field_simp
  <;> ring

theorem center_bounds {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) :
    epsilon < center b ∧ center b < 1-epsilon := by
  have hb : 0 < b := by linarith
  rw [center_formula hb.ne']
  dsimp [epsilon]
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith

theorem transition_inside {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) :
    0 < center b-epsilon ∧ center b-epsilon < center b+epsilon ∧ center b+epsilon < 1 := by
  obtain ⟨h0,h1⟩ := center_bounds hl hr
  dsimp [epsilon] at *
  constructor
  · linarith
  constructor <;> linarith

theorem lowerLength_formula {b : ℝ} (hb : b ≠ 0) :
    lowerLength b = 273/272 - 383*b/34816 := by
  rw [lowerLength, center_formula hb]
  dsimp [theta, epsilon]
  field_simp
  <;> ring

theorem upperLength_formula {b : ℝ} (hb : b ≠ 0) :
    upperLength b = 32513*b/2176 - 273/17 := by
  rw [upperLength, center_formula hb]
  dsimp [theta, epsilon]
  field_simp
  <;> ring

theorem plateau_lengths {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) :
    1/2 < lowerLength b ∧ 1/2 < upperLength b := by
  have hb : b ≠ 0 := by linarith
  rw [lowerLength_formula hb, upperLength_formula hb]
  constructor <;> nlinarith

theorem matching_identity {b : ℝ} (hb : b ≠ 0) :
    theta^2+(1-theta^2)*(1-center b) = (1+theta+theta^2)/b := by
  dsimp [center, theta]
  field_simp
  <;> ring

theorem primitive_eq_integral {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    primitive b x = ∫ t in (0 : ℝ)..x, ramp b t := by
  have hz : primitive b 0 = 0 := primitive_eq_zero (transition_inside hl hr).1.le
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => primitive_hasDerivAt b t) ((ramp_contDiff b).continuous.intervalIntegrable 0 x), hz,
    sub_zero]

theorem integral_ramp {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) :
    ∫ t in (0 : ℝ)..1, ramp b t = 1-center b := by
  rw [← primitive_eq_integral hl hr, primitive_eq_affine (transition_inside hl hr).2.2.le]

theorem clip_lipschitz : LipschitzWith 1 clip :=
  (LipschitzWith.id.const_min 1).const_max 0

theorem unitDerivative_abs_sub_le (u v : ℝ) :
    |unitDerivative u-unitDerivative v| ≤ 6*|u-v| := by
  obtain ⟨hu0,hu1⟩ := clip_mem u
  obtain ⟨hv0,hv1⟩ := clip_mem v
  have hc : |clip u-clip v| ≤ |u-v| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using clip_lipschitz.dist_le_mul u v
  have hs : |1-clip u-clip v| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    |unitDerivative u-unitDerivative v| = 6*|clip u-clip v| *|1-clip u-clip v| := by
      rw [unitDerivative_eq, unitDerivative_eq]
      rw [show 6*clip u*(1-clip u)-6*clip v*(1-clip v) =
        6*(clip u-clip v)*(1-clip u-clip v) by ring, abs_mul, abs_mul]
      norm_num
    _ ≤ 6*|clip u-clip v| := by nlinarith [mul_nonneg (abs_nonneg (clip u-clip v)) (sub_nonneg.mpr hs)]
    _ ≤ 6*|u-v| := by linarith

theorem rampCoordinate_sub (b x y : ℝ) : rampCoordinate b x-rampCoordinate b y = 64*(x-y) := by
  dsimp [rampCoordinate, epsilon]
  ring

theorem rampDerivative_abs_sub_le (b x y : ℝ) :
    |rampDerivative b x-rampDerivative b y| ≤ 24576*|x-y| := by
  have h := unitDerivative_abs_sub_le (rampCoordinate b x) (rampCoordinate b y)
  rw [rampCoordinate_sub, abs_mul] at h
  norm_num at h
  dsimp [rampDerivative]
  rw [← mul_sub, abs_mul]
  norm_num
  linarith

theorem rampDerivative_lipschitz (b : ℝ) : LipschitzWith 24576 (rampDerivative b) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_ofNat] using rampDerivative_abs_sub_le b x y

theorem ramp_second_derivative_bound (b x : ℝ) : |deriv (deriv (ramp b)) x| ≤ 24576 := by
  have hd : deriv (ramp b) = rampDerivative b := funext (fun t => (ramp_hasDerivAt b t).deriv)
  rw [hd]
  simpa only [Real.norm_eq_abs, NNReal.coe_ofNat] using
    (norm_deriv_le_of_lipschitz (x₀ := x) (rampDerivative_lipschitz b))


theorem ramp_monotone (b : ℝ) : Monotone (ramp b) :=
  monotone_of_hasDerivAt_nonneg (ramp_hasDerivAt b) (fun x => (rampDerivative_bounds b x).1)

theorem deriv_ramp_bounds (b x : ℝ) : 0 ≤ deriv (ramp b) x ∧ deriv (ramp b) x ≤ 96 := by
  rw [(ramp_hasDerivAt b x).deriv]
  exact rampDerivative_bounds b x

theorem rampDerivative_eq_zero_left {b x : ℝ} (hx : x ≤ center b-epsilon) :
    rampDerivative b x = 0 := by
  have ht : rampCoordinate b x ≤ 0 := by norm_num [rampCoordinate, epsilon] at *; linarith
  have ht1 : rampCoordinate b x ≤ 1 := by linarith
  simp [rampDerivative, unitDerivative, join, ht, ht1]

theorem rampDerivative_eq_zero_right {b x : ℝ} (hx : center b+epsilon ≤ x) :
    rampDerivative b x = 0 := by
  have ht : 1 ≤ rampCoordinate b x := by norm_num [rampCoordinate, epsilon] at *; linarith
  rcases eq_or_lt_of_le ht with h | h
  · rw [rampDerivative, ← h]; norm_num [unitDerivative, join, cubicDerivative]
  · simp [rampDerivative, unitDerivative, join, not_le.mpr h]

theorem endpoint_data {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) :
    ramp b 0 = 0 ∧ ramp b 1 = 1 ∧ rampDerivative b 0 = 0 ∧ rampDerivative b 1 = 0 ∧
    primitive b 0 = 0 ∧ primitive b 1 = 1-center b := by
  obtain ⟨h0,_,h1⟩ := transition_inside hl hr
  exact ⟨ramp_eq_zero h0.le, ramp_eq_one h1.le, rampDerivative_eq_zero_left h0.le,
    rampDerivative_eq_zero_right h1.le, primitive_eq_zero h0.le, primitive_eq_affine h1.le⟩

theorem cubicDerivative_hasDerivAt (t : ℝ) :
    HasDerivAt cubicDerivative (6-12*t) t := by
  convert ((hasDerivAt_id t).const_mul 6).sub (((hasDerivAt_id t).pow 2).const_mul 6)
    using 1 <;> simp [cubicDerivative] <;> ring

theorem unitDerivative_hasDerivAt_inside {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasDerivAt unitDerivative (6-12*t) t := by
  apply (cubicDerivative_hasDerivAt t).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds h0 h1] with z hz
  simp [unitDerivative, join, (show z < 1 from hz.2).le, not_le.mpr hz.1]

theorem rampDerivative_hasDerivAt_inside {b x : ℝ} (hl : center b-epsilon < x)
    (hr : x < center b+epsilon) :
    HasDerivAt (rampDerivative b) (4096*(6-12*rampCoordinate b x)) x := by
  have h0 : 0 < rampCoordinate b x := by norm_num [rampCoordinate, epsilon] at *; linarith
  have h1 : rampCoordinate b x < 1 := by norm_num [rampCoordinate, epsilon] at *; linarith
  convert ((unitDerivative_hasDerivAt_inside h0 h1).comp x
    (rampCoordinate_hasDerivAt b x)).const_mul 64 using 1 <;> dsimp [rampDerivative] <;> ring

theorem primitive_third_derivative_inside {b x : ℝ} (hl : center b-epsilon < x)
    (hr : x < center b+epsilon) :
    HasDerivAt (deriv (deriv (primitive b))) (4096*(6-12*rampCoordinate b x)) x := by
  have h1 : deriv (primitive b) = ramp b := funext (fun t => (primitive_hasDerivAt b t).deriv)
  have h2 : deriv (ramp b) = rampDerivative b := funext (fun t => (ramp_hasDerivAt b t).deriv)
  rw [h1, h2]
  exact rampDerivative_hasDerivAt_inside hl hr

theorem rampDerivative_inside_bound {b x : ℝ} (hl : center b-epsilon < x)
    (hr : x < center b+epsilon) : |4096*(6-12*rampCoordinate b x)| ≤ 24576 := by
  simpa only [Real.norm_eq_abs, NNReal.coe_ofNat] using
    (rampDerivative_hasDerivAt_inside hl hr).le_of_lipschitz (rampDerivative_lipschitz b)

def intervalCoordinate (b a x : ℝ) : ℝ := (x/(b*a)-theta)/(1-theta)

def intervalCurvature (b a x : ℝ) : ℝ :=
  a*(1+theta)/b * rampDerivative b (intervalCoordinate b a x)

theorem intervalCurvature_bounds {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (x : ℝ) :
    0 ≤ intervalCurvature b a x ∧ intervalCurvature b a x ≤ 102*a/b := by
  obtain ⟨h0,h1⟩ := rampDerivative_bounds b (intervalCoordinate b a x)
  dsimp [intervalCurvature, theta]
  have hc : 0 ≤ a*(1+(1/16:ℝ))/b := by positivity
  constructor
  · exact mul_nonneg hc h0
  · calc
      a*(1+(1/16:ℝ))/b * rampDerivative b (intervalCoordinate b a x) ≤
          a*(1+(1/16:ℝ))/b * 96 := mul_le_mul_of_nonneg_left h1 hc
      _ = 102*a/b := by ring

theorem intervalCoordinate_sub (b a x y : ℝ) :
    intervalCoordinate b a x-intervalCoordinate b a y = (x-y)/(b*a*(1-theta)) := by
  dsimp [intervalCoordinate]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem intervalCurvature_abs_sub_le {b a : ℝ} (hb : 0 < b) (ha : 0 < a) (x y : ℝ) :
    |intervalCurvature b a x-intervalCurvature b a y| ≤ (139264/(5*b^2))*|x-y| := by
  have h := rampDerivative_abs_sub_le b (intervalCoordinate b a x) (intervalCoordinate b a y)
  have hθ : 0 < 1-theta := by norm_num [theta]
  have hc : 0 < a*(1+theta)/b := by dsimp [theta]; positivity
  rw [intervalCoordinate_sub, abs_div, abs_of_pos (mul_pos (mul_pos hb ha) hθ)] at h
  dsimp [intervalCurvature]
  rw [← mul_sub, abs_mul, abs_of_pos hc]
  calc
    a*(1+theta)/b * |rampDerivative b (intervalCoordinate b a x)-rampDerivative b (intervalCoordinate b a y)|
      ≤ a*(1+theta)/b * (24576*(|x-y|/(b*a*(1-theta)))) :=
        mul_le_mul_of_nonneg_left h hc.le
    _ = (139264/(5*b^2))*|x-y| := by
      dsimp [theta]
      field_simp
      <;> ring

theorem intervalCurvature_lipschitz {b a : ℝ} (hb : 0 < b) (ha : 0 < a) :
    LipschitzWith ⟨139264/(5*b^2), by positivity⟩ (intervalCurvature b a) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_mk] using intervalCurvature_abs_sub_le hb ha x y


theorem primitive_monotone (b : ℝ) : Monotone (primitive b) :=
  monotone_of_hasDerivAt_nonneg (primitive_hasDerivAt b) (fun x => (ramp_bounds b x).1)

theorem identity_sub_primitive_monotone (b : ℝ) : Monotone (fun x => x-primitive b x) := by
  apply monotone_of_hasDerivAt_nonneg
    (fun x => (hasDerivAt_id x).sub (primitive_hasDerivAt b x))
  intro x
  exact sub_nonneg.mpr (ramp_bounds b x).2

theorem primitive_nonnegative {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    0 ≤ primitive b x := by
  have hz := (endpoint_data hl hr).2.2.2.2.1
  by_cases hx : x ≤ 0
  · rw [primitive_eq_zero (hx.trans (transition_inside hl hr).1.le)]
  · have h := primitive_monotone b (le_of_not_ge hx)
    simpa only [hz] using h

theorem primitive_linear_upper_bound {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) :
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

theorem primitive_abs_bound {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    |primitive b x| ≤ |x| := by
  rw [abs_of_nonneg (primitive_nonnegative hl hr x)]
  exact (primitive_linear_upper_bound hl hr x).trans (max_le (abs_nonneg x) (le_abs_self x))


theorem intervalCoordinate_hasDerivAt (b a x : ℝ) :
    HasDerivAt (intervalCoordinate b a) (1/(b*a*(1-theta))) x := by
  convert (((hasDerivAt_id x).div_const (b*a)).sub_const theta).div_const (1-theta) using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem intervalCurvature_hasDerivAt_inside {b a x : ℝ} (hb : 0 < b) (ha : 0 < a)
    (hl : center b-epsilon < intervalCoordinate b a x)
    (hr : intervalCoordinate b a x < center b+epsilon) :
    HasDerivAt (intervalCurvature b a)
      ((1+theta)/(b^2*(1-theta)) * (4096*(6-12*rampCoordinate b (intervalCoordinate b a x)))) x := by
  convert ((rampDerivative_hasDerivAt_inside hl hr).comp x
    (intervalCoordinate_hasDerivAt b a x)).const_mul (a*(1+theta)/b) using 1
  dsimp [theta]
  field_simp
  <;> ring

theorem intervalCurvature_derivative_inside_bound {b a x : ℝ} (hb : 0 < b) (ha : 0 < a)
    (hl : center b-epsilon < intervalCoordinate b a x)
    (hr : intervalCoordinate b a x < center b+epsilon) :
    |(1+theta)/(b^2*(1-theta)) * (4096*(6-12*rampCoordinate b (intervalCoordinate b a x)))|
      ≤ 139264/(5*b^2) := by
  simpa only [Real.norm_eq_abs, NNReal.coe_mk] using
    (intervalCurvature_hasDerivAt_inside hb ha hl hr).le_of_lipschitz (intervalCurvature_lipschitz hb ha)


theorem primitive_second_hasDerivAt (b x : ℝ) :
    HasDerivAt (deriv (primitive b)) (rampDerivative b x) x := by
  rw [funext (fun t => (primitive_hasDerivAt b t).deriv)]
  exact ramp_hasDerivAt b x

theorem primitive_secondDerivative_lipschitz (b : ℝ) :
    LipschitzWith 24576 (deriv (deriv (primitive b))) := by
  rw [funext (fun t => (primitive_second_hasDerivAt b t).deriv)]
  exact rampDerivative_lipschitz b

end
end BfgsVerification.DScalarRamp
