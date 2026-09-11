import BfgsVerification.DScalarRamp
import Mathlib.Analysis.Convex.Deriv

open Set Filter
open scoped Topology

namespace BfgsVerification.DScalarNegative
open DScalarRamp
noncomputable section

def quadratic (x : ℝ) : ℝ := 1-3*(x+1)+3*(x+1)^2

def quadraticDerivative (x : ℝ) : ℝ := -3+6*(x+1)

def negative : ℝ → ℝ := DScalarRamp.join 0 (DScalarRamp.join (-1) quadratic (fun x => -x^3)) (fun _ => 0)

def first : ℝ → ℝ :=
  DScalarRamp.join 0 (DScalarRamp.join (-1) quadraticDerivative (fun x => -3*x^2)) (fun _ => 0)

def second : ℝ → ℝ := DScalarRamp.join 0 (DScalarRamp.join (-1) (fun _ => 6) (fun x => -6*x)) (fun _ => 0)

theorem quadratic_hasDerivAt (x : ℝ) : HasDerivAt quadratic (quadraticDerivative x) x := by
  convert ((hasDerivAt_const x 1).sub (((hasDerivAt_id x).add_const 1).const_mul 3)).add
    ((((hasDerivAt_id x).add_const 1).pow 2).const_mul 3) using 1 <;>
    dsimp [quadratic, quadraticDerivative] <;> ring

theorem quadraticDerivative_hasDerivAt (x : ℝ) : HasDerivAt quadraticDerivative 6 x := by
  convert (hasDerivAt_const x (-3)).add (((hasDerivAt_id x).add_const 1).const_mul 6)
    using 1 <;> dsimp [quadraticDerivative] <;> ring

theorem negative_hasDerivAt (x : ℝ) : HasDerivAt negative (first x) x := by
  apply join_hasDerivAt
  · apply join_hasDerivAt quadratic_hasDerivAt
    · intro x
      convert ((hasDerivAt_id x).pow 3).neg using 1 <;> dsimp only [id_eq] <;> ring
    · norm_num [quadratic]
    · norm_num [quadraticDerivative]
  · exact fun x => hasDerivAt_const x 0
  · norm_num [DScalarRamp.join]
  · norm_num [DScalarRamp.join]

theorem first_hasDerivAt (x : ℝ) : HasDerivAt first (second x) x := by
  apply join_hasDerivAt
  · apply join_hasDerivAt quadraticDerivative_hasDerivAt
    · intro x
      convert (((hasDerivAt_id x).pow 2).const_mul (-3)) using 1 <;> dsimp only [id_eq] <;> ring
    · norm_num [quadraticDerivative]
    · norm_num
  · exact fun x => hasDerivAt_const x 0
  · norm_num [DScalarRamp.join]
  · norm_num [DScalarRamp.join]

theorem deriv_negative : deriv negative = first := funext (fun x => (negative_hasDerivAt x).deriv)

theorem deriv_first : deriv first = second := funext (fun x => (first_hasDerivAt x).deriv)

theorem second_eq_clip (x : ℝ) : second x = 6*clip (-x) := by
  by_cases h0 : x ≤ 0
  · by_cases h1 : x ≤ -1
    · have h : 1 ≤ -x := by linarith
      simp [second, DScalarRamp.join, h0, h1, clip, min_eq_left h]
    · have h : -x ≤ 1 := by linarith
      have hp : 0 ≤ -x := by linarith
      simp [second, DScalarRamp.join, h0, h1, clip, min_eq_right h, max_eq_right hp]
  · have hx : -x ≤ 0 := by linarith
    have hx1 : -x ≤ 1 := by linarith
    simp [second, DScalarRamp.join, h0, clip, min_eq_right hx1, max_eq_left hx]

theorem second_continuous : Continuous second := by
  rw [funext second_eq_clip]
  exact continuous_const.mul (clip_lipschitz.continuous.comp continuous_neg)

theorem first_contDiff : ContDiff ℝ 1 first := by
  rw [contDiff_one_iff_deriv, deriv_first]
  exact ⟨fun x => (first_hasDerivAt x).differentiableAt, second_continuous⟩

theorem negative_contDiff : ContDiff ℝ 2 negative := by
  rw [show (2 : WithTop ℕ∞)=1+1 by norm_num, contDiff_succ_iff_deriv, deriv_negative]
  exact ⟨fun x => (negative_hasDerivAt x).differentiableAt, by norm_num, first_contDiff⟩

theorem second_bounds (x : ℝ) : 0 ≤ second x ∧ second x ≤ 6 := by
  rw [second_eq_clip]
  obtain ⟨h0,h1⟩ := clip_mem (-x)
  constructor <;> linarith

theorem actual_second_derivative_bounds (x : ℝ) :
    0 ≤ deriv (deriv negative) x ∧ deriv (deriv negative) x ≤ 6 := by
  rw [deriv_negative, deriv_first]
  exact second_bounds x

theorem negative_convex : ConvexOn ℝ univ negative := by
  apply Monotone.convexOn_univ_of_deriv (fun x => (negative_hasDerivAt x).differentiableAt)
  rw [deriv_negative]
  exact monotone_of_hasDerivAt_nonneg first_hasDerivAt (fun x => (second_bounds x).1)

theorem negative_eq_quadratic {x : ℝ} (hx : x ≤ -1) : negative x=quadratic x := by
  have h0 : x ≤ 0 := by linarith
  simp [negative, DScalarRamp.join, hx, h0]

theorem negative_eq_cubic {x : ℝ} (hl : -1 ≤ x) (hr : x ≤ 0) : negative x = -x^3 := by
  rcases eq_or_lt_of_le hl with h | h
  · rw [← h]
    norm_num [negative, DScalarRamp.join, quadratic]
  · simp [negative, DScalarRamp.join, hr, not_le.mpr h]

theorem negative_eq_zero {x : ℝ} (hx : 0 ≤ x) : negative x=0 := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]; norm_num [negative, DScalarRamp.join]
  · simp [negative, DScalarRamp.join, not_le.mpr h]

theorem negative_pos {x : ℝ} (hx : x < 0) : 0 < negative x := by
  by_cases h1 : x ≤ -1
  · rw [negative_eq_quadratic h1]
    dsimp [quadratic]
    nlinarith [sq_nonneg (x+1)]
  · rw [negative_eq_cubic (le_of_not_ge h1) hx.le]
    nlinarith [pow_pos (neg_pos.mpr hx) 3]

theorem negative_nonnegative (x : ℝ) : 0 ≤ negative x := by
  by_cases hx : x < 0
  · exact (negative_pos hx).le
  · rw [negative_eq_zero (le_of_not_gt hx)]

theorem negative_zero_iff (x : ℝ) : negative x=0 ↔ 0 ≤ x := by
  constructor
  · intro h
    by_contra hx
    have hp := negative_pos (lt_of_not_ge hx)
    linarith
  · exact negative_eq_zero

theorem first_eq_zero {x : ℝ} (hx : 0 ≤ x) : first x=0 := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]; norm_num [first, DScalarRamp.join]
  · simp [first, DScalarRamp.join, not_le.mpr h]

theorem second_eq_zero {x : ℝ} (hx : 0 ≤ x) : second x=0 := by
  rw [second_eq_clip]
  have h : -x ≤ 0 := by linarith
  have h1 : -x ≤ 1 := by linarith
  simp [clip, min_eq_right h1, max_eq_left h]

theorem first_negative {x : ℝ} (hx : x < 0) : first x < 0 := by
  by_cases h1 : x ≤ -1
  · simp only [first, DScalarRamp.join, if_pos hx.le, if_pos h1, quadraticDerivative]
    linarith
  · simp only [first, DScalarRamp.join, if_pos hx.le, if_neg h1]
    nlinarith [sq_pos_of_ne_zero hx.ne]

theorem second_abs_sub_le (x y : ℝ) : |second x-second y| ≤ 6*|x-y| := by
  have hc : |clip (-x)-clip (-y)| ≤ |x-y| := by
    have h := clip_lipschitz.dist_le_mul (-x) (-y)
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, neg_sub_neg, abs_sub_comm y x] using h
  rw [second_eq_clip, second_eq_clip, ← mul_sub, abs_mul]
  norm_num
  linarith

theorem second_lipschitz : LipschitzWith 6 second := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_ofNat] using second_abs_sub_le x y

theorem actual_second_derivative_lipschitz : LipschitzWith 6 (deriv (deriv negative)) := by
  rw [deriv_negative, deriv_first]
  exact second_lipschitz

theorem negative_lower_bound_left {x : ℝ} (hx : x ≤ -1) : -x ≤ negative x := by
  rw [negative_eq_quadratic hx]
  dsimp [quadratic]
  have h := mul_nonneg_of_nonpos_of_nonpos (show x+1 ≤ 0 by linarith) (show 3*x+1 ≤ 0 by linarith)
  nlinarith

theorem negative_coercive_atBot : Tendsto negative atBot atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_le_atBot (min (-1) (-B))] with x hx
  have hx1 : x ≤ -1 := hx.trans (min_le_left _ _)
  have hxB : x ≤ -B := hx.trans (min_le_right _ _)
  have h := negative_lower_bound_left hx1
  linarith

theorem negative_join_data :
    negative (-1)=1 ∧ first (-1)= -3 ∧ second (-1)=6 ∧
      negative 0=0 ∧ first 0=0 ∧ second 0=0 := by
  norm_num [negative, first, second, DScalarRamp.join, quadratic, quadraticDerivative]

end
end BfgsVerification.DScalarNegative
