import BfgsVerification.LScalarTargets

noncomputable section
open scoped Topology BigOperators
open Set Filter
namespace BfgsVerification.LScalarStep
open LScalarGeometric

def hinge (b : ℝ) (n : ℕ) (x : ℝ) : ℝ := max 0 (x-LScalar.peak b n)
def component (b : ℝ) (n : ℕ) (x : ℝ) : ℝ := (1-theta)*scale n*hinge b n x
def positivePart (b x : ℝ) : ℝ := ∑' n : ℕ, component b n x

theorem component_nonnegative (b : ℝ) (n : ℕ) (x : ℝ) : 0 ≤ component b n x :=
  mul_nonneg (mul_nonneg (sub_pos.mpr theta_lt_one).le (scale_pos n).le) (le_max_left _ _)

theorem component_nonpos {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : x ≤ 0) (n : ℕ) :
    component b n x = 0 := by
  have hp := LScalar.peak_positive hl hr n
  simp [component, hinge, max_eq_left (show x-LScalar.peak b n ≤ 0 by linarith)]

theorem component_norm_bound {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) (x : ℝ) :
    ‖component b n x‖ ≤ (1-theta)*scale n*‖x‖ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (component_nonnegative b n x), component, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left
  · apply max_le (abs_nonneg x)
    have hp := LScalar.peak_positive hl hr n
    exact (by linarith : x-LScalar.peak b n ≤ x).trans (le_abs_self x)
  · exact mul_nonneg (sub_pos.mpr theta_lt_one).le (scale_pos n).le

theorem summable_component {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    Summable (fun n => component b n x) := by
  have hs : Summable (fun n => (1-theta)*scale n*‖x‖) := by
    simpa only [pow_one] using ((summable_scale_power (by omega : 0 < 1)).mul_left (1-theta)).mul_right ‖x‖
  exact Summable.of_norm_bounded _ hs (fun n => component_norm_bound hl hr n x)

theorem component_convex (b : ℝ) (n : ℕ) : ConvexOn ℝ univ (component b n) := by
  have ha : ConvexOn ℝ univ (fun x : ℝ => x-LScalar.peak b n) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a c ha hc hac
    simp only [smul_eq_mul]
    apply le_of_eq
    calc
      a*x+c*y-LScalar.peak b n = a*x+c*y-(a+c)*LScalar.peak b n := by rw [hac]; ring
      _ = a*(x-LScalar.peak b n)+c*(y-LScalar.peak b n) := by ring
  have hc : ConvexOn ℝ univ (fun x : ℝ => max 0 (x-LScalar.peak b n)) :=
    (convexOn_const (0 : ℝ) convex_univ).sup ha
  exact hc.smul (mul_nonneg (sub_pos.mpr theta_lt_one).le (scale_pos n).le)

theorem positivePart_convex {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    ConvexOn ℝ univ (positivePart b) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a c ha hc hac
  have hs := (summable_component hl hr x).mul_left a
  have ht := (summable_component hl hr y).mul_left c
  change (∑' n, component b n (a*x+c*y)) ≤ a*(∑' n, component b n x)+c*(∑' n, component b n y)
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add hs ht]
  apply (summable_component hl hr _).tsum_le_tsum _ (hs.add ht)
  intro n
  exact (component_convex b n).2 hx hy ha hc hac

theorem positivePart_nonnegative (b x : ℝ) : 0 ≤ positivePart b x :=
  tsum_nonneg (fun n => component_nonnegative b n x)

theorem positivePart_nonpos {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : x ≤ 0) :
    positivePart b x = 0 := by simp only [positivePart, component_nonpos hl hr hx, tsum_zero]

theorem peak_formula {b : ℝ} (hb : 0 < b) (n : ℕ) :
    LScalar.peak b n = (1+theta)*(b-1)*scale n := by
  rw [LScalar.peak, LScalarRamp.center_formula hb.ne']
  dsimp [theta]
  field_simp [hb.ne']
  <;> ring

theorem component_affine_of_peak {b x : ℝ} (hb : 0 < b) (n : ℕ)
    (hx : LScalar.peak b n ≤ x) :
    component b n x = (1-theta)*scale n*x+(1-b)*(1-theta^2)*(scale n)^2 := by
  rw [component, hinge, max_eq_right (sub_nonneg.mpr hx), peak_formula hb n]
  ring

theorem component_zero_of_coordinate {b x : ℝ} (hb : 0 < b) (n : ℕ)
    (hx : coordinate b (scale n) x ≤ LScalarRamp.center b) : component b n x = 0 := by
  have hp := (LScalar.coordinate_le_iff hb (scale_pos n) (LScalarRamp.center b)).mp hx
  change x ≤ LScalar.peak b n at hp
  simp [component, hinge, max_eq_left (sub_nonpos.mpr hp)]

theorem component_affine_of_coordinate {b x : ℝ} (hb : 0 < b) (n : ℕ)
    (hx : LScalarRamp.center b ≤ coordinate b (scale n) x) :
    component b n x = (1-theta)*scale n*x+(1-b)*(1-theta^2)*(scale n)^2 := by
  apply component_affine_of_peak hb
  exact (LScalar.coordinate_ge_iff hb (scale_pos n) (LScalarRamp.center b)).mp hx

def primitive (b ξ : ℝ) : ℝ := max 0 (ξ-LScalarRamp.center b)

theorem component_source_formula {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) :
    component b n x = b*(scale n)^2*(1-theta)^2*primitive b (coordinate b (scale n) x) := by
  by_cases hx : coordinate b (scale n) x ≤ LScalarRamp.center b
  · rw [component_zero_of_coordinate hb n hx, primitive, max_eq_left (sub_nonpos.mpr hx), mul_zero]
  · have hx' := le_of_not_ge hx
    rw [component_affine_of_coordinate hb n hx', primitive, max_eq_right (sub_nonneg.mpr hx'),
      LScalarRamp.center_formula hb.ne']
    have ha := (scale_pos n).ne'
    generalize scale n = a at *
    dsimp [coordinate, theta]
    field_simp [hb.ne', ha]
    <;> ring

theorem primitive_eq_zero {b x : ℝ} (hx : x ≤ LScalarRamp.center b) : primitive b x = 0 :=
  max_eq_left (sub_nonpos.mpr hx)

theorem primitive_eq_affine {b x : ℝ} (hx : LScalarRamp.center b ≤ x) : primitive b x = x-LScalarRamp.center b :=
  max_eq_right (sub_nonneg.mpr hx)

end BfgsVerification.LScalarStep
