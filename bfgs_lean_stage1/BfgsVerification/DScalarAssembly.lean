import BfgsVerification.DScalarCurvature
import BfgsVerification.DScalarIntervals
import BfgsVerification.DScalarJets
import BfgsVerification.DScalarPlateaus
import BfgsVerification.DScalarNegative
import Mathlib.Topology.Order.Compact

open Set Filter
open scoped Topology BigOperators

namespace BfgsVerification.DScalar
open DScalarGeometric
noncomputable section

theorem curvatureComponent_le_positiveCurvature {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) :
    curvatureComponent b n x ≤ positiveCurvature b x :=
  (summable_curvatureComponent hb x).le_tsum n (fun k _ => (curvatureComponent_bounds hb k x).1)

theorem positiveCurvature_attained {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    ∃ n : ℕ, positiveCurvature b x = curvatureComponent b n x := by
  by_cases hx : x ≤ 0
  · exact ⟨0, by rw [positiveCurvature_nonpos hl hr hx, curvatureComponent_nonpos hl hr hx]⟩
  by_cases hxb : b ≤ x
  · exact ⟨0, by rw [positiveCurvature_outer hl hr hxb,
      curvatureComponent_outer_zero hl hr 0 (by simpa only [scale_zero, mul_one] using hxb)]⟩
  obtain ⟨n,hlo,hhi⟩ := positive_interval_cover (by linarith : 0 < b) (lt_of_not_ge hx) (le_of_not_ge hxb)
  exact ⟨n, positiveCurvature_interval hl hr n hlo.le hhi⟩

theorem curvatureComponent_lipschitz {b : ℝ} (hb : 0 < b) (n : ℕ) :
    LipschitzWith ⟨139264/(5*b^2), by positivity⟩ (curvatureComponent b n) :=
  DScalarRamp.intervalCurvature_lipschitz hb (scale_pos n)

theorem positiveCurvature_sub_le {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x y : ℝ) :
    positiveCurvature b x-positiveCurvature b y ≤ 139264/(5*b^2)*|x-y| := by
  obtain ⟨n,hn⟩ := positiveCurvature_attained hl hr x
  have hb : 0 < b := by linarith
  have hc := curvatureComponent_le_positiveCurvature hb n y
  have hd := DScalarRamp.intervalCurvature_abs_sub_le hb (scale_pos n) x y
  change |curvatureComponent b n x-curvatureComponent b n y| ≤ _ at hd
  rw [hn]
  linarith [le_abs_self (curvatureComponent b n x-curvatureComponent b n y)]

theorem positiveCurvature_lipschitz {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) :
    LipschitzWith ⟨139264/(5*b^2), by positivity⟩ (positiveCurvature b) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [Real.dist_eq, NNReal.coe_mk]
  apply abs_le.mpr
  constructor
  · have h := positiveCurvature_sub_le hl hr y x
    rw [abs_sub_comm y x] at h
    linarith
  · exact positiveCurvature_sub_le hl hr x y

def phi (b x : ℝ) : ℝ := positivePart b x+DScalarNegative.negative x

def phiFirst (b x : ℝ) : ℝ := positiveSlope b x+DScalarNegative.first x

def phiSecond (b x : ℝ) : ℝ := positiveCurvature b x+DScalarNegative.second x

theorem phi_hasDerivAt {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    HasDerivAt (phi b) (phiFirst b x) x :=
  (positivePart_hasDerivAt hl hr x).add (DScalarNegative.negative_hasDerivAt x)

theorem phiFirst_hasDerivAt {b : ℝ} (hl : 2 ≤ b) (x : ℝ) :
    HasDerivAt (phiFirst b) (phiSecond b x) x :=
  (positiveSlope_hasDerivAt (by linarith) x).add (DScalarNegative.first_hasDerivAt x)

theorem deriv_phi {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) : deriv (phi b) = phiFirst b :=
  funext (fun x => (phi_hasDerivAt hl hr x).deriv)

theorem deriv_phiFirst {b : ℝ} (hl : 2 ≤ b) : deriv (phiFirst b) = phiSecond b :=
  funext (fun x => (phiFirst_hasDerivAt hl x).deriv)

theorem phi_contDiff {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) : ContDiff ℝ 2 (phi b) :=
  (positivePart_contDiff hl hr).add DScalarNegative.negative_contDiff

theorem phi_convex {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) : ConvexOn ℝ univ (phi b) :=
  (positivePart_convex hl hr).add DScalarNegative.negative_convex

theorem phi_nonnegative {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) : 0 ≤ phi b x :=
  add_nonneg (positivePart_nonnegative hl hr x) (DScalarNegative.negative_nonnegative x)

theorem phiSecond_eq_max {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    phiSecond b x = max (positiveCurvature b x) (DScalarNegative.second x) := by
  by_cases hx : x ≤ 0
  · rw [phiSecond, positiveCurvature_nonpos hl hr hx, zero_add,
      max_eq_right (DScalarNegative.second_bounds x).1]
  · rw [phiSecond, DScalarNegative.second_eq_zero (le_of_not_ge hx), add_zero,
      max_eq_left (positiveCurvature_nonnegative (by linarith) x)]

theorem phiSecond_bounds {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    0 ≤ phiSecond b x ∧ phiSecond b x ≤ max 6 (102/b) := by
  rw [phiSecond_eq_max hl hr]
  constructor
  · exact (positiveCurvature_nonnegative (by linarith) x).trans (le_max_left _ _)
  · exact max_le ((positiveCurvature_bounds hl hr x).2.trans (le_max_right _ _))
      ((DScalarNegative.second_bounds x).2.trans (le_max_left _ _))

theorem phiSecond_lipschitz {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) :
    LipschitzWith ⟨max 6 (139264/(5*b^2)), le_trans (by norm_num) (le_max_left _ _)⟩ (phiSecond b) := by
  rw [funext (phiSecond_eq_max hl hr)]
  simpa only [max_comm] using
    (positiveCurvature_lipschitz hl hr).max DScalarNegative.second_lipschitz

theorem phi_second_derivative_bounds {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    0 ≤ deriv (deriv (phi b)) x ∧ deriv (deriv (phi b)) x ≤ max 6 (102/b) := by
  rw [deriv_phi hl hr, deriv_phiFirst hl]
  exact phiSecond_bounds hl hr x

theorem phi_second_derivative_lipschitz {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) :
    LipschitzWith ⟨max 6 (139264/(5*b^2)), le_trans (by norm_num) (le_max_left _ _)⟩ (deriv (deriv (phi b))) := by
  rw [deriv_phi hl hr, deriv_phiFirst hl]
  exact phiSecond_lipschitz hl hr

theorem phi_eq_negative {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : x ≤ 0) :
    phi b x = DScalarNegative.negative x := by
  simp only [phi, positivePart_nonpos hl hr hx, zero_add]

theorem phi_eq_positive {b x : ℝ} (hx : 0 ≤ x) : phi b x=positivePart b x := by
  simp only [phi, DScalarNegative.negative_eq_zero hx, add_zero]

theorem phi_eq_outer {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : b ≤ x) :
    phi b x = 1+x-b := by
  rw [phi_eq_positive (by linarith), positivePart_outer hl hr hx]

theorem phi_coercive_atBot {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) : Tendsto (phi b) atBot atTop := by
  apply DScalarNegative.negative_coercive_atBot.congr'
  filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
  exact (phi_eq_negative hl hr hx).symm

theorem phi_coercive_atTop {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) : Tendsto (phi b) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop (max b (B+b))] with x hx
  rw [phi_eq_outer hl hr (le_trans (le_max_left _ _) hx)]
  have h := le_trans (le_max_right _ _) hx
  linarith

theorem phi_coercive {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) :
    Tendsto (phi b) (cocompact ℝ) atTop := by
  rw [cocompact_eq_atBot_atTop, tendsto_sup]
  exact ⟨phi_coercive_atBot hl hr, phi_coercive_atTop hl hr⟩


theorem phi_sublevel_bounds {b x a : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : phi b x ≤ a) :
    min (-1) (-a) ≤ x ∧ x ≤ max b (a+b) := by
  constructor
  · by_cases hx1 : x ≤ -1
    · have hh := DScalarNegative.negative_lower_bound_left hx1
      rw [phi_eq_negative hl hr (by linarith)] at hx
      exact (min_le_right _ _).trans (by linarith)
    · exact (min_le_left _ _).trans (le_of_not_ge hx1)
  · by_cases hxb : b ≤ x
    · rw [phi_eq_outer hl hr hxb] at hx
      exact (show x ≤ a+b by linarith).trans (le_max_right _ _)
    · exact (le_of_not_ge hxb).trans (le_max_left _ _)

theorem phi_sublevels_compact {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (a : ℝ) :
    IsCompact {x : ℝ | phi b x ≤ a} := by
  apply isCompact_Icc.of_isClosed_subset (isClosed_le (phi_contDiff hl hr).continuous continuous_const)
  intro x hx
  exact phi_sublevel_bounds hl hr hx


theorem phi_zero {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) : phi b 0 = 0 := by
  rw [phi_eq_positive (le_refl 0), positivePart_nonpos hl hr (le_refl 0)]

theorem phi_positive_of_ne_zero {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : x ≠ 0) :
    0 < phi b x := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · rw [phi_eq_negative hl hr hx.le]
    exact DScalarNegative.negative_pos hx
  · rw [phi_eq_positive hx.le]
    exact positivePart_positive hl hr hx

theorem phi_zero_iff {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (x : ℝ) : phi b x=0 ↔ x=0 := by
  constructor
  · intro h
    by_contra hx
    have hp := phi_positive_of_ne_zero hl hr hx
    linarith
  · intro h
    subst x
    exact phi_zero hl hr

theorem phi_unique_minimizer {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) :
    (∀ x : ℝ, phi b 0 ≤ phi b x) ∧ (∀ x : ℝ, phi b x=phi b 0 → x=0) := by
  rw [phi_zero hl hr]
  exact ⟨phi_nonnegative hl hr, fun x hx => (phi_zero_iff hl hr x).mp hx⟩

theorem phiFirst_negative {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : x < 0) :
    phiFirst b x < 0 := by
  rw [phiFirst, positiveSlope_nonpos hl hr hx.le, zero_add]
  exact DScalarNegative.first_negative hx

theorem phiFirst_positive {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : 0 < x) :
    0 < phiFirst b x := by
  rw [phiFirst, DScalarNegative.first_eq_zero hx.le, add_zero]
  have hb : 0 < b := by linarith
  by_cases hxb : b ≤ x
  · have hnode : positiveSlope b b=1 := by simpa only [scale_zero, mul_one, one_pow] using positiveSlope_node hl hr 0
    have h := positiveSlope_monotone hb hxb
    rw [hnode] at h
    linarith
  · obtain ⟨n,hlo,hhi⟩ := positive_interval_cover hb hx (le_of_not_ge hxb)
    rw [positiveSlope_interval hl hr n hlo.le hhi]
    have hp := (DScalarRamp.ramp_bounds b (coordinate b (scale n) x)).1
    have hs := scale_pos n
    norm_num [theta]
    positivity

theorem phi_interval {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hxlo : b*theta*scale m ≤ x) (hxhi : x ≤ b*scale m) :
    phi b x = (theta*scale m)^3 + b*(scale m)^3*(1-theta)*
      (theta^2*coordinate b (scale m) x +
        (1-theta^2)*DScalarRamp.primitive b (coordinate b (scale m) x)) := by
  have hx : 0 ≤ x := by
    have h : 0 < b*theta*scale m := mul_pos (mul_pos (by linarith) theta_pos) (scale_pos m)
    linarith
  rw [phi_eq_positive hx]
  exact positivePart_interval hl hr m hxlo hxhi

theorem phi_eq_negative_quadratic {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (hx : x ≤ -1) :
    phi b x = 1-3*(x+1)+3*(x+1)^2 := by
  rw [phi_eq_negative hl hr (by linarith), DScalarNegative.negative_eq_quadratic hx]
  rfl

theorem phi_eq_negative_cubic {b x : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34)
    (hxlo : -1 ≤ x) (hxhi : x ≤ 0) : phi b x = -x^3 := by
  rw [phi_eq_negative hl hr hxhi, DScalarNegative.negative_eq_cubic hxlo hxhi]

theorem phi_node {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ) :
    phi b (b*scale m)=(scale m)^3 := by
  rw [phi_eq_positive (mul_nonneg (by linarith) (scale_pos m).le)]
  exact positivePart_node hl hr m

theorem phiFirst_node {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ) :
    phiFirst b (b*scale m)=(scale m)^2 := by
  rw [phiFirst, DScalarNegative.first_eq_zero (mul_nonneg (by linarith) (scale_pos m).le), add_zero]
  exact positiveSlope_node hl hr m

theorem phiSecond_node {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ) :
    phiSecond b (b*scale m)=0 := by
  rw [phiSecond, DScalarNegative.second_eq_zero (mul_nonneg (by linarith) (scale_pos m).le), add_zero]
  exact positiveCurvature_node hl hr m


theorem phi_node_hasDerivAt {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ) :
    HasDerivAt (phi b) ((scale m)^2) (b*scale m) := by
  simpa only [phiFirst_node hl hr m] using phi_hasDerivAt hl hr (b*scale m)

theorem phi_node_second_hasDerivAt {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ) :
    HasDerivAt (deriv (phi b)) 0 (b*scale m) := by
  rw [deriv_phi hl hr]
  simpa only [phiSecond_node hl hr m] using phiFirst_hasDerivAt hl (b*scale m)

theorem phi_plateau {b h : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hh : |h| ≤ scale m/2) :
    phi b (b*scale m+h)=(scale m)^3+(scale m)^2*h := by
  have hs := scale_pos m
  have hb := mul_le_mul_of_nonneg_right hl hs.le
  have hhlo := (abs_le.mp hh).1
  rw [phi_eq_positive (by nlinarith)]
  exact positivePart_plateau hl hr m hh

end
end BfgsVerification.DScalar
