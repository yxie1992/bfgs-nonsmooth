import BfgsVerification.LScalarJets
import BfgsVerification.LScalarPlateaus
import BfgsVerification.LScalarLipschitz

noncomputable section
open scoped Topology BigOperators
open Set Filter
namespace BfgsVerification.LScalar
open LScalarGeometric

def negative (x : ℝ) : ℝ := if x ≤ 0 then x^2/2 else 0

def negativeSlope (x : ℝ) : ℝ := min x 0

theorem negative_hasDerivAt (x : ℝ) : HasDerivAt negative (negativeSlope x) x := by
  have h := DScalarRamp.join_hasDerivAt (a := 0)
    (fun y => ((hasDerivAt_id y).pow 2).div_const 2)
    (fun y => hasDerivAt_const y 0) (by norm_num) (by norm_num) x
  convert h using 1
  by_cases hx : x ≤ 0
  · simp [negativeSlope, DScalarRamp.join, min_eq_left hx, hx]
  · simp [negativeSlope, DScalarRamp.join, min_eq_right (le_of_not_ge hx), hx]

theorem negativeSlope_continuous : Continuous negativeSlope := continuous_id.min continuous_const

theorem negative_contDiff : ContDiff ℝ 1 negative := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (negative_hasDerivAt x).differentiableAt, ?_⟩
  simpa only [funext (fun x => (negative_hasDerivAt x).deriv)] using negativeSlope_continuous

theorem negativeSlope_lipschitz : LipschitzWith 1 negativeSlope := LipschitzWith.id.min_const 0

theorem negative_convex : ConvexOn ℝ univ negative := by
  apply Monotone.convexOn_univ_of_deriv (fun x => (negative_hasDerivAt x).differentiableAt)
  rw [funext (fun x => (negative_hasDerivAt x).deriv)]
  exact monotone_id.min monotone_const

theorem negative_nonnegative (x : ℝ) : 0 ≤ negative x := by
  unfold negative
  split_ifs <;> positivity

theorem negative_nonneg_zero {x : ℝ} (hx : 0 ≤ x) : negative x = 0 := by
  by_cases he : x = 0
  · simp [he, negative]
  · simp [negative, not_le.mpr (lt_of_le_of_ne hx (Ne.symm he))]

def phi (b x : ℝ) : ℝ := positivePart b x+negative x

def phiFirst (b x : ℝ) : ℝ := positiveSlope b x+negativeSlope x

theorem phi_hasDerivAt {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    HasDerivAt (phi b) (phiFirst b x) x :=
  (positivePart_hasDerivAt hl hr x).add (negative_hasDerivAt x)

theorem deriv_phi {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) : deriv (phi b) = phiFirst b :=
  funext (fun x => (phi_hasDerivAt hl hr x).deriv)

theorem phi_contDiff {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) : ContDiff ℝ 1 (phi b) :=
  (positivePart_contDiff hl hr).add negative_contDiff

theorem phiFirst_lipschitz {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    LipschitzWith (⟨768/b, by positivity⟩+1) (phiFirst b) :=
  (positiveSlope_lipschitz hl hr).add negativeSlope_lipschitz

theorem phi_derivative_lipschitz {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    LipschitzWith (⟨768/b, by positivity⟩+1) (deriv (phi b)) := by
  rw [deriv_phi hl hr]
  exact phiFirst_lipschitz hl hr

theorem phi_convex {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) : ConvexOn ℝ univ (phi b) :=
  (positivePart_convex hl hr).add negative_convex

theorem phi_nonnegative {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (x : ℝ) : 0 ≤ phi b x :=
  add_nonneg (positivePart_nonnegative hl hr x) (negative_nonnegative x)

theorem phi_eq_negative {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : x ≤ 0) :
    phi b x = x^2/2 := by
  simp [phi, positivePart_nonpos hl hr hx, negative, hx]

theorem phi_eq_positive {b x : ℝ} (hx : 0 ≤ x) : phi b x = positivePart b x := by
  simp only [phi, negative_nonneg_zero hx, add_zero]

theorem phiFirst_eq_negative {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : x ≤ 0) :
    phiFirst b x = x := by
  simp [phiFirst, positiveSlope_nonpos hl hr hx, negativeSlope, min_eq_left hx]

theorem phiFirst_eq_positive {b x : ℝ} (hx : 0 ≤ x) : phiFirst b x = positiveSlope b x := by
  simp [phiFirst, negativeSlope, min_eq_right hx]

theorem phi_eq_outer {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : b ≤ x) :
    phi b x = 1+x-b := by
  rw [phi_eq_positive (by linarith), positivePart_outer hl hr hx]

theorem phi_zero {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) : phi b 0 = 0 := by
  rw [phi_eq_negative hl hr (le_refl 0)]
  norm_num

theorem phiFirst_zero {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) : phiFirst b 0 = 0 :=
  phiFirst_eq_negative hl hr (le_refl 0)

theorem phi_positive_of_ne_zero {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : x ≠ 0) :
    0 < phi b x := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · rw [phi_eq_negative hl hr hx.le]
    positivity
  · rw [phi_eq_positive hx.le]
    exact positivePart_positive hl hr hx

theorem phi_unique_minimizer {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    (∀ x : ℝ, phi b 0 ≤ phi b x) ∧ (∀ x : ℝ, phi b x = phi b 0 → x = 0) := by
  rw [phi_zero hl hr]
  refine ⟨phi_nonnegative hl hr, ?_⟩
  intro x hx
  by_contra hn
  have hp := phi_positive_of_ne_zero hl hr hn
  linarith

theorem phi_node {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) :
    phi b (b*scale n) = (scale n)^2 := by
  rw [phi_eq_positive (mul_nonneg (by linarith) (scale_pos n).le)]
  exact positivePart_node hl hr n

theorem phi_node_hasDerivAt {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) :
    HasDerivAt (phi b) (scale n) (b*scale n) := by
  have he : phiFirst b (b*scale n) = scale n := by
    rw [phiFirst_eq_positive (mul_nonneg (by linarith) (scale_pos n).le), positiveSlope_node hl hr n, pow_one]
  simpa only [he] using phi_hasDerivAt hl hr (b*scale n)

theorem phi_plateau {b h : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ)
    (hh : |h| ≤ scale n/2) :
    phi b (b*scale n+h) = (scale n)^2+scale n*h := by
  have hs := scale_pos n
  have hhlo := (abs_le.mp hh).1
  have hb := mul_le_mul_of_nonneg_right hl hs.le
  rw [phi_eq_positive (by nlinarith)]
  simpa only [pow_one] using positivePart_plateau hl hr n hh

theorem phi_interval {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ)
    (hxlo : b*theta*scale n ≤ x) (hxhi : x ≤ b*scale n) :
    phi b x = (theta*scale n)^2 + b*(scale n)^2*(1-theta)*
      (theta*coordinate b (scale n) x +
        (1-theta)*LScalarRamp.primitive b (coordinate b (scale n) x)) := by
  have hx : 0 ≤ x := (mul_pos (mul_pos (by linarith : 0 < b) theta_pos) (scale_pos n)).le.trans hxlo
  rw [phi_eq_positive hx]
  simpa only [pow_one] using positivePart_interval hl hr n hxlo hxhi

theorem phi_contDiffAt_pos {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : 0 < x) :
    ContDiffAt ℝ 2 (phi b) x := by
  apply (positivePart_contDiffAt_pos hl hr hx).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact phi_eq_positive (show 0 ≤ y from hy.le)

theorem phi_contDiffAt_neg {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : x < 0) :
    ContDiffAt ℝ 2 (phi b) x := by
  have hc : ContDiff ℝ 2 (fun y : ℝ => y^2/2) := by simp only [div_eq_mul_inv]; fun_prop
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact phi_eq_negative hl hr (show y ≤ 0 from hy.le)

end BfgsVerification.LScalar
