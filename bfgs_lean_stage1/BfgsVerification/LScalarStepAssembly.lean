import BfgsVerification.LScalarStepPlateaus

noncomputable section
open scoped Topology BigOperators
open Set Filter
namespace BfgsVerification.LScalarStep
open LScalarGeometric

def phi (b x : ℝ) : ℝ := positivePart b x+max 0 (-x)

theorem phi_convex {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) : ConvexOn ℝ univ (phi b) :=
  (positivePart_convex hl hr).add ((convexOn_const (0 : ℝ) convex_univ).sup (concaveOn_id convex_univ).neg)

theorem phi_continuous {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) : Continuous (phi b) :=
  continuous_iff_continuousOn_univ.mpr ((phi_convex hl hr).continuousOn isOpen_univ)

theorem phi_nonnegative (b x : ℝ) : 0 ≤ phi b x :=
  add_nonneg (positivePart_nonnegative b x) (le_max_left _ _)

theorem phi_eq_negative {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : x ≤ 0) : phi b x = -x := by
  simp [phi, positivePart_nonpos hl hr hx, max_eq_right (neg_nonneg.mpr hx)]

theorem phi_eq_positive {b x : ℝ} (hx : 0 ≤ x) : phi b x = positivePart b x := by
  simp [phi, max_eq_left (neg_nonpos.mpr hx)]

theorem phi_eq_outer {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : b ≤ x) :
    phi b x = 1+x-b := by
  rw [phi_eq_positive (by linarith), positivePart_outer hl hr hx]

theorem phi_zero {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) : phi b 0 = 0 := by
  rw [phi_eq_negative hl hr (le_refl 0), neg_zero]

theorem phi_positive_of_ne_zero {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : x ≠ 0) :
    0 < phi b x := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · rw [phi_eq_negative hl hr hx.le]
    linarith
  · rw [phi_eq_positive hx.le]
    exact positivePart_positive hl hr hx

theorem phi_unique_minimizer {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    (∀ x : ℝ, phi b 0 ≤ phi b x) ∧ (∀ x : ℝ, phi b x = phi b 0 → x = 0) := by
  rw [phi_zero hl hr]
  refine ⟨phi_nonnegative b, ?_⟩
  intro x hx
  by_contra hn
  have hp := phi_positive_of_ne_zero hl hr hn
  linarith

theorem phi_coercive_atBot {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    Tendsto (phi b) atBot atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_le_atBot (-max 0 B)] with x hx
  have h0 := le_max_left (0 : ℝ) B
  have hB := le_max_right (0 : ℝ) B
  rw [phi_eq_negative hl hr (by linarith)]
  linarith

theorem phi_coercive_atTop {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    Tendsto (phi b) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop (max b (B+b))] with x hx
  rw [phi_eq_outer hl hr ((le_max_left _ _).trans hx)]
  have h := (le_max_right b (B+b)).trans hx
  linarith

theorem phi_coercive {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    Tendsto (phi b) (cocompact ℝ) atTop := by
  rw [cocompact_eq_atBot_atTop, tendsto_sup]
  exact ⟨phi_coercive_atBot hl hr, phi_coercive_atTop hl hr⟩

theorem phi_node {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) :
    phi b (b*scale n) = (scale n)^2 := by
  rw [phi_eq_positive (mul_nonneg (by linarith) (scale_pos n).le), positivePart_node hl hr n]

theorem phi_plateau {b h : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ)
    (hh : |h| ≤ scale n/2) : phi b (b*scale n+h) = (scale n)^2+scale n*h := by
  have hs := scale_pos n
  have hhlo := (abs_le.mp hh).1
  have hb := mul_le_mul_of_nonneg_right hl hs.le
  rw [phi_eq_positive (by nlinarith)]
  simpa only [pow_one] using positivePart_plateau hl hr n hh

theorem phi_plateau_hasDerivAt {b h : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ)
    (hh : |h| < scale n/2) : HasDerivAt (phi b) (scale n) (b*scale n+h) := by
  have hc : HasDerivAt (fun y => (scale n)^2+scale n*(y-b*scale n)) (scale n) (b*scale n+h) := by
    convert (hasDerivAt_const (b*scale n+h) ((scale n)^2)).add
      (((hasDerivAt_id (b*scale n+h)).sub_const (b*scale n)).const_mul (scale n)) using 1 <;> ring
  apply hc.congr_of_eventuallyEq
  have hopen : IsOpen {y : ℝ | |y-b*scale n| < scale n/2} :=
    isOpen_lt ((continuous_id.sub continuous_const).abs) continuous_const
  have hmem : b*scale n+h ∈ {y : ℝ | |y-b*scale n| < scale n/2} := by
    simpa only [mem_setOf_eq, add_sub_cancel_left] using hh
  filter_upwards [hopen.mem_nhds hmem] with y hy
  have he := phi_plateau hl hr n (h := y-b*scale n) (show |y-b*scale n| ≤ scale n/2 from hy.le)
  simpa only [add_sub_cancel] using he

theorem phi_node_hasDerivAt {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) :
    HasDerivAt (phi b) (scale n) (b*scale n) := by
  simpa only [add_zero] using phi_plateau_hasDerivAt hl hr n (h := 0)
    (by rw [abs_zero]; have := scale_pos n; positivity)

end BfgsVerification.LScalarStep
