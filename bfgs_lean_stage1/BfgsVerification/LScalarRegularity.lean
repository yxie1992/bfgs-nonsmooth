import BfgsVerification.LScalarAssembly

noncomputable section
open scoped Topology BigOperators
open Set Filter
namespace BfgsVerification.LScalar
open LScalarGeometric

theorem phi_coercive_atBot {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    Tendsto (phi b) atBot atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_le_atBot (-max 1 (2*B))] with x hx
  have h1 : x ≤ -1 := by have := le_max_left (1 : ℝ) (2*B); linarith
  have hB : x ≤ -2*B := by have := le_max_right (1 : ℝ) (2*B); linarith
  rw [phi_eq_negative hl hr (by linarith)]
  nlinarith [mul_nonneg (show 0 ≤ -x by linarith) (show 0 ≤ -x-1 by linarith)]

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

theorem phiFirst_hasDerivAt_pos {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : 0 < x) :
    HasDerivAt (phiFirst b) (positiveCurvature b x) x := by
  apply (positiveSlope_hasDerivAt_pos hl hr hx).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact phiFirst_eq_positive (show 0 ≤ y from hy.le)

theorem phiFirst_hasDerivAt_neg {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : x < 0) :
    HasDerivAt (phiFirst b) 1 x := by
  apply (hasDerivAt_id x).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact phiFirst_eq_negative hl hr (show y ≤ 0 from hy.le)

theorem phi_second_hasDerivAt_pos {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : 0 < x) :
    HasDerivAt (deriv (phi b)) (positiveCurvature b x) x := by
  rw [deriv_phi hl hr]
  exact phiFirst_hasDerivAt_pos hl hr hx

theorem phi_second_hasDerivAt_neg {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : x < 0) :
    HasDerivAt (deriv (phi b)) 1 x := by
  rw [deriv_phi hl hr]
  exact phiFirst_hasDerivAt_neg hl hr hx

theorem phi_second_derivative_bounds_of_ne_zero {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    (hx : x ≠ 0) :
    0 ≤ deriv (deriv (phi b)) x ∧ deriv (deriv (phi b)) x ≤ max 1 (768/b) := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · rw [(phi_second_hasDerivAt_neg hl hr hx).deriv]
    exact ⟨by norm_num, le_max_left _ _⟩
  · rw [(phi_second_hasDerivAt_pos hl hr hx).deriv]
    exact ⟨(positiveCurvature_bounds hl hr x).1,
      (positiveCurvature_bounds hl hr x).2.trans (le_max_right _ _)⟩

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

theorem derivative_ratio_on_nodes {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) :
    deriv (phi b) (b*scale n)/(b*scale n) = 1/b := by
  rw [(phi_node_hasDerivAt hl hr n).deriv]
  field_simp [(by linarith : b ≠ 0), (scale_pos n).ne']
  <;> ring

theorem derivative_ratio_on_shifted_nodes {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) :
    deriv (phi b) ((b+1/4)*scale n)/((b+1/4)*scale n) = 1/(b+1/4) := by
  have hh : |scale n/4| < scale n/2 := by have := scale_pos n; rw [abs_of_pos (by positivity)]; linarith
  have hd := (phi_plateau_hasDerivAt hl hr n hh).deriv
  have he : b*scale n+scale n/4 = (b+1/4)*scale n := by ring
  rw [he] at hd
  rw [hd]
  field_simp [(by linarith : b+1/4 ≠ 0), (scale_pos n).ne']
  <;> ring

theorem scaled_nodes_tendsto_punctured {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n => c*scale n) atTop (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall (fun n => ?_)⟩
  · simpa only [mul_zero] using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).mul scale_tendsto_zero)
  · simpa only [mem_compl_iff, mem_singleton_iff] using (mul_pos hc (scale_pos n)).ne'

theorem phi_not_twice_differentiable_zero {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    ¬ DifferentiableAt ℝ (deriv (phi b)) 0 := by
  intro hd
  have hz : deriv (phi b) 0 = 0 := by rw [deriv_phi hl hr, phiFirst_zero hl hr]
  have hleft := hd.hasDerivAt.tendsto_slope_zero.comp
    (scaled_nodes_tendsto_punctured (c := b) (by linarith))
  have hright := hd.hasDerivAt.tendsto_slope_zero.comp
    (scaled_nodes_tendsto_punctured (c := b+1/4) (by linarith))
  have hlconst : Tendsto (fun _ : ℕ => 1/b) atTop (𝓝 (deriv (deriv (phi b)) 0)) := by
    convert hleft using 1
    ext n
    simpa only [Function.comp_def, zero_add, hz, sub_zero, smul_eq_mul, ← div_eq_inv_mul] using
      (derivative_ratio_on_nodes hl hr n).symm
  have hrconst : Tendsto (fun _ : ℕ => 1/(b+1/4)) atTop (𝓝 (deriv (deriv (phi b)) 0)) := by
    convert hright using 1
    ext n
    simpa only [Function.comp_def, zero_add, hz, sub_zero, smul_eq_mul, ← div_eq_inv_mul] using
      (derivative_ratio_on_shifted_nodes hl hr n).symm
  have he : (1:ℝ)/b = 1/(b+1/4) :=
    (tendsto_nhds_unique tendsto_const_nhds hlconst).trans (tendsto_nhds_unique hrconst tendsto_const_nhds)
  have hb : b ≠ 0 := by linarith
  have hc : b+1/4 ≠ 0 := by linarith
  have hcross := (div_eq_div_iff hb hc).mp he
  linarith

theorem phi_second_derivative_bounds {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    {x a : ℝ} (hx : HasDerivAt (deriv (phi b)) a x) : 0 ≤ a ∧ a ≤ max 1 (768/b) := by
  have hn : x ≠ 0 := by
    intro he
    subst x
    exact phi_not_twice_differentiable_zero hl hr hx.differentiableAt
  rw [← hx.deriv]
  exact phi_second_derivative_bounds_of_ne_zero hl hr hn

end BfgsVerification.LScalar
