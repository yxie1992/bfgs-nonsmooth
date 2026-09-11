import BfgsVerification.LScalarCurvature
import BfgsVerification.LScalarIntervals

noncomputable section
set_option maxHeartbeats 1600000
open scoped Topology BigOperators
open Set Filter
namespace BfgsVerification.LScalar
open LScalarGeometric

theorem scale_tendsto_zero : Tendsto scale atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one theta_pos.le theta_lt_one

theorem exists_scale_below {b x : ℝ} (hx : 0 < x) : ∃ N, b*scale N < x := by
  have h : Tendsto (fun N => b*scale N) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul scale_tendsto_zero
  exact (h.eventually (gt_mem_nhds hx)).exists

theorem curvatureComponent_zero_of_le {b y : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    {N n : ℕ} (hN : N ≤ n) (hy : b*scale N ≤ y) : curvatureComponent b n y = 0 := by
  apply curvatureComponent_outer_zero hl hr
  exact (mul_le_mul_of_nonneg_left (scale_antitone hN) (by linarith)).trans hy

theorem slopeComponent_constant_of_le {b y : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    {N n : ℕ} (hN : N ≤ n) (hy : b*scale N ≤ y) :
    slopeComponent b n y = (scale n)^1*(1-theta^1) := by
  have hc := (coordinate_ge_one_iff (by linarith : 0 < b) (scale_pos n)).mpr
    ((mul_le_mul_of_nonneg_left (scale_antitone hN) (by linarith)).trans hy)
  simp only [slopeComponent,
    LScalarRamp.ramp_eq_one ((LScalarRamp.transition_inside hl hr).2.2.le.trans hc), mul_one]

theorem positiveSlope_finite_tail {b y : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    (N : ℕ) (hy : b*scale N ≤ y) :
    positiveSlope b y = (∑ n ∈ Finset.range N, slopeComponent b n y)+scale N := by
  have he := (summable_slopeComponent b y).sum_add_tsum_nat_add N
  have ht : (∑' n : ℕ, slopeComponent b (n+N) y) = scale N := by
    simp_rw [slopeComponent_constant_of_le hl hr (show N ≤ _+N from Nat.le_add_left _ _) hy]
    rw [tsum_mul_right, tsum_tail_power (by omega : 0 < 1)]
    norm_num [theta]
  rw [ht] at he
  exact he.symm

theorem positiveCurvature_finite {b y : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    (N : ℕ) (hy : b*scale N ≤ y) :
    positiveCurvature b y = ∑ n ∈ Finset.range N, curvatureComponent b n y := by
  apply tsum_eq_sum
  intro n hn
  exact curvatureComponent_zero_of_le hl hr (by simpa only [Finset.mem_range, not_lt] using hn) hy

theorem positiveSlope_hasDerivAt_pos {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    (hx : 0 < x) : HasDerivAt (positiveSlope b) (positiveCurvature b x) x := by
  obtain ⟨N,hN⟩ := exists_scale_below (b := b) hx
  rw [positiveCurvature_finite hl hr N hN.le]
  apply ((HasDerivAt.sum (fun n _ => slopeComponent_hasDerivAt (by linarith) n x)).add_const
    (scale N)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hN] with y hy
  exact positiveSlope_finite_tail hl hr N (show b*scale N ≤ y from hy.le)

theorem positiveCurvature_continuousAt_pos {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    (hx : 0 < x) : ContinuousAt (positiveCurvature b) x := by
  obtain ⟨N,hN⟩ := exists_scale_below (b := b) hx
  have hc : Continuous (fun y => ∑ n ∈ Finset.range N, curvatureComponent b n y) := by
    apply continuous_finset_sum
    intro n hn
    change Continuous (fun y => 1/b * (512 * DScalarRamp.unitDerivative
      (LScalarRamp.rampCoordinate b (coordinate b (scale n) y))))
    apply continuous_const.mul
    exact continuous_const.mul (DScalarRamp.unitDerivative_continuous.comp (by
      unfold LScalarRamp.rampCoordinate coordinate
      fun_prop))
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hN] with y hy
  exact positiveCurvature_finite hl hr N (show b*scale N ≤ y from hy.le)

theorem positivePart_finite_tail {b y : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    (N : ℕ) (hy : b*scale N ≤ y) :
    positivePart b y = (∑ n ∈ Finset.range N, component b n y)+
      scale N*y+(1-b)*(scale N)^2 := by
  have he := (summable_component hl hr y).sum_add_tsum_nat_add N
  have hs1 : Summable (fun n => (scale (n+N))^1) :=
    (summable_nat_add_iff N).mpr (summable_scale_power (by omega : 0 < 1))
  have hs2 : Summable (fun n => (scale (n+N))^2) :=
    (summable_nat_add_iff N).mpr (summable_scale_power (by omega : 0 < 2))
  have ht : (∑' n, component b (n+N) y) = scale N*y+(1-b)*(scale N)^2 := by
    have hc (n : ℕ) := component_affine hl hr (n+N)
      ((mul_le_mul_of_nonneg_left (scale_antitone (Nat.le_add_left N n)) (by linarith)).trans hy)
    simp_rw [hc]
    rw [Summable.tsum_add ((hs1.mul_left _).mul_right _) (hs2.mul_left _),
      tsum_mul_right, tsum_mul_left, tsum_mul_left,
      tsum_tail_power (by omega : 0 < 1), tsum_tail_power (by omega : 0 < 2)]
    norm_num [theta] <;> ring
  rw [ht] at he
  change _ = positivePart b y at he
  rw [← he]
  ring

theorem component_contDiff (b : ℝ) (n : ℕ) : ContDiff ℝ 2 (component b n) := by
  apply contDiff_const.mul
  exact (LScalarRamp.primitive_contDiff b).comp (by unfold coordinate; simp only [div_eq_mul_inv]; fun_prop)

theorem positivePart_contDiffAt_pos {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    (hx : 0 < x) : ContDiffAt ℝ 2 (positivePart b) x := by
  obtain ⟨N,hN⟩ := exists_scale_below (b := b) hx
  have hc : ContDiff ℝ 2 (fun y => (∑ n ∈ Finset.range N, component b n y)+
      scale N*y+(1-b)*(scale N)^2) := by
    apply ContDiff.add
    · apply ContDiff.add
      · exact ContDiff.sum (fun n _ => component_contDiff b n)
      · fun_prop
    · fun_prop
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hN] with y hy
  exact positivePart_finite_tail hl hr N (show b*scale N ≤ y from hy.le)

end BfgsVerification.LScalar
