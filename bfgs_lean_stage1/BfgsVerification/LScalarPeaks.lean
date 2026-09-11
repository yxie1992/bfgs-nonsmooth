import BfgsVerification.LScalarRegularity

noncomputable section
open scoped Topology BigOperators
open Set Filter
namespace BfgsVerification.LScalar
open LScalarGeometric

def peak (b : ℝ) (n : ℕ) : ℝ := b*scale n*(theta+(1-theta)*LScalarRamp.center b)

theorem peak_interval {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) :
    b*theta*scale n < peak b n ∧ peak b n < b*scale n := by
  have hb : 0 < b := by linarith
  have ha := scale_pos n
  have hc := LScalarRamp.center_bounds hl hr
  have hc0 : 0 < LScalarRamp.center b := by have := hc.1; norm_num [LScalarRamp.epsilon] at this; linarith
  have hc1 : LScalarRamp.center b < 1 := by have := hc.2; norm_num [LScalarRamp.epsilon] at this; linarith
  have h0 : theta < theta+(1-theta)*LScalarRamp.center b := by
    have := mul_pos (sub_pos.mpr theta_lt_one) hc0
    linarith
  have h1 : theta+(1-theta)*LScalarRamp.center b < 1 := by
    nlinarith [mul_pos (sub_pos.mpr theta_lt_one) (sub_pos.mpr hc1)]
  have hp0 := mul_lt_mul_of_pos_left h0 (mul_pos hb ha)
  have hp1 := mul_lt_mul_of_pos_left h1 (mul_pos hb ha)
  dsimp [peak]
  constructor <;> nlinarith

theorem peak_positive {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) : 0 < peak b n :=
  (mul_pos (mul_pos (by linarith : 0 < b) theta_pos) (scale_pos n)).trans (peak_interval hl hr n).1

theorem peak_coordinate {b : ℝ} (hb : 0 < b) (n : ℕ) :
    coordinate b (scale n) (peak b n) = LScalarRamp.center b := by
  unfold coordinate peak
  rw [mul_div_cancel_left₀ _ (mul_ne_zero hb.ne' (scale_pos n).ne')]
  field_simp [(sub_pos.mpr theta_lt_one).ne']

theorem rampDerivative_center (b : ℝ) : LScalarRamp.rampDerivative b (LScalarRamp.center b) = 768 := by
  norm_num [LScalarRamp.rampDerivative, LScalarRamp.rampCoordinate, LScalarRamp.epsilon,
    DScalarRamp.unitDerivative, DScalarRamp.join, DScalarRamp.cubicDerivative]

theorem positiveCurvature_peak {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) :
    positiveCurvature b (peak b n) = 768/b := by
  obtain ⟨h0,h1⟩ := peak_interval hl hr n
  rw [positiveCurvature_interval hl hr n h0.le h1.le, curvatureComponent,
    peak_coordinate (by linarith), rampDerivative_center]
  ring

theorem phi_peak_second_hasDerivAt {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) :
    HasDerivAt (deriv (phi b)) (768/b) (peak b n) := by
  rw [← positiveCurvature_peak hl hr n]
  exact phi_second_hasDerivAt_pos hl hr (peak_positive hl hr n)

theorem phi_node_second_hasDerivAt {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) :
    HasDerivAt (deriv (phi b)) 0 (b*scale n) := by
  rw [← positiveCurvature_node hl hr n]
  exact phi_second_hasDerivAt_pos hl hr (mul_pos (by linarith) (scale_pos n))

theorem peak_tendsto_zero (b : ℝ) : Tendsto (peak b) atTop (𝓝 0) := by
  simpa only [peak, mul_zero, zero_mul] using
    (((tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b)).mul scale_tendsto_zero).mul
      (tendsto_const_nhds (x := theta+(1-theta)*LScalarRamp.center b)))

theorem peak_curvature_nonvanishing {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    0 < 768/b ∧ (∀ n, deriv (deriv (phi b)) (peak b n) = 768/b) ∧
      ¬ Tendsto (fun n => deriv (deriv (phi b)) (peak b n)) atTop (𝓝 0) := by
  have hp : 0 < 768/b := by positivity
  refine ⟨hp, fun n => (phi_peak_second_hasDerivAt hl hr n).deriv, ?_⟩
  intro hzero
  have hc : Tendsto (fun n => deriv (deriv (phi b)) (peak b n)) atTop (𝓝 (768/b)) := by
    simpa only [funext (fun n => (phi_peak_second_hasDerivAt hl hr n).deriv)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => 768/b) atTop (𝓝 (768/b)))
  exact hp.ne' (tendsto_nhds_unique hc hzero)

end BfgsVerification.LScalar
