import BfgsVerification.LScalarPeaks

noncomputable section
open scoped Topology
open Set Filter Asymptotics
namespace BfgsVerification.LScalar
open LScalarGeometric

theorem positiveSlope_nonnegative (b x : ℝ) : 0 ≤ positiveSlope b x :=
  tsum_nonneg (fun n => (slopeComponent_bounds b n x).1)

theorem positivePart_monotone {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) : Monotone (positivePart b) :=
  monotone_of_hasDerivAt_nonneg (positivePart_hasDerivAt hl hr) (positiveSlope_nonnegative b)

theorem positive_small_bounds {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    (hx : 0 < x) (hxb : x ≤ b) :
    0 ≤ phi b x ∧ phi b x ≤ (x/(b*theta))^2 ∧
    0 ≤ phiFirst b x ∧ phiFirst b x ≤ x/(b*theta) := by
  have hb : 0 < b := by linarith
  obtain ⟨n,hlo,hhi⟩ := positive_interval_cover hb hx hxb
  have ha : scale n ≤ x/(b*theta) := (le_div_iff₀ (mul_pos hb theta_pos)).mpr (by nlinarith)
  have hv : positivePart b x ≤ (scale n)^2 := by
    simpa only [positivePart_node hl hr n] using positivePart_monotone hl hr hhi
  have hs : positiveSlope b x ≤ scale n := by
    simpa only [positiveSlope_node hl hr n, pow_one] using positiveSlope_monotone hb hhi
  rw [phi_eq_positive hx.le, phiFirst_eq_positive hx.le]
  exact ⟨positivePart_nonnegative hl hr x, hv.trans (pow_le_pow_left₀ (scale_pos n).le ha 2),
    positiveSlope_nonnegative b x, hs.trans ha⟩

theorem positive_asymptotic_orders {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    phi b =O[𝓝[>] 0] (fun x : ℝ => x^2) ∧
    phiFirst b =O[𝓝[>] 0] (fun x : ℝ => x) := by
  have hb : 0 < b := by linarith
  have he : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x ∧ x ≤ b := by
    filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds hb).filter_mono nhdsWithin_le_nhds] with x hx hxb
    exact ⟨hx,hxb.le⟩
  refine ⟨Asymptotics.isBigO_iff.mpr ⟨1/(b*theta)^2, ?_⟩,
    Asymptotics.isBigO_iff.mpr ⟨1/(b*theta), ?_⟩⟩
  · filter_upwards [he] with x hx
    obtain ⟨h0,h1,_⟩ := positive_small_bounds hl hr hx.1 hx.2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (sq_nonneg _)]
    convert h1 using 1 <;> ring
  · filter_upwards [he] with x hx
    obtain ⟨_,_,h0,h1⟩ := positive_small_bounds hl hr hx.1 hx.2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_pos hx.1]
    convert h1 using 1 <;> ring

end BfgsVerification.LScalar
