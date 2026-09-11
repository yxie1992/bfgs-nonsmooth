import BfgsVerification.LScalarLocalCalculus

noncomputable section
open scoped Topology BigOperators
open Set Filter
namespace BfgsVerification.LScalar
open LScalarGeometric

theorem summable_curvatureComponent {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (x : ℝ) :
    Summable (fun n => curvatureComponent b n x) := by
  by_cases hx : x ≤ 0
  · simp only [curvatureComponent_nonpos hl hr hx]
    exact summable_zero
  obtain ⟨N,hN⟩ := exists_scale_below (b := b) (lt_of_not_ge hx)
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  exact curvatureComponent_zero_of_le hl hr (by simpa only [Finset.mem_range, not_lt] using hn) hN.le

theorem partialSlope_lipschitz {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (N : ℕ) :
    LipschitzWith ⟨768/b, by positivity⟩ (fun x => ∑ n ∈ Finset.range N, slopeComponent b n x) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (HasDerivAt.sum (fun n _ => slopeComponent_hasDerivAt (by linarith) n x)).differentiableAt
  · intro x
    rw [(HasDerivAt.sum (fun n _ => slopeComponent_hasDerivAt (by linarith : 0 < b) n x)).deriv]
    change ‖∑ n ∈ Finset.range N, curvatureComponent b n x‖ ≤ 768/b
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun n _ => (curvatureComponent_bounds (by linarith) n x).1))]
    exact ((summable_curvatureComponent hl hr x).sum_le_tsum _
      (fun n _ => (curvatureComponent_bounds (by linarith) n x).1)).trans
      (positiveCurvature_bounds hl hr x).2

theorem positiveSlope_lipschitz {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    LipschitzWith ⟨768/b, by positivity⟩ (positiveSlope b) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hx := (summable_slopeComponent b x).hasSum.tendsto_sum_nat
  have hy := (summable_slopeComponent b y).hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto' (hx.dist hy) tendsto_const_nhds
    (fun N => (partialSlope_lipschitz hl hr N).dist_le_mul x y)

end BfgsVerification.LScalar
