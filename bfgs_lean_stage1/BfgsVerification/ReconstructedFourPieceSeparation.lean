import BfgsVerification.ReconstructedFourPieceRun

noncomputable section
open scoped BigOperators Topology
open Matrix Set Filter
namespace BfgsVerification.ReconstructedFourPiece
open SeedOrbit SeedCycle RadialCertificate

/-- The literal supporting-plane condition fails along actual successive
accepted iterates, with one fixed positive band before the proposed constant. -/
theorem no_intercept_bounds :
    ¬ HasInterceptBounds objective {z | objective z ≤ objective (point 0)} optimizer := by
  intro h
  obtain ⟨C, hC⟩ := h valueScale valueScale_pos
  let R := run (c₁ := 1 / 4) (c₂ := 3 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hindex : Tendsto (fun m : ℕ => 3 * m + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  have ht : Tendsto (fun m : ℕ => C * secantCurvature
      (point (3 * m + 1)) (point (3 * m + 1 + 1))
      (gradient (3 * m + 1)) (gradient (3 * m + 1 + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (secant_tendsto_zero.comp hindex)
  have hsmall : ∀ᶠ m : ℕ in atTop, C * secantCurvature
      (point (3 * m + 1)) (point (3 * m + 1 + 1))
      (gradient (3 * m + 1)) (gradient (3 * m + 1 + 1)) < (25 / 4 : ℝ) ^ 2 :=
    ht.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨m, hm⟩ := hsmall.exists
  have hband : objective optimizer + valueScale ≤ objective (point (3 * m + 1 + 1)) := by
    rw [minimum_value]
    linarith [point_value_above_limit (3 * m + 1 + 1)]
  have hb := hC (point (3 * m + 1)) (point (3 * m + 1 + 1))
    (gradient (3 * m + 1)) (gradient (3 * m + 1 + 1))
    (R.objective_le_initial _) (R.objective_le_initial _) hband
    (R.objective_strict_decrease (3 * m + 1)).le
    (point_hasGradient _) (point_hasGradient _) (secant_pos _)
  have hi : optimizerIntercept objective optimizer (point (3 * m + 1)) (gradient (3 * m + 1)) = 0 := by
    simpa using point_phase_intercepts m 1
  have hj : optimizerIntercept objective optimizer (point (3 * m + 1 + 1)) (gradient (3 * m + 1 + 1)) = 25 / 4 := by
    simpa only [Nat.add_assoc] using point_phase_intercepts m 2
  rw [hi, hj, sub_zero] at hb
  exact (not_lt_of_ge hb) hm

theorem no_radial_bounds :
    ¬ HasRadialSecantBounds objective {z | objective z ≤ objective (point 0)} optimizer := by
  intro h
  exact no_intercept_bounds ((radial_iff_intercept_on_compact objective_convex
    (sublevels_compact _) optimizer).mp h)

end BfgsVerification.ReconstructedFourPiece
