import BfgsVerification.ParabolicEnvelopeBound

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification
namespace Parabolic
namespace Family
variable {m : ℕ} (P : Family m)

/-- The selector-free exponent is the finite calibrated ramp potential evaluated
at the actual normalized normal coordinate. It is used on positive levels. -/
def calibratedExponent (x : Vec 2) : ℝ := P.envelopePotential (x 1 / P.objective x)

/-- The exact source scale, defined without making any active-index choice. -/
def calibratedScale (x : Vec 2) : ℝ := Real.exp (P.calibratedExponent x)

theorem calibratedScale_pos (x : Vec 2) : 0 < P.calibratedScale x := Real.exp_pos _

theorem log_calibratedScale (x : Vec 2) : Real.log (P.calibratedScale x) = P.calibratedExponent x :=
  Real.log_exp _

theorem calibratedExponent_eq_active {i : Fin m} {x : Vec 2}
    (hi : P.Active i x) (hx : 0 < P.objective x) :
    P.calibratedExponent x = P.a i * (x 0)^2 / (2 * P.objective x) + P.calibration i := by
  obtain ⟨ht, hc⟩ := P.active_normalized_cell hi hx
  have he := P.calibration_matches_cell hc
  rw [ht] at he
  change P.envelopePotential (x 1 / P.objective x) = _
  exact he.trans (by ring)

theorem calibratedScale_eq_active {i : Fin m} {x : Vec 2}
    (hi : P.Active i x) (hx : 0 < P.objective x) :
    P.calibratedScale x = Real.exp (P.a i * (x 0)^2 / (2 * P.objective x) + P.calibration i) := by
  rw [calibratedScale, P.calibratedExponent_eq_active hi hx]

theorem envelopePotential_continuous : Continuous P.envelopePotential := by
  unfold envelopePotential Envelope.ramp
  fun_prop

/-- Continuity is asserted only on F>0. No extension or continuity at the
minimizer is assumed or concluded. -/
theorem calibratedExponent_continuousOn :
    ContinuousOn P.calibratedExponent {x | 0 < P.objective x} := by
  have hn : ContinuousOn (fun x : Vec 2 => x 1 / P.objective x) {x | 0 < P.objective x} :=
    (continuous_apply 1).continuousOn.div P.objective_continuous.continuousOn (fun _ hx => hx.ne')
  exact P.envelopePotential_continuous.comp_continuousOn hn

theorem calibratedScale_continuousOn :
    ContinuousOn P.calibratedScale {x | 0 < P.objective x} :=
  Real.continuous_exp.comp_continuousOn P.calibratedExponent_continuousOn

/-- Uniform positive lower and finite upper bounds hold on every positive
level, derived from compact normalized-coordinate bounds of the original family. -/
theorem calibratedScale_uniform_bounds :
    ∃ θmin θmax : ℝ, 0 < θmin ∧ 0 < θmax ∧
      ∀ x : Vec 2, 0 < P.objective x → θmin ≤ P.calibratedScale x ∧ P.calibratedScale x ≤ θmax := by
  obtain ⟨a, ha⟩ := (isCompact_Icc : IsCompact (Icc P.normalLeft P.normalRight)).bddBelow_image
    P.envelopePotential_continuous.continuousOn
  obtain ⟨b, hb⟩ := (isCompact_Icc : IsCompact (Icc P.normalLeft P.normalRight)).bddAbove_image
    P.envelopePotential_continuous.continuousOn
  refine ⟨Real.exp a, Real.exp b, Real.exp_pos _, Real.exp_pos _, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := P.exists_active x
  have hv := (P.active_normalized_cell hi hx).2.1
  have hlo := ha ⟨x 1 / P.objective x, hv, rfl⟩
  have hhi := hb ⟨x 1 / P.objective x, hv, rfl⟩
  exact ⟨Real.exp_le_exp.mpr hlo, Real.exp_le_exp.mpr hhi⟩

end Family
end Parabolic
end BfgsVerification
