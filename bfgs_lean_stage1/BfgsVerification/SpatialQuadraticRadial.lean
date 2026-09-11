import BfgsVerification.SpatialQuadraticTransport
import BfgsVerification.QuadraticGaugeAlgebra
import BfgsVerification.RadialConvergence

/-! The alternative radial certificate for the same literal quadratic.
Failure of the canonical field is not a BFGS divergence assertion. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification
namespace SpatialQuadraticWarning
open RadialCertificate

theorem objective_zero : objective 0 = 0 := by simp [objective_coordinates]

theorem objective_nonnegative (x : Vec 3) : 0 ≤ objective x :=
  div_nonneg (QuadraticGauge.metricEnergy_nonneg Q_posDef.posSemidef x) (by norm_num)

theorem objective_unique_zero (x : Vec 3) (hx : objective x = 0) : x = 0 := by
  by_contra hn
  have hp := metricEnergy_pos Q_posDef hn
  change metricEnergy Q x / 2 = 0 at hx
  linarith

theorem sublevel_compact (b : ℝ) : IsCompact {x | objective x ≤ b} :=
  Localization.sublevel_compact objective_convex 0
    (fun x => by rw [objective_zero]; exact objective_nonnegative x)
    (fun x hx => objective_unique_zero x (by simpa only [objective_zero] using hx)) b

theorem radial_field_pairing (x : Vec 3) : dot (gradient x) x = 2*objective x := by
  rw [objective,gradient,metricEnergy]
  have h := dotProduct_comm (Q.mulVec x) x
  change dot (Q.mulVec x) x = dot x (Q.mulVec x) at h
  linarith

theorem radial_secant_inequality (x z : Vec 3) :
    (dot (gradient z-gradient x) z)^2 ≤
      (2*objective z)*dot (gradient z-gradient x) (z-x) := by
  have he : gradient z-gradient x = Q.mulVec (z-x) := by
    simp only [gradient,Matrix.mulVec_sub]
  have hc : dot (Q.mulVec (z-x)) (z-x) = metricEnergy Q (z-x) :=
    dotProduct_comm _ _
  rw [he,hc]
  have h := QuadraticGauge.metric_cauchy_schwarz Q_posDef.posSemidef (z-x) z
  convert h using 1
  unfold objective
  ring

theorem actual_radial_certificate (b : ℝ) :
    HasRadialSecantBounds objective {x | objective x ≤ b} 0 := by
  intro η hη
  refine ⟨2*b,?_⟩
  intro x z g h hx hz hband horder hg hh ht
  have hg' : g = gradient x := AffineProjection.gradientFunctional_injective
    (hg.unique (objective_hasGradient x))
  have hh' : h = gradient z := AffineProjection.gradientFunctional_injective
    (hh.unique (objective_hasGradient z))
  subst g h
  simp only [radialNumerator,sub_zero,secantCurvature] at ht ⊢
  have hzb : objective z ≤ b := hz
  exact (radial_secant_inequality x z).trans
    (mul_le_mul_of_nonneg_right (by linarith : 2*objective z ≤ 2*b) ht.le)

/-- Every admissible infinite full-BFGS run on this quadratic converges. No
boundedness, iterate limit, or matrix limit is assumed. -/
theorem actual_fullBFGS_convergence (R : AdmissibleBFGSRun 3 objective) :
    Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨hv,_,hx⟩ := R.radial_certificate_convergence_on_sublevel (objective (R.x 0))
    (sublevel_compact _) 0
    (fun x => by rw [objective_zero]; exact objective_nonnegative x) le_rfl
    (actual_radial_certificate _)
  refine ⟨by simpa only [objective_zero] using hv,hx ?_⟩
  intro x hx
  exact objective_unique_zero x (by simpa only [objective_zero] using hx)

end SpatialQuadraticWarning
end BfgsVerification
