import BfgsVerification.ReconstructedFourPieceOrbit
import BfgsVerification.ObjectiveValueScaling

noncomputable section
open scoped BigOperators Topology
open Matrix Set Filter
namespace BfgsVerification.ReconstructedFourPiece
open SeedOrbit SeedCycle RadialCertificate AffineProjection

def transportedRun {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) :=
  ObjectiveValueScale.run valueScale (valueScale - 1) valueScale_pos
    (AffineWhitening.run coordinate coordinate_det_ne (coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂))

theorem transported_objective :
    ObjectiveValueScale.objective valueScale (valueScale - 1)
      (AffineWhitening.objective coordinate coerciveObjective) = objective := by
  funext z
  exact (objective_formula z).symm

/-- The actual infinite transformed full-BFGS run. Only the original source
line-search parameter range occurs; all matrix and derivative data are derived. -/
def run {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) : AdmissibleBFGSRun 2 objective where
  convex := objective_convex
  x := point
  H := (transportedRun hc₁ hc₁' hc hc₂).H
  g := gradient
  α := orbitLength
  c₁ := c₁
  c₂ := c₂
  c₁_pos := hc₁
  c₁_lt_c₂ := hc
  c₂_lt_one := hc₂
  initial_posDef := (transportedRun hc₁ hc₁' hc hc₂).initial_posDef
  alpha_pos := (transportedRun hc₁ hc₁' hc hc₂).alpha_pos
  gradient_nonzero := (transportedRun hc₁ hc₁' hc hc₂).gradient_nonzero
  hasGradient := point_hasGradient
  step := (transportedRun hc₁ hc₁' hc hc₂).step
  update := (transportedRun hc₁ hc₁' hc hc₂).update
  armijo k := by
    have h := (transportedRun hc₁ hc₁' hc hc₂).armijo k
    change valueScale * coerciveObjective (coordinate.mulVec (point (k + 1))) + (valueScale - 1) ≤
      valueScale * coerciveObjective (coordinate.mulVec (point k)) + (valueScale - 1) +
        c₁ * dot (gradient k) (bfgsStep ((transportedRun hc₁ hc₁' hc hc₂).H k) (gradient k) (orbitLength k)) at h
    rwa [← objective_formula, ← objective_formula] at h
  weak_wolfe := (transportedRun hc₁ hc₁' hc hc₂).weak_wolfe

@[simp] theorem run_x {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) (k : ℕ) : (run hc₁ hc₁' hc hc₂).x k = point k := rfl
@[simp] theorem run_g {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) (k : ℕ) : (run hc₁ hc₁' hc hc₂).g k = gradient k := rfl
@[simp] theorem run_H {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) (k : ℕ) :
    (run hc₁ hc₁' hc hc₂).H k = valueScale⁻¹ • AffineWhitening.metric coordinate (orbitMetric k) := rfl
@[simp] theorem run_alpha {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) (k : ℕ) : (run hc₁ hc₁' hc hc₂).α k = orbitLength k := rfl

theorem secant_pos (k : ℕ) :
    0 < secantCurvature (point k) (point (k + 1)) (gradient k) (gradient (k + 1)) := by
  let R := run (c₁ := 1 / 4) (c₂ := 3 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := (R.positive_invariants k).2.2
  change 0 < dot (R.g (k + 1) - R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) at h
  have hs : R.x (k + 1) - R.x k = bfgsStep (R.H k) (R.g k) (R.α k) := by rw [R.step]; abel
  change 0 < dot (R.g (k + 1) - R.g k) (R.x (k + 1) - R.x k)
  rwa [hs]

end BfgsVerification.ReconstructedFourPiece
