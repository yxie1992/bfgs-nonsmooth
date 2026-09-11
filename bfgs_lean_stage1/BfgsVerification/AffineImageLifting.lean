import BfgsVerification.AffineFiberProjection

/-! End-to-end linear-image lifting and finite-prefix exports for F and H. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace AffineProjection

variable {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) (hA : FullRowRank A)
    (F : Vec r → ℝ) (R : AdmissibleBFGSRun n (fun x => F (A.mulVec x)))
include hA R

/-- Exact iterate identity for the genuine projected admissible run. -/
theorem projectRun_iterate_lift (k : ℕ) :
    R.x k = fiberPoint A (R.H 0) (R.x 0) ((projectRun A hA F R).x k) :=
  R.affine_iterate_lift A hA (projectedGradient A F R)
    (projected_gradient_lift A hA F R) k

/-- F:lifting. Convergence of the genuine projected run supplies the only
limit premise; the full iterate limit and metric-fiber characterization follow. -/
theorem projectRun_limit_lift (zstar : Vec r)
    (hz : Tendsto (projectRun A hA F R).x atTop (𝓝 zstar)) :
    Tendsto R.x atTop (𝓝 (fiberPoint A (R.H 0) (R.x 0) zstar)) ∧
    A.mulVec (fiberPoint A (R.H 0) (R.x 0) zstar) = zstar ∧
    ∀ x : Vec n, A.mulVec x = zstar →
      metricEnergy (R.H 0)⁻¹ (fiberPoint A (R.H 0) (R.x 0) zstar - R.x 0) ≤
        metricEnergy (R.H 0)⁻¹ (x - R.x 0) ∧
      (metricEnergy (R.H 0)⁻¹ (x - R.x 0) =
          metricEnergy (R.H 0)⁻¹ (fiberPoint A (R.H 0) (R.x 0) zstar - R.x 0) ↔
        x = fiberPoint A (R.H 0) (R.x 0) zstar) := by
  refine ⟨R.affine_limit_lift A hA (projectedGradient A F R)
    (projected_gradient_lift A hA F R) zstar hz,
    fiberPoint_in_fiber A hA R.initial_posDef (R.x 0) zstar, ?_⟩
  intro x hx
  exact ⟨fiberPoint_minimizes A hA R.initial_posDef (R.x 0) x zstar hx,
    fiberPoint_minimizer_unique A hA R.initial_posDef (R.x 0) x zstar hx⟩

/-- Any projected optimizer lifts to a genuine optimizer of the original objective. -/
theorem fiberPoint_objective_minimum (zstar : Vec r) (hmin : ∀ z, F zstar ≤ F z) :
    ∀ x : Vec n, F (A.mulVec (fiberPoint A (R.H 0) (R.x 0) zstar)) ≤ F (A.mulVec x) := by
  intro x
  rw [fiberPoint_in_fiber A hA R.initial_posDef]
  exact hmin _

omit R

/-- Unique reduced optimality identifies precisely the entire original solution fiber. -/
theorem objective_minimum_iff_fiber (zstar : Vec r) (hmin : ∀ z, F zstar ≤ F z)
    (huniq : ∀ z, F z = F zstar → z = zstar) (x : Vec n) :
    (∀ y : Vec n, F (A.mulVec x) ≤ F (A.mulVec y)) ↔ A.mulVec x = zstar := by
  constructor
  · intro hx
    have h := hx ((rightInverse A).mulVec zstar)
    rw [Matrix.mulVec_mulVec, mul_rightInverse A hA, Matrix.one_mulVec] at h
    exact huniq _ (le_antisymm h (hmin _))
  · intro hx y
    rw [hx]
    exact hmin _

end AffineProjection
namespace AdmissibleBFGSRun
open AffineProjection

/-- H.7.1 on an arbitrary tail, with its actual current SPD metric. -/
theorem affine_iterate_lift_tail {n r : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) (J : ℕ) (gbar : ℕ → Vec r)
    (hg : ∀ k, Aᵀ.mulVec (gbar k) = R.g (J + k)) (k : ℕ) :
    R.x (J + k) = R.x J + (lift A (R.H J)).mulVec
      (A.mulVec (R.x (J + k)) - A.mulVec (R.x J)) := by
  simpa only [shift, Nat.add_zero] using (R.shift J).affine_iterate_lift A hA gbar hg k

/-- A projected tail limit lifts to a limit of the full original sequence. -/
theorem affine_limit_lift_tail {n r : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : FullRowRank A) (J : ℕ) (gbar : ℕ → Vec r)
    (hg : ∀ k, Aᵀ.mulVec (gbar k) = R.g (J + k)) (zstar : Vec r)
    (hz : Tendsto (fun k => A.mulVec (R.x (J + k))) atTop (𝓝 zstar)) :
    Tendsto R.x atTop (𝓝 (R.x J + (lift A (R.H J)).mulVec (zstar - A.mulVec (R.x J)))) := by
  have h := (R.shift J).affine_limit_lift A hA gbar hg zstar hz
  have ht : Tendsto (fun k => R.x (k + J)) atTop
      (𝓝 (R.x J + (lift A (R.H J)).mulVec (zstar - A.mulVec (R.x J)))) := by
    simpa only [shift, Nat.add_zero, Nat.add_comm] using h
  exact (tendsto_add_atTop_iff_nat J).mp ht

end AdmissibleBFGSRun
end BfgsVerification
