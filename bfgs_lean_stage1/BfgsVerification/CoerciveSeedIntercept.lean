import BfgsVerification.AlgebraicSeedCoercive
import BfgsVerification.RadialEquivalence
import BfgsVerification.RadialConvergence
import BfgsVerification.InwardRadial

/-! Corrected supporting-plane interpretation for the current D four-piece objective. -/

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.SeedOrbit
open SeedCycle RadialCertificate

theorem historical_point_not_current_optimizer :
    (3/8 : ℝ) ≤ coerciveObjective ![-1,5] := by
  have h := (coercive_coordinate_bounds ![-1,5]).2.1
  norm_num at h
  exact h

theorem coercive_intercept_at_active {x : Vec 2} {i : Fin 3}
    (h : PointCertificate seedC seedD x i) :
    optimizerIntercept coerciveObjective coerciveOptimizer x (gradient seedC seedD i) =
      -1-dot (gradient seedC seedD i) coerciveOptimizer := by
  rw [optimizerIntercept, dot_sub_right, coercive_value_eq h, objective_of_active h.active,
    coercive_minimum_value]
  ring

def coerciveBranchIntercept : Fin 3 → ℝ := ![0,0,-1+seedC-16*seedD]

theorem coercive_branch_intercepts (i : Fin 3) :
    -1-dot (gradient seedC seedD i) coerciveOptimizer = coerciveBranchIntercept i := by
  fin_cases i <;>
    norm_num [coerciveBranchIntercept, coerciveOptimizer, gradient, g0, g1, g2, dot,
      Fin.sum_univ_two, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem coercive_third_intercept_positive : 0 < coerciveBranchIntercept 2 := by
  have h := source_downhill_pairings.2.2
  change dot (gradient seedC seedD 2) coerciveOptimizer < -1 at h
  rw [← coercive_branch_intercepts]
  linarith

theorem coercive_orbit_intercepts (k : ℕ) :
    optimizerIntercept coerciveObjective coerciveOptimizer (orbitPoint k) (orbitGradient k) =
      coerciveBranchIntercept (phase k) := by
  exact (coercive_intercept_at_active (coercive_orbit_certificate k)).trans (coercive_branch_intercepts _)

def coerciveSecantFactor (j : Fin 3) : ℝ :=
  dot (gradient seedC seedD (nextPhase j)-gradient seedC seedD j)
    (length j • direction seedC seedD seedRatio j)

theorem orbit_secant_factor (k : ℕ) :
    secantCurvature (orbitPoint k) (orbitPoint (k+1)) (orbitGradient k) (orbitGradient (k+1)) =
      orbitScale k*coerciveSecantFactor (phase k) := by
  rw [secantCurvature, orbit_step, add_sub_cancel_left]
  simp only [orbitGradient, orbitMetric, orbitLength, bfgsStep_scale_matrix,
    source_direction, dot_smul_right, orbit_next_phase, coerciveSecantFactor]

theorem orbit_secant_tendsto_zero :
    Tendsto (fun k => secantCurvature (orbitPoint k) (orbitPoint (k+1))
      (orbitGradient k) (orbitGradient (k+1))) atTop (𝓝 0) := by
  let C : ℝ := ∑ j : Fin 3, |coerciveSecantFactor j|
  have hb (j : Fin 3) : |coerciveSecantFactor j| ≤ C := by
    dsimp only [C]
    exact Finset.single_le_sum (f := fun i : Fin 3 => |coerciveSecantFactor i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hbound (k : ℕ) :
      ‖secantCurvature (orbitPoint k) (orbitPoint (k+1)) (orbitGradient k) (orbitGradient (k+1))‖ ≤
        orbitScale k*C := by
    rw [orbit_secant_factor, Real.norm_eq_abs, abs_mul, abs_of_pos (orbitScale_pos k)]
    exact mul_le_mul_of_nonneg_left (hb _) (orbitScale_pos k).le
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) hbound
  simpa only [zero_mul] using orbitScale_tendsto.mul_const C

theorem coercive_no_radial_bounds :
    ¬ HasRadialSecantBounds coerciveObjective
      {x | coerciveObjective x ≤ coerciveObjective (orbitPoint 0)} coerciveOptimizer := by
  intro hRS
  let R := coerciveRun (1/4) (3/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hv := R.radial_certificate_values
    {x | coerciveObjective x ≤ coerciveObjective (orbitPoint 0)}
    (coercive_sublevels_compact _) (fun k => R.objective_le_initial k)
    coerciveOptimizer (fun x => by rw [coercive_minimum_value]; exact coercive_lower_bound x) hRS
  rw [coercive_minimum_value] at hv
  change Tendsto (fun k => coerciveObjective (orbitPoint k)) atTop (𝓝 (-1)) at hv
  have he := tendsto_nhds_unique hv coercive_orbit_values_tendsto
  norm_num at he

theorem coercive_no_intercept_bounds :
    ¬ HasInterceptBounds coerciveObjective
      {x | coerciveObjective x ≤ coerciveObjective (orbitPoint 0)} coerciveOptimizer := by
  intro h
  apply coercive_no_radial_bounds
  exact (radial_iff_intercept_on_compact coerciveFamily.objective_convex
    (coercive_sublevels_compact _) coerciveOptimizer).mpr h

end BfgsVerification.SeedOrbit
