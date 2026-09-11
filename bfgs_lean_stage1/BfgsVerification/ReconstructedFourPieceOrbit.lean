import BfgsVerification.ReconstructedFourPieceObjective

noncomputable section
open scoped BigOperators Topology
open Matrix Set Filter
namespace BfgsVerification.ReconstructedFourPiece
open SeedOrbit SeedCycle RadialCertificate AffineProjection

def point (k : ℕ) : Vec 2 := AffineWhitening.point coordinate (orbitPoint k)
def gradient (k : ℕ) : Vec 2 := valueScale • AffineWhitening.gradient coordinate (orbitGradient k)

theorem map_point (k : ℕ) : coordinate.mulVec (point k) = orbitPoint k :=
  AffineWhitening.map_point coordinate coordinate_det_ne _

theorem point_optimizer : AffineWhitening.point coordinate coerciveOptimizer = optimizer := by
  rw [← coordinate_optimizer, AffineWhitening.point_map coordinate coordinate_det_ne]

theorem point_tendsto : Tendsto point atTop (𝓝 0) := by
  simpa only [point, AffineWhitening.point, matrixCLM_apply, Function.comp_def, Matrix.mulVec_zero] using
    (matrixCLM coordinate⁻¹).continuous.continuousAt.tendsto.comp orbitPoint_tendsto

theorem point_value (k : ℕ) :
    objective (point k) = valueScale * coerciveObjective (orbitPoint k) + (valueScale - 1) := by
  rw [objective_formula, map_point]

theorem point_values_tendsto :
    Tendsto (fun k => objective (point k)) atTop (𝓝 (valueScale - 1)) := by
  simp_rw [point_value]
  simpa only [mul_zero, zero_add] using
    (tendsto_const_nhds.mul coercive_orbit_values_tendsto).add_const (valueScale - 1)

theorem point_value_above_limit (k : ℕ) : valueScale - 1 < objective (point k) := by
  rw [point_value, coercive_orbit_value]
  have h := mul_pos valueScale_pos (orbit_value_pos k)
  linarith

theorem family_gradient (i : Fin 3) :
    family.a i.castSucc = valueScale • AffineWhitening.gradient coordinate (SeedOrbit.gradient seedC seedD i) := by
  change valueScale • coordinateᵀ.mulVec (coerciveFamily.a i.castSucc) = _
  have h : coerciveFamily.a i.castSucc = SeedOrbit.gradient seedC seedD i := by
    fin_cases i <;> norm_num [coerciveFamily, SeedOrbit.gradient, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  rw [h]
  rfl

theorem point_strict_active (k : ℕ) :
    ∀ j : Fin 4, j ≠ (phase k).castSucc → family.branch j (point k) < family.branch (phase k).castSucc (point k) := by
  intro j hj
  simp only [branch_formula, map_point]
  exact add_lt_add_right (mul_lt_mul_of_pos_left
    (coercive_strict_active (coercive_orbit_certificate k) j hj) valueScale_pos) _

theorem point_hasGradient (k : ℕ) : HasFDerivAt objective (gradientFunctional (gradient k)) (point k) := by
  have h := family.strict_active_hasGradient (point_strict_active k)
  rw [family_gradient] at h
  exact h

theorem point_intercepts (k : ℕ) :
    optimizerIntercept objective optimizer (point k) (gradient k) =
      (![0, 0, 25 / 4] : Vec 3) (phase k) := by
  have he : point k - optimizer = AffineWhitening.point coordinate (orbitPoint k - coerciveOptimizer) := by
    rw [← point_optimizer]
    exact (Matrix.mulVec_sub coordinate⁻¹ (orbitPoint k) coerciveOptimizer).symm
  have hscale : optimizerIntercept objective optimizer (point k) (gradient k) =
      valueScale * optimizerIntercept coerciveObjective coerciveOptimizer (orbitPoint k) (orbitGradient k) := by
    rw [optimizerIntercept, he, gradient, PlanarUpdate.dot_scale_left,
      AffineWhitening.dot_gradient_point coordinate coordinate_det_ne,
      point_value, minimum_value, optimizerIntercept, coercive_minimum_value]
    ring
  rw [hscale, coercive_orbit_intercepts, scaled_branch_intercepts]

theorem point_phase_intercepts (m : ℕ) (j : Fin 3) :
    optimizerIntercept objective optimizer (point (3 * m + j.val)) (gradient (3 * m + j.val)) =
      (![0, 0, 25 / 4] : Vec 3) j := by
  rw [point_intercepts]
  have hp : phase (3 * m + j.val) = j := by
    apply Fin.ext
    change (3 * m + j.val) % 3 = j.val
    omega
  rw [hp]

theorem secant_scale (k : ℕ) :
    secantCurvature (point k) (point (k + 1)) (gradient k) (gradient (k + 1)) =
      valueScale * secantCurvature (orbitPoint k) (orbitPoint (k + 1)) (orbitGradient k) (orbitGradient (k + 1)) := by
  simp only [secantCurvature, gradient, point, ← smul_sub, AffineWhitening.gradient,
    ← Matrix.mulVec_sub, AffineWhitening.point, PlanarUpdate.dot_scale_left]
  exact congrArg (valueScale * ·) (AffineWhitening.dot_gradient_point coordinate coordinate_det_ne _ _)

theorem secant_tendsto_zero :
    Tendsto (fun k => secantCurvature (point k) (point (k + 1)) (gradient k) (gradient (k + 1)))
      atTop (𝓝 0) := by
  simp_rw [secant_scale]
  simpa only [mul_zero] using tendsto_const_nhds.mul orbit_secant_tendsto_zero

end BfgsVerification.ReconstructedFourPiece
