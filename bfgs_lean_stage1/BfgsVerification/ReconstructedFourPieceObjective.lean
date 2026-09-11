import BfgsVerification.CoerciveSeedIntercept
import BfgsVerification.AffineWhiteningRun

/-! A new explicit reconstruction of R182–187 from the verified D objective.
The printed numerical assertions and failure interpretation are reconstructed
by actual coordinate and positive-value transformations. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Set Filter
namespace BfgsVerification.ReconstructedFourPiece
open SeedOrbit SeedCycle RadialCertificate AffineProjection

def gap : ℝ := -1 + seedC - 16 * seedD
def valueScale : ℝ := (25 / 4) / gap
def coordinate : Mat 2 := !![1, 0; 0, 16 / 5]
def optimizer : Vec 2 := ![-1, 5]

theorem gap_pos : 0 < gap := by
  simpa [gap, coerciveBranchIntercept] using coercive_third_intercept_positive

theorem valueScale_pos : 0 < valueScale := div_pos (by norm_num) gap_pos

theorem valueScale_mul_gap : valueScale * gap = 25 / 4 := by
  exact div_mul_cancel₀ _ gap_pos.ne'

theorem coordinate_det_ne : coordinate.det ≠ 0 := by
  norm_num [coordinate, Matrix.det_fin_two]

theorem coordinate_apply (z : Vec 2) : coordinate.mulVec z = ![z 0, (16 / 5) * z 1] := by
  ext i
  fin_cases i <;> simp [coordinate, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem coordinate_optimizer : coordinate.mulVec optimizer = coerciveOptimizer := by
  rw [coordinate_apply]
  norm_num [optimizer, coerciveOptimizer]

def family : MaxAffine.Family 2 4 where
  a i := valueScale • coordinateᵀ.mulVec (coerciveFamily.a i)
  b i := valueScale * coerciveFamily.b i + (valueScale - 1)
  nonempty := ⟨0⟩

def objective : Vec 2 → ℝ := family.objective

theorem branch_formula (i : Fin 4) (z : Vec 2) :
    family.branch i z = valueScale * coerciveFamily.branch i (coordinate.mulVec z) + (valueScale - 1) := by
  simp only [MaxAffine.Family.branch, family, PlanarUpdate.dot_scale_left,
    dot_transpose_mulVec]
  ring

theorem literal_branches (i : Fin 4) (z : Vec 2) :
    family.branch i z =
      (![valueScale * z 0 + valueScale - 1,
        valueScale * (-z 0 - (2 / 5) * z 1) + valueScale - 1,
        valueScale * (seedC * z 0 + (16 / 5) * seedD * z 1) + valueScale - 1,
        (16 / 5) * valueScale * z 1 - 16 * valueScale - 1] : Vec 4) i := by
  rw [branch_formula, coordinate_apply]
  fin_cases i <;>
    norm_num [coerciveFamily, MaxAffine.Family.branch, g0, g1, g2, dot,
      Fin.sum_univ_two, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem objective_formula (z : Vec 2) :
    objective z = valueScale * coerciveObjective (coordinate.mulVec z) + (valueScale - 1) := by
  apply le_antisymm
  · unfold objective MaxAffine.Family.objective
    apply Finset.sup'_le
    intro i _
    rw [branch_formula]
    exact add_le_add_right (mul_le_mul_of_nonneg_left (coerciveFamily.branch_le i _) valueScale_pos.le) _
  · obtain ⟨i, hi⟩ := coerciveFamily.exists_active (coordinate.mulVec z)
    have h := family.branch_le i z
    rw [branch_formula, hi] at h
    exact h

theorem objective_convex : ConvexOn ℝ univ objective := family.objective_convex

theorem minimum_value : objective optimizer = -1 := by
  rw [objective_formula, coordinate_optimizer, coercive_minimum_value]
  ring

theorem lower_bound (z : Vec 2) : -1 ≤ objective z := by
  rw [objective_formula]
  have h := mul_le_mul_of_nonneg_left (coercive_lower_bound (coordinate.mulVec z)) valueScale_pos.le
  nlinarith

theorem unique_optimizer {z : Vec 2} (hz : objective z = -1) : z = optimizer := by
  have he : coerciveObjective (coordinate.mulVec z) = -1 := by
    rw [objective_formula] at hz
    nlinarith [valueScale_pos]
  have h := coercive_unique_optimizer he
  rw [← coordinate_optimizer] at h
  have hh := congrArg coordinate⁻¹.mulVec h
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ coordinate_det_ne.isUnit,
    Matrix.one_mulVec] using hh

theorem sublevels_compact (a : ℝ) : IsCompact {z | objective z ≤ a} :=
  Localization.sublevel_compact objective_convex optimizer
    (fun z => by rw [minimum_value]; exact lower_bound z)
    (fun z hz => unique_optimizer (by simpa only [minimum_value] using hz)) a

theorem scaled_branch_intercepts (i : Fin 3) :
    valueScale * coerciveBranchIntercept i = (![0, 0, 25 / 4] : Vec 3) i := by
  fin_cases i
  · norm_num [coerciveBranchIntercept]
  · norm_num [coerciveBranchIntercept]
  · simpa only [coerciveBranchIntercept, Matrix.cons_val_two, Matrix.cons_val_zero,
      gap] using valueScale_mul_gap

theorem branches_at_optimizer (i : Fin 3) :
    family.branch i.castSucc optimizer = (![-1, -1, -29 / 4] : Vec 3) i := by
  rw [branch_formula, coordinate_optimizer, coercive_branch_old]
  have h := congrArg (fun r : ℝ => valueScale * r) (coercive_branch_intercepts i)
  change valueScale * (-1 - dot (SeedOrbit.gradient seedC seedD i) coerciveOptimizer) =
    valueScale * coerciveBranchIntercept i at h
  rw [scaled_branch_intercepts] at h
  have he : valueScale * dot (SeedOrbit.gradient seedC seedD i) coerciveOptimizer + (valueScale - 1) =
      -1 - (![0, 0, 25 / 4] : Vec 3) i := by nlinarith [h]
  rw [he]
  fin_cases i <;> norm_num

theorem zero_value : objective 0 = valueScale - 1 := by
  rw [objective_formula, Matrix.mulVec_zero, coercive_zero_value]
  ring

theorem limit_not_stationary :
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential objective 0 := by
  intro h
  have hh := h optimizer
  rw [minimum_value, zero_value] at hh
  norm_num [dot] at hh
  linarith [valueScale_pos]

end BfgsVerification.ReconstructedFourPiece
