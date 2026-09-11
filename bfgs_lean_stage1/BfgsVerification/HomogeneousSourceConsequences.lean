import BfgsVerification.HomogeneousLowRankConvergence
import BfgsVerification.HomogeneousClassCorollaries
import BfgsVerification.HomogeneousPotentialConsequences
import BfgsVerification.HomogeneousSubspaceProjection

/-! Remaining explicit deductions in H.2, H.5.1 and H.7.3, including degenerate
rank bookkeeping. External historical/example provenance is not asserted here. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace Homogeneous

/-- A nonzero supporting vector supplies its own unit direction attaining a
value at least its norm. Together with compactness of the sphere this is the
source's exact bound by the maximum of F on that sphere. -/
theorem supporting_unit_direction {n : ℕ} {F : Vec n → ℝ}
    (hh : PositiveDegreeOne F) (x g : Vec n) (hs : Supports F x g) (hg : g ≠ 0) :
    let z := ‖euclideanVector g‖⁻¹ • g
    ‖euclideanVector z‖ = 1 ∧ ‖euclideanVector g‖ ≤ F z := by
  let r := ‖euclideanVector g‖
  have hr : 0 < r := norm_pos_iff.mpr (fun h => hg (by exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => (fun i => v i)) h))
  have hgg : dot g g = r^2 := by
    have h := FrameNorms.euclidean_norm_sq (euclideanVector g)
    simpa only [dot, sqNorm, pow_two] using h.symm
  have he : dot g (r⁻¹ • g) = r := by
    change g ⬝ᵥ (r⁻¹ • g) = r
    rw [dotProduct_smul]
    change r⁻¹ * dot g g = r
    rw [hgg]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · change ‖r⁻¹ • euclideanVector g‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  · simpa only [he] using supporting_linear_le hh hs (r⁻¹ • g)

/-- An actual opposite slope pair makes the whole finite maximum nonnegative,
including the degenerate zero-slope pair. -/
theorem finiteMax_opposite_slopes_nonneg {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (a b : Vec n) (ha : a ∈ A) (hb : b ∈ A) (κ : ℝ) (hκ : 0 < κ) (he : b = -κ • a)
    (x : Vec n) : 0 ≤ finiteMaxLinear A hA x := by
  have h1 := slope_le_finiteMaxLinear A hA ha x
  have h2 := slope_le_finiteMaxLinear A hA hb x
  rw [he, HomogeneousBlock.dot_smul_first] at h2
  have hm := mul_le_mul_of_nonneg_left h1 hκ.le
  nlinarith

/-- Source H.7.3's globally unbounded-below objective cannot contain an
opposite pair anywhere in its slope alphabet. -/
theorem unbounded_finiteMax_no_opposite_slopes {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (hu : ¬BddBelow (Set.range (finiteMaxLinear A hA)))
    (a b : Vec n) (ha : a ∈ A) (hb : b ∈ A) (κ : ℝ) (hκ : 0 < κ) : b ≠ -κ • a := by
  intro he
  apply hu
  exact ⟨0, by rintro z ⟨x, rfl⟩; exact finiteMax_opposite_slopes_nonneg A hA a b ha hb κ hκ he x⟩

end Homogeneous
namespace AdmissibleBFGSRun
open Homogeneous

/-- The source h,ell curvature decomposition is an exact identity. -/
theorem homogeneous_curvature_pairings {n : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.curvature k = dot (R.gradientChange k) (R.x (k+1)) + (-dot (R.gradientChange k) (R.x k)) := by
  have hx : R.displacement k = R.x (k+1)-R.x k := by rw [R.step]; simp [displacement]
  unfold curvature
  rw [hx]
  exact dotProduct_sub _ _ _

/-- Both source decrease inequalities use the actual accepted objective. -/
theorem homogeneous_decrease_sandwich {n : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.c₁*R.d k ≤ F (R.x k)-F (R.x (k+1)) ∧ F (R.x k)-F (R.x (k+1)) ≤ R.d k :=
  ⟨R.armijo_decrease k, R.convexity_decrease_upper k⟩

/-- The actual recurrent gradient span of a nonstationary finite-max run has
positive rank; a zero-dimensional projected infinite run never arises. -/
theorem maxLinear_recurrent_span_pos {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun n (finiteMaxLinear A hA)) :
    0 < Module.finrank ℝ (Submodule.span ℝ (recurrentValues R.g)) := by
  obtain ⟨g, hg⟩ := recurrentValues_nonempty R.g (R.maxLinear_gradient_range_finite A hA)
  obtain ⟨k, hk⟩ := recurrentValues_subset_range R.g hg
  have hg0 : g ≠ 0 := by rw [← hk]; exact R.gradient_nonzero k
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨g, Submodule.subset_span hg⟩, ?_⟩
  intro h
  exact hg0 (congrArg (fun v : Submodule.span ℝ (recurrentValues R.g) => (v : Vec n)) h)

end AdmissibleBFGSRun
end BfgsVerification
