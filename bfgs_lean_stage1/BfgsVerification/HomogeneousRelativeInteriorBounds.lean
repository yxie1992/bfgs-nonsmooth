import BfgsVerification.HomogeneousRelativeInteriorGeometry
import BfgsVerification.ObjectiveRates

/-! H.8 derives an actual orthonormal coordinate representation and coercivity
on the slope span. These are geometric conclusions, not additional run bounds. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace Homogeneous

/-- Every actual finite slope span has orthonormal coordinates. No nonzero rank
assumption is imposed; the zero-dimensional representation is included. -/
theorem exists_slope_span_coordinates {n : ℕ} (A : Finset (Vec n)) :
    ∃ (r : ℕ) (U : Matrix (Fin n) (Fin r) ℝ), Uᵀ * U = 1 ∧
      ∀ x, x ∈ Submodule.span ℝ (A : Set (Vec n)) ↔ ∃ z, U.mulVec z = x := by
  let S := Submodule.span ℝ (A : Set (Vec n))
  let e := (WithLp.linearEquiv 2 ℝ (Vec n)).symm
  let SE := S.map e.toLinearMap
  obtain ⟨U, hU, hspan⟩ := FrameNorms.orthonormal_matrix_for_subspace SE
  refine ⟨Module.finrank ℝ SE, U, hU, ?_⟩
  intro x
  have hm : euclideanVector x ∈ SE ↔ x ∈ S := by
    constructor
    · rintro ⟨y, hy, he⟩
      have hxy : y = x := e.injective he
      simpa only [hxy] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  exact hm.symm.trans (hspan (euclideanVector x))

/-- Strict positivity of a finite convex homogeneous function derives its
Euclidean coercivity constant from a compact unit sublevel. -/
theorem positive_homogeneous_euclidean_lower_bound {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (hh : PositiveDegreeOne F)
    (hp : ∀ x, x ≠ 0 → 0 < F x) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x, μ * ‖euclideanVector x‖ ≤ F x := by
  have hmin : ∀ x, F 0 ≤ F x := by
    intro x
    by_cases hx : x = 0
    · subst x; exact le_rfl
    · rw [value_zero hh]; exact (hp x hx).le
  have huniq : ∀ x, F x = F 0 → x = 0 := by
    intro x he
    by_contra hx
    have hpos := hp x hx
    rw [he, value_zero hh] at hpos
    exact lt_irrefl 0 hpos
  have hK := Localization.sublevel_compact hF 0 hmin huniq 1
  obtain ⟨M, hM, hbound⟩ := compact_sqNorm_radius hK 0
  refine ⟨M⁻¹, inv_pos.mpr hM, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simp [euclideanVector, value_zero hh]
  have hpos := hp x hx
  let y := (F x)⁻¹ • x
  have hy : F y ≤ 1 := by
    dsimp [y]
    rw [hh _ (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hpos.ne']
  have hn : ‖euclideanVector y‖ ^ 2 = sqNorm y := FrameNorms.euclidean_norm_sq (euclideanVector y)
  have hym : ‖euclideanVector y‖ ≤ M := by
    have hb := hbound y hy
    rw [sub_zero] at hb
    nlinarith [norm_nonneg (euclideanVector y)]
  have hxy : x = F x • y := by
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  have hxm : ‖euclideanVector x‖ ≤ M * F x := by
    conv_lhs => rw [hxy]
    change ‖F x • euclideanVector y‖ ≤ M * F x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hxm (inv_nonneg.mpr hM.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hM.ne', one_mul] using hm

theorem finiteMaxLinear_comp_homogeneous {n r : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (U : Matrix (Fin n) (Fin r) ℝ) :
    PositiveDegreeOne (fun z => finiteMaxLinear A hA (U.mulVec z)) := by
  intro c hc z
  change finiteMaxLinear A hA (U.mulVec (c • z)) = c * finiteMaxLinear A hA (U.mulVec z)
  rw [Matrix.mulVec_smul, finiteMaxLinear_homogeneous A hA c hc]

theorem relativeInterior_projected_positive {n r : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (hri : RelativeInteriorZero A) (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hspan : ∀ x, x ∈ Submodule.span ℝ (A : Set (Vec n)) ↔ ∃ z, U.mulVec z = x)
    (z : Vec r) (hz : z ≠ 0) : 0 < finiteMaxLinear A hA (U.mulVec z) := by
  have hUz : U.mulVec z ≠ 0 := by
    intro hu
    apply hz
    apply orthonormal_transpose_fullRowRank U hU
    simpa only [Matrix.transpose_transpose, Matrix.mulVec_zero] using hu
  exact relativeInteriorZero_positive_on_span A hA hri (U.mulVec z)
    ((hspan _).mpr ⟨z, rfl⟩) hUz

/-- The source's actual uniform lower bound F(x)≥μ‖Uᵀx‖₂ is derived from
relative interior in the full slope span. -/
theorem relativeInterior_euclidean_projection_bound {n r : ℕ}
    (A : Finset (Vec n)) (hA : A.Nonempty) (hri : RelativeInteriorZero A)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hspan : ∀ x, x ∈ Submodule.span ℝ (A : Set (Vec n)) ↔ ∃ z, U.mulVec z = x) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x, μ * ‖euclideanVector (Uᵀ.mulVec x)‖ ≤ finiteMaxLinear A hA x := by
  obtain ⟨μ, hμ, hb⟩ := positive_homogeneous_euclidean_lower_bound
    (finiteMaxLinear_comp_convex A hA U) (finiteMaxLinear_comp_homogeneous A hA U)
    (relativeInterior_projected_positive A hA hri U hU hspan)
  have hAsub (a : Vec n) (ha : a ∈ A) : ∃ z, U.mulVec z = a :=
    (hspan a).mp (Submodule.subset_span ha)
  exact ⟨μ, hμ, fun x => by simpa only [finiteMaxLinear_projection_eq A hA U hU hAsub] using hb (Uᵀ.mulVec x)⟩

/-- The actual zero sublevel equals precisely the orthogonal complement fiber
for the full-slope relative-interior case. -/
theorem relativeInterior_value_zero_iff_projection_zero {n r : ℕ}
    (A : Finset (Vec n)) (hA : A.Nonempty) (hri : RelativeInteriorZero A)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hspan : ∀ x, x ∈ Submodule.span ℝ (A : Set (Vec n)) ↔ ∃ z, U.mulVec z = x) (x : Vec n) :
    finiteMaxLinear A hA x = 0 ↔ Uᵀ.mulVec x = 0 := by
  have hAsub (a : Vec n) (ha : a ∈ A) : ∃ z, U.mulVec z = a :=
    (hspan a).mp (Submodule.subset_span ha)
  constructor
  · intro hx
    by_contra hp
    have h := relativeInterior_projected_positive A hA hri U hU hspan (Uᵀ.mulVec x) hp
    rw [finiteMaxLinear_projection_eq A hA U hU hAsub, hx] at h
    exact lt_irrefl 0 h
  · intro hx
    rw [← finiteMaxLinear_projection_eq A hA U hU hAsub x, hx, Matrix.mulVec_zero,
      value_zero (finiteMaxLinear_homogeneous A hA)]

end Homogeneous
end BfgsVerification
