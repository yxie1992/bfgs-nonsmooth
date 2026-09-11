import BfgsVerification.HomogeneousLowRankProjection
import BfgsVerification.HomogeneousRelativeInteriorConvergence
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

/-! H.8's scope includes exactly the nonnegative finite maxima whose zero
fiber is a linear subspace, in particular actual finite polyhedral seminorms. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace
open Matrix Filter Set

namespace BfgsVerification
namespace Homogeneous

/-- Strict positivity of a finite maximum derives a genuine Euclidean ball
inside its slope polytope by continuous linear separation. -/
theorem positive_finiteMax_convexHull_ball {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (hp : ∀ x : Vec n, x ≠ 0 → 0 < finiteMaxLinear A hA x) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ p : Vec n, ‖euclideanVector p‖ < μ → p ∈ convexHull ℝ (A : Set (Vec n)) := by
  obtain ⟨μ, hμ, hbound⟩ := positive_homogeneous_euclidean_lower_bound
    (finiteMaxLinear_convex A hA) (finiteMaxLinear_homogeneous A hA) hp
  refine ⟨μ, hμ, ?_⟩
  intro p hpμ
  by_contra hnp
  obtain ⟨f, u, hf, hu⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (A : Set (Vec n))) A.finite_toSet.isClosed_convexHull hnp
  let g : Vec n := fun i => f (Pi.single i 1)
  have hfg (x : Vec n) : f x = dot g x := linearFunctional_eq_dot f.toLinearMap x
  obtain ⟨a, ha, hga⟩ := finiteMaxLinear_active A hA g
  have hlt : finiteMaxLinear A hA g < dot g p := by
    have h := (hf a (subset_convexHull ℝ (A : Set (Vec n)) ha)).trans hu
    rw [hfg a, hfg p, show dot g a = dot a g from dotProduct_comm _ _] at h
    exact hga.trans_lt h
  have hg : g ≠ 0 := by
    intro hz
    rw [hz, value_zero (finiteMaxLinear_homogeneous A hA)] at hlt
    simp [dot] at hlt
  have hgn : 0 < ‖euclideanVector g‖ := norm_pos_iff.mpr (fun h => hg (by exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => (fun i => v i)) h))
  have hdot : dot g p ≤ ‖euclideanVector g‖ * ‖euclideanVector p‖ := by
    have hi := real_inner_le_norm (euclideanVector g) (euclideanVector p)
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hi
    change dot p g ≤ _ at hi
    rw [show dot p g = dot g p from dotProduct_comm _ _] at hi
    exact hi
  have hmul := mul_lt_mul_of_pos_left hpμ hgn
  have hb := hbound g
  nlinarith

/-- Strict positivity on the actual full slope span is equivalent to the
source relative-interior condition; here is the geometric reverse implication. -/
theorem relativeInteriorZero_of_positive_on_span {n : ℕ}
    (A : Finset (Vec n)) (hA : A.Nonempty)
    (hp : ∀ x, x ∈ Submodule.span ℝ (A : Set (Vec n)) → x ≠ 0 → 0 < finiteMaxLinear A hA x) :
    RelativeInteriorZero A := by
  obtain ⟨r, U, hU, hspan⟩ := exists_slope_span_coordinates A
  have hAsub (a : Vec n) (ha : a ∈ A) : ∃ z, U.mulVec z = a :=
    (hspan a).mp (Submodule.subset_span ha)
  let B := projectedSlopes A U
  have hB : B.Nonempty := projectedSlopes_nonempty A hA U
  have hpB (z : Vec r) (hz : z ≠ 0) : 0 < finiteMaxLinear B hB z := by
    rw [finiteMaxLinear_projected_value]
    have hUz : U.mulVec z ≠ 0 := by
      intro hu
      apply hz
      apply orthonormal_transpose_fullRowRank U hU
      simpa only [Matrix.transpose_transpose, Matrix.mulVec_zero] using hu
    exact hp _ ((hspan _).mpr ⟨z, rfl⟩) hUz
  obtain ⟨μ, hμ, hball⟩ := positive_finiteMax_convexHull_ball B hB hpB
  let S := Submodule.span ℝ (A : Set (Vec n))
  have hcont : Continuous (fun v : S => euclideanVector (Uᵀ.mulVec (v : Vec n))) := by
    exact (PiLp.continuous_equiv_symm _ _).comp ((AffineProjection.matrixCLM Uᵀ).continuous.comp continuous_subtype_val)
  have hn : ∀ᶠ v : S in 𝓝 0, ‖euclideanVector (Uᵀ.mulVec (v : Vec n))‖ < μ := by
    have ht : Tendsto (fun v : S => ‖euclideanVector (Uᵀ.mulVec (v : Vec n))‖) (𝓝 0) (𝓝 0) := by
      have ht := hcont.norm.tendsto 0
      have hz : euclideanVector (Uᵀ.mulVec ((0 : S) : Vec n)) = 0 := by
        rw [Submodule.coe_zero, Matrix.mulVec_zero]
        rfl
      simpa only [hz, norm_zero] using ht
    exact ht.eventually (eventually_lt_nhds hμ)
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hn] with v hv
  have hz := hball (Uᵀ.mulVec (v : Vec n)) hv
  have hsub : U.mulVec '' (B : Set (Vec r)) ⊆ (A : Set (Vec n)) := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    simpa only [orthonormal_projection_on_range U hU a (hAsub a ha)] using ha
  have himg : U.mulVec (Uᵀ.mulVec (v : Vec n)) ∈ convexHull ℝ (A : Set (Vec n)) := by
    have h := Set.mem_image_of_mem U.mulVec hz
    change U.mulVec (Uᵀ.mulVec (v : Vec n)) ∈ U.mulVecLin '' (convexHull ℝ (B : Set (Vec r))) at h
    rw [U.mulVecLin.image_convexHull] at h
    exact convexHull_mono hsub h
  simpa only [orthonormal_projection_on_range U hU (v : Vec n) ((hspan _).mp v.property)] using himg

/-- Nonnegativity and a zero fiber closed under negation force strict positivity
on the actual slope span. The zero fiber's other linear properties are not
needed for this implication. -/
theorem positive_on_span_of_zero_neg {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (hn : ∀ x, 0 ≤ finiteMaxLinear A hA x)
    (hzneg : ∀ x, finiteMaxLinear A hA x = 0 → finiteMaxLinear A hA (-x) = 0)
    (x : Vec n) (hxS : x ∈ Submodule.span ℝ (A : Set (Vec n))) (hx : x ≠ 0) :
    0 < finiteMaxLinear A hA x := by
  by_contra hnp
  have hx0 : finiteMaxLinear A hA x = 0 := le_antisymm (le_of_not_gt hnp) (hn x)
  have hneg := hzneg x hx0
  have hall (a : Vec n) (ha : a ∈ A) : dot x a = 0 := by
    have h1 := slope_le_finiteMaxLinear A hA ha x
    have h2 := slope_le_finiteMaxLinear A hA ha (-x)
    rw [hx0] at h1
    rw [hneg] at h2
    have hh : dot a (-x) = -dot a x := dotProduct_neg _ _
    rw [hh] at h2
    rw [show dot x a = dot a x from dotProduct_comm _ _]
    linarith
  have hker : Submodule.span ℝ (A : Set (Vec n)) ≤ LinearMap.ker (gradientFunctional x).toLinearMap := by
    apply Submodule.span_le.mpr
    intro a ha
    change (gradientFunctional x) a = 0
    rw [gradientFunctional_apply]
    exact hall a ha
  have hxx : dot x x = 0 := by
    have h := hker hxS
    change (gradientFunctional x) x = 0 at h
    simpa only [gradientFunctional_apply] using h
  have hp : 0 < dot x x := by
    simpa only [metricEnergy, Matrix.one_mulVec] using metricEnergy_pos Matrix.PosDef.one hx
  linarith

theorem relativeInteriorZero_iff_nonneg_linear_zero_fiber {n : ℕ}
    (A : Finset (Vec n)) (hA : A.Nonempty) :
    RelativeInteriorZero A ↔ (∀ x, 0 ≤ finiteMaxLinear A hA x) ∧
      ∃ S : Submodule ℝ (Vec n), ∀ x, finiteMaxLinear A hA x = 0 ↔ x ∈ S := by
  constructor
  · intro hri
    obtain ⟨r, U, hU, hspan⟩ := exists_slope_span_coordinates A
    exact ⟨relativeInteriorZero_nonneg A hA hri, LinearMap.ker Uᵀ.mulVecLin,
      relativeInterior_value_zero_iff_projection_zero A hA hri U hU hspan⟩
  · rintro ⟨hn, S, hS⟩
    apply relativeInteriorZero_of_positive_on_span A hA
    apply positive_on_span_of_zero_neg A hA hn
    intro x hx
    exact (hS (-x)).mpr (S.neg_mem ((hS x).mp hx))

end Homogeneous
end BfgsVerification
