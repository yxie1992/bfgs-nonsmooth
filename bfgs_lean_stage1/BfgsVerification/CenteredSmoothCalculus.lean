import BfgsVerification.ConvexDifferentiability
import BfgsVerification.EuclideanEstimates

noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter

namespace BfgsVerification
namespace CenteredSmoothSublinear

/-- Standard local C1,1 regularity, using the derivative in the ambient norm.
The conclusions below state their Euclidean constants explicitly. -/
def LocallyC11On {n : ℕ} (U : Set (Vec n)) (ψ : Vec n → ℝ) : Prop :=
  DifferentiableOn ℝ ψ U ∧ LocallyLipschitzOn U (fderiv ℝ ψ)

/-- The finite-Pi norm is dominated by the actual Euclidean norm. -/
theorem pi_norm_sq_le_sqNorm {n : ℕ} (v : Vec n) : ‖v‖ ^ 2 ≤ sqNorm v := by
  have hb : ‖v‖ ≤ Real.sqrt (sqNorm v) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (sqNorm_nonneg v), Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have h := (sq_le_sq₀ (norm_nonneg v) (Real.sqrt_nonneg (sqNorm v))).mpr hb
  rwa [Real.sq_sqrt (sqNorm_nonneg v)] at h

/-- A derivative of a function convex on U supports every other point of U.
Convexity or regularity outside U is not assumed. -/
theorem supporting_inequality_on {n : ℕ} {U : Set (Vec n)} {ψ : Vec n → ℝ}
    (hψ : ConvexOn ℝ U ψ) {x : Vec n} {l : Vec n →L[ℝ] ℝ}
    (hl : HasFDerivAt ψ l x) (hx : x ∈ U) {y : Vec n} (hy : y ∈ U) :
    l (y - x) ≤ ψ y - ψ x := by
  let a := AffineMap.lineMap (k := ℝ) x y
  have hc : ConvexOn ℝ (a ⁻¹' U) (ψ ∘ a) := hψ.comp_affineMap a
  have hp : HasDerivAt (a : ℝ → Vec n) (y - x) 0 := by
    change HasDerivAt (fun t : ℝ => t • (y - x) + x) (y - x) 0
    simpa only [one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).add_const x
  have hd : HasDerivAt (ψ ∘ a) (l (y - x)) 0 := by
    exact hl.comp_hasDerivAt_of_eq 0 hp (by simp [a])
  have hs := hc.le_slope_of_hasDerivAt (by simpa [a] using hx)
    (by simpa [a] using hy) (show (0 : ℝ) < 1 by norm_num) hd
  simpa [slope_def_field, a] using hs

/-- An elementary local Taylor estimate. Its constant is deliberately not
claimed sharp; later we choose the source's uniform constant large enough. -/
theorem taylor_remainder_le {n : ℕ} {ψ : Vec n → ℝ} {V : Set (Vec n)}
    (hV : Convex ℝ V) (hψ : ∀ w ∈ V, DifferentiableAt ℝ ψ w)
    {M : ℝ≥0} (hM : LipschitzOnWith M (fderiv ℝ ψ) V)
    {x z : Vec n} (hx : x ∈ V) (hz : z ∈ V) :
    |ψ z - ψ x - (fderiv ℝ ψ x) (z - x)| ≤ (M : ℝ) * sqNorm (z - x) := by
  let f : Vec n → ℝ := fun w => ψ w - (fderiv ℝ ψ x) w
  let D : Vec n → (Vec n →L[ℝ] ℝ) := fun w => fderiv ℝ ψ w - fderiv ℝ ψ x
  have hsub : segment ℝ x z ⊆ V := hV.segment_subset hx hz
  have hd : ∀ w ∈ segment ℝ x z, HasFDerivWithinAt f (D w) (segment ℝ x z) w := by
    intro w hw
    exact ((hψ w (hsub hw)).hasFDerivAt.sub
      (fderiv ℝ ψ x).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ w ∈ segment ℝ x z, ‖D w‖ ≤ (M : ℝ) * ‖z - x‖ := by
    intro w hw
    exact (hM.norm_sub_le (hsub hw) hx).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hw) M.coe_nonneg)
  have he := (convex_segment x z).norm_image_sub_le_of_norm_hasFDerivWithin_le hd hbound
    (left_mem_segment ℝ x z) (right_mem_segment ℝ x z)
  have he' : |ψ z - ψ x - (fderiv ℝ ψ x) (z - x)| ≤ (M : ℝ) * ‖z - x‖ ^ 2 := by
    convert he using 1
    · rw [Real.norm_eq_abs]
      congr 1
      simp only [f, map_sub]
      ring
    · ring
  exact he'.trans (mul_le_mul_of_nonneg_left (pi_norm_sq_le_sqNorm _) M.coe_nonneg)

end CenteredSmoothSublinear
end BfgsVerification
