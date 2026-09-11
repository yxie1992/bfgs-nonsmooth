import BfgsVerification.PlanarConvexCorner
import BfgsVerification.PlanarCrossingAlgebra
import BfgsVerification.CenteredCocoercivity

/-! Actual finite-max endpoint gradients, crossing points, and norm bookkeeping. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification
namespace PlanarCrossing
open ConvexSubdifferential PlanarCornerCharts HomogeneousPlanar

theorem actual_gradient_eq_active_branch {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ} {x g : Vec n}
    (hrep : LocalFiniteMax F f x) (hf : ∀ i, DifferentiableAt ℝ (f i) x)
    (hg : HasFDerivAt F (gradientFunctional g) x) {i : Fin m} (hi : f i x=F x) :
    coordinateGradient (f i) x=g := by
  exact supporting_vector_eq_gradient
    (active_gradient_supports hF hrep (fun j => hasFDerivAt_coordinateGradient (hf j))
      (mem_activeIndices.mpr hi)) hg

theorem exists_actual_active_gradient {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ} {x g : Vec n}
    (hrep : LocalFiniteMax F f x) (hf : ∀ i, DifferentiableAt ℝ (f i) x)
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    ∃ i, f i x=F x ∧ coordinateGradient (f i) x=g := by
  obtain ⟨i,hi⟩ := activeIndices_nonempty hrep
  exact ⟨i,mem_activeIndices.mp hi,
    actual_gradient_eq_active_branch hF hrep hf hg (mem_activeIndices.mp hi)⟩

theorem pi_norm_le_euclidean_norm (v : Vec 2) : ‖v‖≤‖euclideanVector v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [FrameNorms.euclidean_norm_sq]
  exact CenteredSmoothSublinear.pi_norm_sq_le_sqNorm v

theorem euclidean_norm_le_two_pi_norm (v : Vec 2) : ‖euclideanVector v‖≤2*‖v‖ := by
  have h0 := norm_le_pi_norm v (0 : Fin 2)
  have h1 := norm_le_pi_norm v (1 : Fin 2)
  have h0s := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h0
  have h1s := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h1
  rw [Real.norm_eq_abs,sq_abs] at h0s h1s
  have he := FrameNorms.euclidean_norm_sq (euclideanVector v)
  change ‖euclideanVector v‖^2=∑ i : Fin 2, (v i)^2 at he
  rw [Fin.sum_univ_two] at he
  nlinarith [norm_nonneg v,norm_nonneg (euclideanVector v)]

/-- Opposite active branches give a genuine tie point on the closed segment;
no finite-intersection assertion about the switching curve is required. -/
theorem exists_tie_on_segment {F f₀ f₁ : Vec 2 → ℝ} {x z : Vec 2}
    (hc₀ : ContinuousOn f₀ (segment ℝ x z)) (hc₁ : ContinuousOn f₁ (segment ℝ x z))
    (hx : f₁ x≤f₀ x) (hz : f₀ z≤f₁ z) :
    ∃ p ∈ segment ℝ x z, f₀ p=f₁ p := by
  obtain ⟨p,hp,he⟩ := (convex_segment x z).isPreconnected.intermediate_value₂
    (left_mem_segment ℝ x z) (right_mem_segment ℝ x z) hc₁ hc₀ hx hz
  exact ⟨p,hp,he.symm⟩

/-- Each part of a segment is no longer than the whole displacement. -/
theorem segment_sub_norm_le {x z p : Vec 2} (hp : p ∈ segment ℝ x z) :
    ‖p-x‖≤‖z-x‖ ∧ ‖z-p‖≤‖z-x‖ := by
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨t,ht,rfl⟩ := hp
  have he₁ : AffineMap.lineMap x z t-x=t • (z-x) := by
    rw [AffineMap.lineMap_apply_module']; abel
  have he₂ : z-AffineMap.lineMap x z t=(1-t) • (z-x) := by
    rw [AffineMap.lineMap_apply_module']; module
  rw [he₁,he₂,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg ht.1,abs_of_nonneg (sub_nonneg.mpr ht.2)]
  constructor <;> nlinarith [ht.1,ht.2,norm_nonneg (z-x)]

end PlanarCrossing
end BfgsVerification
