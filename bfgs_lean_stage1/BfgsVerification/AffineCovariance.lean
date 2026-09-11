import BfgsVerification.AffineCertificates

/-! Module T's coordinate covariance, with actual invertible matrices and
translations, both directions, unchanged constants and unchanged pair domains. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Set

namespace BfgsVerification
namespace AffineCertificate
open AffineProjection TransportedCertificate

def backwardAffineMap {n : ℕ} (A : Mat n) (b : Vec n) : Vec n →ᵃ[ℝ] Vec n where
  toFun := backward A b
  linear := A⁻¹.mulVecLin
  map_vadd' x v := by
    change A⁻¹.mulVec (v + x - b) = A⁻¹.mulVec v + A⁻¹.mulVec (x - b)
    rw [← Matrix.mulVec_add]
    congr 1
    abel

theorem objective_convex {n : ℕ} (A : Mat n) (b : Vec n) {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) : ConvexOn ℝ univ (objective A b F) := by
  simpa only [Set.preimage_univ, Function.comp_def, objective, backwardAffineMap] using
    hF.comp_affineMap (backwardAffineMap A b)

theorem forward_continuous {n : ℕ} (A : Mat n) (b : Vec n) : Continuous (forward A b) := by
  exact ((matrixCLM A).continuous.add continuous_const)

theorem transformed_compact {n : ℕ} (A : Mat n) (b : Vec n) {K : Set (Vec n)}
    (hK : IsCompact K) : IsCompact (forward A b '' K) := hK.image (forward_continuous A b)

theorem transformed_minimum {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (b : Vec n)
    {F : Vec n → ℝ} (star : Vec n) (hmin : ∀ x, F star ≤ F x) :
    ∀ z, objective A b F (forward A b star) ≤ objective A b F z := by
  intro z
  simpa only [objective, backward_forward A hA] using hmin (backward A b z)

theorem inverse_forward {n : ℕ} (A : Mat n) (b z : Vec n) :
    forward A⁻¹ (-A⁻¹.mulVec b) z = backward A b z := by
  change A⁻¹.mulVec z - A⁻¹.mulVec b = A⁻¹.mulVec (z - b)
  rw [Matrix.mulVec_sub]

theorem inverse_backward {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (b x : Vec n) :
    backward A⁻¹ (-A⁻¹.mulVec b) x = forward A b x := by
  simp only [backward, forward, Matrix.nonsing_inv_nonsing_inv _ hA.isUnit,
    sub_neg_eq_add, Matrix.mulVec_add, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.one_mulVec]

theorem twice_objective {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (b : Vec n)
    (F : Vec n → ℝ) :
    objective A⁻¹ (-A⁻¹.mulVec b) (objective A b F) = F := by
  funext x
  simp only [objective, inverse_backward A hA, backward_forward A hA]

theorem twice_domain {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (b : Vec n)
    (K : Set (Vec n)) :
    forward A⁻¹ (-A⁻¹.mulVec b) '' (forward A b '' K) = K := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hx⟩
    rw [inverse_forward, backward_forward A hA] at hx
    simpa only [← hx] using hz
  · intro hx
    exact ⟨forward A b x, ⟨x, hx, rfl⟩,
      by rw [inverse_forward, backward_forward A hA]⟩

/-- Existence of the complete objective-only certificate is equivalent under
any invertible affine coordinate change. No sign restriction on C or bounds
on the certificate field are added. -/
theorem hasBandCertificates_affine_iff {n : ℕ} (A : Mat n) (hA : A.det ≠ 0)
    (b : Vec n) (F : Vec n → ℝ) (K : Set (Vec n)) (fstar c₁ c₂ : ℝ) :
    HasBandCertificates F K fstar c₁ c₂ ↔
      HasBandCertificates (objective A b F) (forward A b '' K) fstar c₁ c₂ := by
  constructor
  · exact hasBandCertificates_transform A hA b
  · intro h
    have hi : A⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det A hA.isUnit).ne_zero
    have ht := hasBandCertificates_transform A⁻¹ hi (-A⁻¹.mulVec b) h
    simpa only [twice_objective A hA, twice_domain A hA] using ht

theorem forward_pair_decrease {n : ℕ} (A : Mat n) (hA : A.det ≠ 0)
    (b x z g : Vec n) :
    pairDecrease (forward A b x) (forward A b z) ((A⁻¹)ᵀ.mulVec g) = pairDecrease x z g := by
  simp only [pairDecrease, pairStep, forward_difference, dot_inverse_transpose A hA]

theorem forward_pair_curvature {n : ℕ} (A : Mat n) (hA : A.det ≠ 0)
    (b x z g h : Vec n) :
    pairCurvature (forward A b x) (forward A b z) ((A⁻¹)ᵀ.mulVec g) ((A⁻¹)ᵀ.mulVec h) =
      pairCurvature x z g h := by
  simp only [pairCurvature, pairStep, forward_difference, ← Matrix.mulVec_sub,
    dot_inverse_transpose A hA]

/-- Affine coordinates preserve precisely the eligible-pair predicate,
including actual endpoint differentiability and every acceptance comparison. -/
theorem eligible_pair_affine_iff {n : ℕ} (A : Mat n) (hA : A.det ≠ 0)
    (b : Vec n) {F : Vec n → ℝ} {c₁ c₂ : ℝ} (x z g h : Vec n) :
    EligiblePair F c₁ c₂ x z g h ↔
      EligiblePair (objective A b F) c₁ c₂ (forward A b x) (forward A b z)
        ((A⁻¹)ᵀ.mulVec g) ((A⁻¹)ᵀ.mulVec h) := by
  constructor
  · intro hp
    have hg' : HasFDerivAt F (gradientFunctional g) (backward A b (forward A b x)) := by
      simpa only [backward_forward A hA] using hp.gradient_x
    have hh' : HasFDerivAt F (gradientFunctional h) (backward A b (forward A b z)) := by
      simpa only [backward_forward A hA] using hp.gradient_z
    refine ⟨transformed_gradient A b hg', transformed_gradient A b hh', ?_, ?_, ?_, ?_⟩
    · rw [forward_pair_decrease A hA]
      exact hp.decrease_pos
    · simpa only [forward_pair_decrease A hA, objective, backward_forward A hA] using hp.armijo
    · simpa only [forward_pair_decrease A hA, objective, backward_forward A hA] using hp.convex_decrease
    · simpa only [forward_pair_decrease A hA, forward_pair_curvature A hA] using hp.curvature
  · intro hp
    have hback := original_eligible_pair A hA b hp
    simpa only [backward_forward A hA, transpose_inverse_transpose A hA] using hback

end AffineCertificate
end BfgsVerification
