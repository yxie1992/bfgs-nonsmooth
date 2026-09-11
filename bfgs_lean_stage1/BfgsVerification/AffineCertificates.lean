import BfgsVerification.AffineCertificateAlgebra
import BfgsVerification.ConvexDifferentiability

/-! Module T: full affine covariance of actual objective-pair certificates.
The source constants and the small-decrease threshold are unchanged. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Set

namespace BfgsVerification
namespace AffineCertificate
open AffineProjection TransportedCertificate

theorem backward_pair_decrease {n : ℕ} (A : Mat n) (hA : A.det ≠ 0)
    (b x z g : Vec n) :
    pairDecrease (backward A b x) (backward A b z) (Aᵀ.mulVec g) = pairDecrease x z g := by
  simp only [pairDecrease, pairStep, backward_difference, dot_transpose_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.one_mulVec]

theorem backward_pair_curvature {n : ℕ} (A : Mat n) (hA : A.det ≠ 0)
    (b x z g h : Vec n) :
    pairCurvature (backward A b x) (backward A b z) (Aᵀ.mulVec g) (Aᵀ.mulVec h) =
      pairCurvature x z g h := by
  simp only [pairCurvature, pairStep, backward_difference, ← Matrix.mulVec_sub,
    dot_transpose_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.one_mulVec]

theorem original_eligible_pair {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (b : Vec n)
    {F : Vec n → ℝ} {c₁ c₂ : ℝ} {x z g h : Vec n}
    (hp : EligiblePair (objective A b F) c₁ c₂ x z g h) :
    EligiblePair F c₁ c₂ (backward A b x) (backward A b z) (Aᵀ.mulVec g) (Aᵀ.mulVec h) where
  gradient_x := original_gradient A hA b hp.gradient_x
  gradient_z := original_gradient A hA b hp.gradient_z
  decrease_pos := by rw [backward_pair_decrease A hA]; exact hp.decrease_pos
  armijo := by rw [backward_pair_decrease A hA]; exact hp.armijo
  convex_decrease := by rw [backward_pair_decrease A hA]; exact hp.convex_decrease
  curvature := by rw [backward_pair_decrease A hA, backward_pair_curvature A hA]; exact hp.curvature

theorem transformed_band_iff {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (b : Vec n)
    (F : Vec n → ℝ) (K : Set (Vec n)) (fstar η : ℝ) (x : Vec n) :
    x ∈ positiveBand (objective A b F) (forward A b '' K) fstar η ↔
      backward A b x ∈ positiveBand F K fstar η := by
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hx⟩
    exact ⟨by simpa only [backward_forward A hA] using hy, hx⟩
  · rintro ⟨hx, hlevel⟩
    exact ⟨⟨backward A b x, hx, forward_backward A hA b x⟩, hlevel⟩

/-- Actual affine transformation of a source certificate. Its four constants
m,C,L,delta are retained verbatim. -/
def transform {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (b : Vec n)
    {F : Vec n → ℝ} {K : Set (Vec n)} {fstar c₁ c₂ η : ℝ}
    (C : BandCertificate F K fstar c₁ c₂ η) :
    BandCertificate (objective A b F) (forward A b '' K) fstar c₁ c₂ η where
  W := field A b C.W
  m := C.m
  C := C.C
  L := C.L
  δ := C.δ
  m_pos := C.m_pos
  L_nonneg := C.L_nonneg
  delta_pos := C.delta_pos
  positive_semidefinite x hx hdiff := by
    have hx' := (transformed_band_iff A hA b F K fstar η x).mp hx
    have hd := original_gradient A hA b (hasFDerivAt_coordinateGradient hdiff)
    have hp := (C.positive_semidefinite _ hx' hd.differentiableAt).mul_mul_conjTranspose_same A
    simpa only [field, Matrix.conjTranspose_eq_transpose_of_trivial] using hp
  visibility x hx g hg := by
    have hx' := (transformed_band_iff A hA b F K fstar η x).mp hx
    have hd := original_gradient A hA b hg
    change C.m ≤ metricEnergy (A * C.W (backward A b x) * Aᵀ) g
    rw [congruence_energy]
    exact C.visibility _ hx' _ hd
  secant x z g h hx hz hp hd := by
    have hx' := (transformed_band_iff A hA b F K fstar η x).mp hx
    have hz' := (transformed_band_iff A hA b F K fstar η z).mp hz
    have hp' := original_eligible_pair A hA b hp
    have hd' : pairDecrease (backward A b x) (backward A b z) (Aᵀ.mulVec g) ≤ C.δ := by
      rw [backward_pair_decrease A hA]
      exact hd
    have he := C.secant _ _ _ _ hx' hz' hp' hd'
    rw [backward_pair_curvature A hA] at he
    change metricEnergy (A * C.W (backward A b z) * Aᵀ) (h - g) ≤ _
    rw [congruence_energy, Matrix.mulVec_sub]
    exact he
  transport x z g h hx hz hp hd := by
    have hx' := (transformed_band_iff A hA b F K fstar η x).mp hx
    have hz' := (transformed_band_iff A hA b F K fstar η z).mp hz
    have hp' := original_eligible_pair A hA b hp
    have hd' : pairDecrease (backward A b x) (backward A b z) (Aᵀ.mulVec g) ≤ C.δ := by
      rw [backward_pair_decrease A hA]
      exact hd
    have he := C.transport _ _ _ _ hx' hz' hp' hd'
    have hW : (C.W (backward A b x)).IsSymm := by
      simpa only [Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using
        (C.positive_semidefinite _ hx' hp'.gradient_x.differentiableAt).isHermitian
    have hZ : (C.W (backward A b z)).IsSymm := by
      simpa only [Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using
        (C.positive_semidefinite _ hz' hp'.gradient_z.differentiableAt).isHermitian
    have hstep : A.mulVec (pairStep (backward A b x) (backward A b z)) = pairStep x z := by
      simp only [pairStep, backward_difference, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.one_mulVec]
    have ht := (projected_transport_covariant A hA _ _ hW hZ _ _).mp he
    simpa only [field, backward_pair_decrease A hA, hstep] using ht

theorem transform_field {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (b : Vec n)
    {F : Vec n → ℝ} {K : Set (Vec n)} {fstar c₁ c₂ η : ℝ}
    (C : BandCertificate F K fstar c₁ c₂ η) (x : Vec n) :
    (transform A hA b C).W (forward A b x) = A * C.W x * Aᵀ := by
  simp only [transform, field, backward_forward A hA]

theorem transform_constants {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (b : Vec n)
    {F : Vec n → ℝ} {K : Set (Vec n)} {fstar c₁ c₂ η : ℝ}
    (C : BandCertificate F K fstar c₁ c₂ η) :
    (transform A hA b C).m = C.m ∧ (transform A hA b C).C = C.C ∧
    (transform A hA b C).L = C.L ∧ (transform A hA b C).δ = C.δ :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem hasBandCertificates_transform {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (b : Vec n)
    {F : Vec n → ℝ} {K : Set (Vec n)} {fstar c₁ c₂ : ℝ}
    (hc : HasBandCertificates F K fstar c₁ c₂) :
    HasBandCertificates (objective A b F) (forward A b '' K) fstar c₁ c₂ := by
  intro η hη hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨C⟩ := hc η hη ⟨backward A b x, (transformed_band_iff A hA b F K fstar η x).mp hx⟩
  exact ⟨transform A hA b C⟩

end AffineCertificate
end BfgsVerification
