import BfgsVerification.InwardRadial
import BfgsVerification.QuadraticGaugeGeometry

noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification.RadialNormConvention

/-- The precise source η/G lower radius estimate uses the actual Euclidean norm. -/
theorem positive_band_radius_lower {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) {x g : Vec n} {η G : ℝ}
    (hη : 0 < η) (hG : 0 < G) (hbound : sqNorm g ≤ G^2)
    (hx : F star+η ≤ F x) (hg : HasFDerivAt F (gradientFunctional g) x) :
    η/G ≤ ‖euclideanVector (x-star)‖ := by
  have hs := convex_supporting_inequality hF hg star
  have hp : η ≤ dot g (x-star) := by
    rw [RadialCertificate.dot_sub_right] at hs ⊢
    linarith
  have hn : sqNorm (x-star) ≤ ‖euclideanVector (x-star)‖^2 :=
    (FrameNorms.euclidean_norm_sq (euclideanVector (x-star))).ge
  have he := abs_dot_le_of_sqNorm_le g (x-star) G ‖euclideanVector (x-star)‖
    hG.le (norm_nonneg _) hbound hn
  apply (div_le_iff₀ hG).mpr
  nlinarith [hp.trans (le_abs_self _)]

theorem compact_positive_band_radii {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {K : Set (Vec n)} (hK : IsCompact K) (star : Vec n) :
    ∃ G R : ℝ, 0 < G ∧ 0 < R ∧ ∀ η : ℝ, 0 < η →
      ∀ x g, x ∈ K → F star+η ≤ F x → HasFDerivAt F (gradientFunctional g) x →
        η/G ≤ ‖euclideanVector (x-star)‖ ∧ ‖euclideanVector (x-star)‖ ≤ R := by
  obtain ⟨G,hG,hgb⟩ := convex_gradient_bound_on_compact hF hK
  obtain ⟨R,hR,hr⟩ := compact_sqNorm_radius hK star
  refine ⟨G,R,hG,hR,?_⟩
  intro η hη x g hx hval hg
  refine ⟨positive_band_radius_lower hF star hη hG (hgb x hx g hg) hval hg,?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) hR.le).mp
  simpa only [FrameNorms.euclidean_norm_sq] using hr x hx

def HasNormScaledInwardBounds {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n))
    (star : Vec n) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M θ : ℝ, 0 < θ ∧ θ ≤ 1/2 ∧
    ∀ x g, x ∈ K → F star+η ≤ F x → HasFDerivAt F (gradientFunctional g) x →
      ∀ t : ℝ, 0 ≤ t → t ≤ θ →
        0 ≤ RadialCertificate.supportingError F x g (RadialCertificate.inwardPoint star x t) ∧
        RadialCertificate.supportingError F x g (RadialCertificate.inwardPoint star x t) ≤
          M/2*t^2*‖euclideanVector (x-star)‖^2

/-- The literal factor ‖x-star‖₂² may be included or omitted in IR on compact
positive bands. Radius and gradient bounds are derived from actual convexity. -/
theorem inward_iff_norm_scaled_on_compact {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {K : Set (Vec n)} (hK : IsCompact K) (star : Vec n) :
    RadialCertificate.HasInwardTaylorBounds F K star ↔ HasNormScaledInwardBounds F K star := by
  obtain ⟨G,R,hG,hR,hr⟩ := compact_positive_band_radii hF hK star
  constructor
  · intro hIR η hη
    obtain ⟨M,θ,hθ,hθhalf,he⟩ := hIR η hη
    refine ⟨max M 0*(G/η)^2,θ,hθ,hθhalf,?_⟩
    intro x g hx hv hg t ht0 htθ
    have hb := he x g hx hv hg t ht0 htθ
    have hlo := (hr η hη x g hx hv hg).1
    have hprod : 1 ≤ (G/η)*‖euclideanVector (x-star)‖ := by
      have heq : (G/η)*(η/G)=1 := by field_simp [hG.ne',hη.ne']
      rw [← heq]
      exact mul_le_mul_of_nonneg_left hlo (div_nonneg hG.le hη.le)
    have hs : 1 ≤ (G/η)^2*‖euclideanVector (x-star)‖^2 := by
      have hh := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (by positivity)).mpr hprod
      simpa only [one_pow,mul_pow] using hh
    have hM : max M 0 ≤ (max M 0*(G/η)^2)*‖euclideanVector (x-star)‖^2 := by
      simpa only [mul_one,mul_assoc] using mul_le_mul_of_nonneg_left hs (le_max_right M 0)
    refine ⟨hb.1,hb.2.trans ?_⟩
    calc
      M/2*t^2 ≤ max M 0/2*t^2 := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (le_max_left M 0) (by norm_num)) (sq_nonneg t)
      _ ≤ ((max M 0*(G/η)^2)*‖euclideanVector (x-star)‖^2)/2*t^2 :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hM (by norm_num)) (sq_nonneg t)
      _ = _ := by ring
  · intro hIR η hη
    obtain ⟨M,θ,hθ,hθhalf,he⟩ := hIR η hη
    refine ⟨max M 0*R^2,θ,hθ,hθhalf,?_⟩
    intro x g hx hv hg t ht0 htθ
    have hb := he x g hx hv hg t ht0 htθ
    have hupper := (hr η hη x g hx hv hg).2
    have hs : ‖euclideanVector (x-star)‖^2 ≤ R^2 :=
      (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hupper
    have hM : M*‖euclideanVector (x-star)‖^2 ≤ max M 0*R^2 :=
      (mul_le_mul_of_nonneg_right (le_max_left M 0) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hs (le_max_right M 0))
    refine ⟨hb.1,hb.2.trans ?_⟩
    calc
      M/2*t^2*‖euclideanVector (x-star)‖^2 = (M*‖euclideanVector (x-star)‖^2)/2*t^2 := by ring
      _ ≤ (max M 0*R^2)/2*t^2 := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hM (by norm_num)) (sq_nonneg t)

end BfgsVerification.RadialNormConvention
