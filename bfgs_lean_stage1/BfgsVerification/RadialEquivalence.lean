import BfgsVerification.RadialCertificate
import BfgsVerification.EuclideanEstimates

noncomputable section
open scoped BigOperators
open Set

namespace BfgsVerification
namespace RadialCertificate

/-- Module R's (SP), on exactly the ordered positive-curvature endpoint pairs
used by its radial secant condition. -/
def HasInterceptBounds {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n))
    (star : Vec n) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x z g h,
    x ∈ K → z ∈ K → F star + η ≤ F z → F z ≤ F x →
    HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
    0 < secantCurvature x z g h →
    (optimizerIntercept F star z h - optimizerIntercept F star x g) ^ 2 ≤
      C * secantCurvature x z g h

theorem supportingError_le_curvature {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x z g h : Vec n}
    (hh : HasFDerivAt F (gradientFunctional h) z) :
    supportingError F x g z ≤ secantCurvature x z g h := by
  rw [secantCurvature_eq_errors F]
  exact le_add_of_nonneg_right (supportingError_nonneg hF hh x)

/-- The source's explicit Tmax=4GR bound uses actual Euclidean squared norms. -/
theorem secantCurvature_le_four_mul {n : ℕ} (star x z g h : Vec n) (G R : ℝ)
    (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hg : sqNorm g ≤ G ^ 2) (hh : sqNorm h ≤ G ^ 2)
    (hx : sqNorm (x - star) ≤ R ^ 2) (hz : sqNorm (z - star) ≤ R ^ 2) :
    secantCurvature x z g h ≤ 4 * G * R := by
  have hs : sqNorm (z - x) ≤ (2 * R) ^ 2 := by
    simpa only [sub_sub_sub_cancel_right] using sqNorm_difference_le_four (z - star) (x - star) R hz hx
  have hb := abs_dot_le_of_sqNorm_le (h - g) (z - x) (2 * G) (2 * R)
    (by positivity) (by positivity) (sqNorm_difference_le_four h g G hh hg) hs
  unfold secantCurvature
  calc
    dot (h - g) (z - x) ≤ |dot (h - g) (z - x)| := le_abs_self _
    _ ≤ (2 * G) * (2 * R) := hb
    _ = 4 * G * R := by ring

/-- The radial numerator's absolute bound used by the inward-probe optimization. -/
theorem abs_radialNumerator_le_two_mul {n : ℕ} (star z g h : Vec n) (G R : ℝ)
    (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hg : sqNorm g ≤ G ^ 2) (hh : sqNorm h ≤ G ^ 2)
    (hz : sqNorm (z - star) ≤ R ^ 2) :
    |radialNumerator star z g h| ≤ 2 * G * R :=
  abs_dot_le_of_sqNorm_le (h - g) (z - star) (2 * G) R
    (by positivity) hR (sqNorm_difference_le_four h g G hh hg) hz

/-- Full objective-pair equivalence between the radial correction bound and
regularity of the supporting-plane height at the optimizer. Compactness supplies
the Euclidean radius and gradient bounds; no derivative continuity is assumed. -/
theorem radial_iff_intercept_on_compact {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {K : Set (Vec n)} (hK : IsCompact K) (star : Vec n) :
    HasRadialSecantBounds F K star ↔ HasInterceptBounds F K star := by
  obtain ⟨G, hG, hg⟩ := convex_gradient_bound_on_compact hF hK
  obtain ⟨R, hR, hr⟩ := compact_sqNorm_radius hK star
  have hT (x z g h : Vec n) (hx : x ∈ K) (hz : z ∈ K)
      (hdg : HasFDerivAt F (gradientFunctional g) x)
      (hdh : HasFDerivAt F (gradientFunctional h) z) :
      secantCurvature x z g h ≤ 4 * G * R :=
    secantCurvature_le_four_mul star x z g h G R hG.le hR.le
      (hg x hx g hdg) (hg z hz h hdh) (hr x hx) (hr z hz)
  constructor
  · intro hRS η hη
    obtain ⟨C, hC⟩ := hRS η hη
    refine ⟨2 * C + 2 * (4 * G * R), ?_⟩
    intro x z g h hx hz hband horder hdg hdh ht
    have hb := intercept_bound_of_radial (supportingError_nonneg hF hdg z)
      (supportingError_le_curvature hF hdh) (hT x z g h hx hz hdg hdh)
      (hC x z g h hx hz hband horder hdg hdh ht)
    rw [radialNumerator_eq_error_intercepts F star x z g h] at hb
    convert hb using 1 <;> ring
  · intro hSP η hη
    obtain ⟨C, hC⟩ := hSP η hη
    refine ⟨2 * C + 2 * (4 * G * R), ?_⟩
    intro x z g h hx hz hband horder hdg hdh ht
    have hbound : (radialNumerator star z g h - supportingError F x g z) ^ 2 ≤
        C * secantCurvature x z g h := by
      rw [radialNumerator_eq_error_intercepts F star x z g h]
      convert hC x z g h hx hz hband horder hdg hdh ht using 1 <;> ring
    exact radial_bound_of_intercept (supportingError_nonneg hF hdg z)
      (supportingError_le_curvature hF hdh) (hT x z g h hx hz hdg hdh) hbound

end RadialCertificate
end BfgsVerification
