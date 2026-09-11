import BfgsVerification.CompactConvergence

/-!
# Radial secant certificates and supporting-plane intercepts

Module R's radial certificate is imposed on objective endpoint pairs and positive
bands. Its convergence consequence is derived from the actual full-BFGS energy
identity. This file does not assume radial differentiability away from endpoints.
-/

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification
namespace RadialCertificate

/-- Supporting-plane error; only the base point's derivative is needed. -/
def supportingError {n : ℕ} (F : Vec n → ℝ) (x g z : Vec n) : ℝ :=
  F z - F x - dot g (z - x)

/-- Amount by which the supporting plane at x undershoots the value at star. -/
def optimizerIntercept {n : ℕ} (F : Vec n → ℝ) (star x g : Vec n) : ℝ :=
  dot g (x - star) - (F x - F star)

/-- Curvature paired with displacement between actual objective endpoints. -/
def secantCurvature {n : ℕ} (x z g h : Vec n) : ℝ := dot (h - g) (z - x)

/-- Secant numerator in the radial correction at the new endpoint. -/
def radialNumerator {n : ℕ} (star z g h : Vec n) : ℝ := dot (h - g) (z - star)

/-- Module R's (RS): differentiable ordered endpoints in any nonempty positive
band, with positive curvature. No BFGS matrix occurs in the hypothesis. -/
def HasRadialSecantBounds {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n))
    (star : Vec n) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x z g h,
    x ∈ K → z ∈ K → F star + η ≤ F z → F z ≤ F x →
    HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
    0 < secantCurvature x z g h →
    (radialNumerator star z g h) ^ 2 ≤ C * secantCurvature x z g h

theorem supportingError_nonneg {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x g : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) (z : Vec n) :
    0 ≤ supportingError F x g z := by
  have := convex_supporting_inequality hF hg z
  unfold supportingError
  linarith

theorem optimizerIntercept_eq_error {n : ℕ} (F : Vec n → ℝ) (star x g : Vec n) :
    optimizerIntercept F star x g = supportingError F x g star := by
  unfold optimizerIntercept supportingError dot
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

theorem secantCurvature_eq_errors {n : ℕ} (F : Vec n → ℝ) (x z g h : Vec n) :
    secantCurvature x z g h = supportingError F x g z + supportingError F z h x := by
  unfold secantCurvature supportingError dot
  simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

theorem radialNumerator_eq_error_intercepts {n : ℕ}
    (F : Vec n → ℝ) (star x z g h : Vec n) :
    radialNumerator star z g h = supportingError F x g z +
      optimizerIntercept F star z h - optimizerIntercept F star x g := by
  unfold radialNumerator supportingError optimizerIntercept dot
  simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Bounded curvature converts RS into the supporting-intercept estimate with
exact source constant 2C + 2Tmax. -/
theorem intercept_bound_of_radial {N D T C Tmax : ℝ}
    (hD : 0 ≤ D) (hDT : D ≤ T) (hT : T ≤ Tmax) (hN : N ^ 2 ≤ C * T) :
    (N - D) ^ 2 ≤ (2 * C + 2 * Tmax) * T := by
  have hD2 : D ^ 2 ≤ Tmax * T := by
    have hT0 : 0 ≤ T := hD.trans hDT
    nlinarith [mul_le_mul hDT hDT hD hT0, mul_le_mul_of_nonneg_right hT hT0]
  nlinarith [sq_nonneg (N + D)]

/-- The converse supporting-intercept estimate has the same constant conversion. -/
theorem radial_bound_of_intercept {N D T C Tmax : ℝ}
    (hD : 0 ≤ D) (hDT : D ≤ T) (hT : T ≤ Tmax) (hN : (N - D) ^ 2 ≤ C * T) :
    N ^ 2 ≤ (2 * C + 2 * Tmax) * T := by
  have hD2 : D ^ 2 ≤ Tmax * T := by
    have hT0 : 0 ≤ T := hD.trans hDT
    nlinarith [mul_le_mul hDT hDT hD hT0, mul_le_mul_of_nonneg_right hT hT0]
  nlinarith [sq_nonneg (N - 2 * D)]

end RadialCertificate
end BfgsVerification
