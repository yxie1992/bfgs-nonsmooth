import BfgsVerification.RadialHessian
import BfgsVerification.FixedNormalStrongConvex
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Bounds for an actual derivative of a derivative from local quadratic
increment estimates. No continuity of second derivatives is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification
namespace FiniteMaxHessian

/-- An upper increment bound passes to the actual second derivative. -/
theorem second_upper_of_increment {n : ℕ}
    {D : Vec n → (Vec n →L[ℝ] ℝ)}
    {B : Vec n →L[ℝ] Vec n →L[ℝ] ℝ} {x : Vec n} {C : ℝ}
    (hD : HasFDerivAt D B x)
    (hbound : ∀ᶠ z in 𝓝 x, (D z - D x) (z - x) ≤ C * sqNorm (z - x))
    (v : Vec n) : B v v ≤ C * sqNorm v := by
  have hp := RadialHessian.ray_hasDerivAt x v (0 : ℝ)
  have hd := hD.comp_hasDerivAt_of_eq 0 hp (by simp [RadialHessian.ray])
  have hv := hd.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hlim : Tendsto (fun t : ℝ =>
      ((D (RadialHessian.ray x v t)) v - (D x) v) / t)
      (𝓝[>] 0) (𝓝 (B v v)) := by
    simpa [RadialHessian.ray, div_eq_mul_inv, mul_comm] using hv.tendsto_slope_zero_right
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (D (RadialHessian.ray x v t) - D x) (RadialHessian.ray x v t - x) ≤
      C * sqNorm (RadialHessian.ray x v t - x) :=
    (hp.continuousAt.eventually (by simpa only [RadialHessian.ray, zero_smul, add_zero] using hbound)).filter_mono
      nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [hb, self_mem_nhdsWithin] with t ht ht0
  have htpos : 0 < t := ht0
  have he : RadialHessian.ray x v t - x = t • v := by simp [RadialHessian.ray]
  rw [he, map_smul, smul_eq_mul, RadialPower.sqNorm_smul] at ht
  simp only [ContinuousLinearMap.sub_apply] at ht
  apply (div_le_iff₀ htpos).mpr
  nlinarith

/-- The matching lower increment estimate. -/
theorem second_lower_of_increment {n : ℕ}
    {D : Vec n → (Vec n →L[ℝ] ℝ)}
    {B : Vec n →L[ℝ] Vec n →L[ℝ] ℝ} {x : Vec n} {C : ℝ}
    (hD : HasFDerivAt D B x)
    (hbound : ∀ᶠ z in 𝓝 x, C * sqNorm (z - x) ≤ (D z - D x) (z - x))
    (v : Vec n) : C * sqNorm v ≤ B v v := by
  have hn := second_upper_of_increment hD.neg (C := -C) (by
    filter_upwards [hbound] with z hz
    have he : (-D z - -D x) (z - x) = -((D z - D x) (z - x)) := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply]
      ring
    rw [he]
    linarith) v
  simp only [ContinuousLinearMap.neg_apply] at hn
  linarith

/-- A supplied derivative field with a derivative at the base is exactly the
actual second Fréchet derivative when it gives actual first derivatives nearby. -/
theorem actual_second_eq {n : ℕ} {F : Vec n → ℝ}
    {D : Vec n → (Vec n →L[ℝ] ℝ)}
    {B : Vec n →L[ℝ] Vec n →L[ℝ] ℝ} {x : Vec n}
    (hfirst : ∀ᶠ z in 𝓝 x, HasFDerivAt F (D z) z)
    (hsecond : HasFDerivAt D B x) : fderiv ℝ (fderiv ℝ F) x = B := by
  have he : fderiv ℝ F =ᶠ[𝓝 x] D := hfirst.mono fun z hz => hz.fderiv
  exact (hsecond.congr_of_eventuallyEq he).fderiv

/-- Actual second derivatives are symmetric, requiring only two derivatives at
the base in the usual neighborhood sense, not C2 regularity. -/
theorem second_symmetric {n : ℕ} {F : Vec n → ℝ}
    {D : Vec n → (Vec n →L[ℝ] ℝ)}
    {B : Vec n →L[ℝ] Vec n →L[ℝ] ℝ} {x : Vec n}
    (hfirst : ∀ᶠ z in 𝓝 x, HasFDerivAt F (D z) z)
    (hsecond : HasFDerivAt D B x) (v w : Vec n) : B v w = B w v :=
  second_derivative_symmetric_of_eventually_of_real hfirst hsecond v w

end FiniteMaxHessian
end BfgsVerification
