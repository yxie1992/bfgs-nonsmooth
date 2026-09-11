import BfgsVerification.ParabolicTransportAlgebra
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Uniform scalar estimates used to discharge the actual Q transport clause. -/
noncomputable section
namespace BfgsVerification
namespace Parabolic

/-- Cancellation plus quadratic horizontal control makes the unscaled
multiplier uniformly close to one; no division by a horizontal step occurs. -/
theorem compensation_square_bound {r α h d a A B : ℝ}
    (ha : 0 < a) (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hα : |α| ≤ A) (hh : h^2 ≤ d/a) (he : |r-1+α*h| ≤ B*d) :
    (r-1)^2 ≤ (2*A^2/a+2*B^2)*d := by
  have hαsq : α^2 ≤ A^2 := by nlinarith [sq_abs α, abs_nonneg α]
  have h1 : (α*h)^2 ≤ (A^2/a)*d := by
    calc
      (α*h)^2 = α^2*h^2 := mul_pow _ _ _
      _ ≤ A^2*h^2 := mul_le_mul_of_nonneg_right hαsq (sq_nonneg h)
      _ ≤ A^2*(d/a) := mul_le_mul_of_nonneg_left hh (sq_nonneg A)
      _ = (A^2/a)*d := by ring
  have hesq : (r-1+α*h)^2 ≤ B^2*d^2 := by
    nlinarith [sq_abs (r-1+α*h), abs_nonneg (r-1+α*h), mul_nonneg hB hd]
  have h2 : (r-1+α*h)^2 ≤ B^2*d := by
    have hb := mul_le_mul_of_nonneg_left (show d^2 ≤ d by nlinarith) (sq_nonneg B)
    exact hesq.trans hb
  have hs := sq_nonneg ((r-1+α*h)+α*h)
  have hrewrite : (2*A^2/a+2*B^2)*d = 2*((A^2/a)*d)+2*(B^2*d) := by ring
  rw [hrewrite]
  nlinarith

/-- The compensated logarithm estimate follows from the explicit quadratic
logarithm remainder and the cancellation residual. -/
theorem compensation_log_bound {r α h d K B : ℝ}
    (hd : 0 ≤ d) (hclose : |r-1| ≤ 1/2) (hsq : (r-1)^2 ≤ K*d)
    (he : |r-1+α*h| ≤ B*d) :
    |Real.log r+α*h| ≤ (2*K+B)*d := by
  have hr := log_remainder_bound hclose
  have hsum := (abs_add (Real.log r-(r-1)) (r-1+α*h)).trans (add_le_add hr he)
  have h1 : |Real.log r+α*h| ≤ 2*(r-1)^2+B*d := by
    simpa only [show Real.log r-(r-1)+(r-1+α*h) = Real.log r+α*h by ring] using hsum
  nlinarith

/-- Convexity of the actual exponential supplies an explicit finite linear
expansion budget, without a numerical estimate for exp(1). -/
theorem exp_mul_le_one_add {C d : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    Real.exp (C*d) ≤ 1+(Real.exp C-1)*d := by
  have h := convexOn_exp.2 (show (0 : ℝ) ∈ Set.univ by trivial)
    (show C ∈ Set.univ by trivial) (sub_nonneg.mpr hd1) hd (show (1-d)+d=1 by ring)
  simpa only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one,
    show 1-d+d*Real.exp C = 1+(Real.exp C-1)*d by ring, mul_comm d C] using h

theorem squared_multiplier_bound {r C d : ℝ} (hr : 0 < r) (hlog : Real.log r ≤ C*d)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    r^2 ≤ 1+(Real.exp (2*C)-1)*d := by
  calc
    r^2 = Real.exp ((2:ℝ)*Real.log r) := by rw [show (2:ℝ)*Real.log r = Real.log r+Real.log r by ring, Real.exp_add, Real.exp_log hr]; ring
    _ ≤ Real.exp ((2*C)*d) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ _ := exp_mul_le_one_add hd hd1

end Parabolic
end BfgsVerification
