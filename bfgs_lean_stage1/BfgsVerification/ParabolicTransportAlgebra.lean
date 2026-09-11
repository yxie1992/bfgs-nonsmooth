import BfgsVerification.ParabolicUniformSecant
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Exact Q.15 transport algebra; all denominators are explicit here and are
supplied by the already proved positive-band denominator theorem. -/
noncomputable section
open scoped BigOperators
open Matrix
namespace BfgsVerification
namespace Parabolic
namespace Family
open TransportedCertificate
variable {m : ℕ} (P : Family m)

def quotientMultiplier (x z : Vec 2) : ℝ :=
  1 + horizontalStep x z * normalStep x z / stepDeterminant x z

def stepMultiplier (x z : Vec 2) : ℝ :=
  (2*x 1*horizontalStep x z-2*x 0*normalStep x z)/stepDeterminant x z

theorem radial_direction_transport {x z : Vec 2} (hD : stepDeterminant x z ≠ 0) :
    radialDirection z = quotientMultiplier x z • radialDirection x + stepMultiplier x z • pairStep x z := by
  ext i
  fin_cases i <;> simp only [radialDirection, quotientMultiplier, stepMultiplier, pairStep,
    Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  all_goals
    field_simp
    simp only [stepDeterminant, horizontalStep, normalStep]
    ring

theorem quotient_cancellation {i : Fin m} {x z : Vec 2} (hi : P.Active i x)
    (hF : P.objective x ≠ 0) (hD : stepDeterminant x z ≠ 0) :
    quotientMultiplier x z - 1 + (P.a i*x 0/P.objective x)*horizontalStep x z =
      -x 1*horizontalStep x z*pairDecrease x z (P.branchGradient i x)/(P.objective x*stepDeterminant x z) := by
  unfold quotientMultiplier
  field_simp
  dsimp only [Active] at hi
  rw [hi]
  simp only [branch, stepDeterminant, horizontalStep, normalStep, pairDecrease,
    pairStep, branchGradient, dot, Fin.sum_univ_two, Pi.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- The old-branch exponent increment has an exact positive remainder,
so no multivariable Taylor approximation is assumed. -/
theorem exponent_increment {i : Fin m} {x z : Vec 2}
    (hx : P.objective x ≠ 0) (hz : P.objective z ≠ 0) :
    P.a i*(z 0)^2/(2*P.objective z)-P.a i*(x 0)^2/(2*P.objective x) -
        (P.a i*x 0/P.objective x)*horizontalStep x z =
      P.a i*(horizontalStep x z)^2/(2*P.objective x) +
        P.a i*(z 0)^2*(P.objective x-P.objective z)/(2*P.objective x*P.objective z) := by
  unfold horizontalStep
  field_simp
  ring

end Family

/-- An explicit uniform quadratic logarithm remainder near one. -/
theorem log_remainder_bound {r : ℝ} (hr : |r-1| ≤ 1/2) :
    |Real.log r-(r-1)| ≤ 2*(r-1)^2 := by
  have hs : |1-r| < 1 := by rw [abs_sub_comm]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hs 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_one, div_one,
    show (1 : ℕ)+1 = 2 by rfl, show 1-(1-r)=r by ring] at h
  have hden : 0 < 1-|1-r| := by linarith
  have hb : |1-r|^2/(1-|1-r|) ≤ 2*(r-1)^2 := by
    apply (div_le_iff₀ hden).mpr
    rw [abs_sub_comm, sq_abs]
    nlinarith [mul_nonneg (sq_nonneg (r-1)) (show 0 ≤ 1/2-|r-1| by linarith)]
  convert h.trans hb using 1
  congr 1
  ring

end Parabolic
end BfgsVerification
