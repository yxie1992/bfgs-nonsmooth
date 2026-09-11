import BfgsVerification.ParabolicFamily
import BfgsVerification.QuadraticGaugeAlgebra

/-! Module Q's exact pair identities and zero-safe secant estimate for the
original finite maximum, before any envelope reduction or calibration. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace BfgsVerification
namespace Parabolic
namespace Family
open TransportedCertificate
variable {m : ℕ} (P : Family m)

def horizontalStep (x z : Vec 2) : ℝ := z 0 - x 0
def normalStep (x z : Vec 2) : ℝ := z 1 - x 1
def deficit (i : Fin m) (z : Vec 2) : ℝ := P.objective z - P.branch i z
def stepDeterminant (x z : Vec 2) : ℝ := 2 * x 1 * horizontalStep x z - x 0 * normalStep x z

theorem deficit_nonneg (i : Fin m) (z : Vec 2) : 0 ≤ P.deficit i z :=
  sub_nonneg.mpr (P.branch_le i z)

theorem decrease_gap_identity {i : Fin m} {x z : Vec 2} (hi : P.Active i x) :
    pairDecrease x z (P.branchGradient i x) - (P.objective x - P.objective z) =
      P.a i * (horizontalStep x z)^2 + P.deficit i z := by
  dsimp only [Active] at hi
  simp only [deficit, hi, branch, pairDecrease, pairStep, branchGradient, dot,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Pi.sub_apply, horizontalStep]
  ring

theorem curvature_identity {i j : Fin m} {x z : Vec 2}
    (hi : P.Active i x) (hj : P.Active j z) :
    pairCurvature x z (P.branchGradient i x) (P.branchGradient j z) =
      (P.a i + P.a j) * (horizontalStep x z)^2 + P.deficit i z + P.deficit j x := by
  dsimp only [Active] at hi hj
  simp only [deficit, hi, hj, branch, pairCurvature, pairStep, branchGradient, dot,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Pi.sub_apply, horizontalStep]
  ring

theorem visibility_identity {i : Fin m} {x : Vec 2} (hi : P.Active i x) :
    dot (P.branchGradient i x) (radialDirection x) = 2 * P.objective x := by
  dsimp only [Active] at hi
  simp only [hi, branch, branchGradient, radialDirection, dot, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

theorem secant_radial_identity {i j : Fin m} {x z : Vec 2} (hj : P.Active j z) :
    dot (P.branchGradient j z - P.branchGradient i x) (radialDirection z) =
      2 * P.a i * horizontalStep x z * z 0 + 2 * P.deficit i z := by
  dsimp only [Active] at hj
  simp only [deficit, hj, branch, branchGradient, radialDirection, dot, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply,
    horizontalStep]
  ring

/-- Source Q's weighted bound, retaining either zero horizontal step or zero
branch deficit; the only denominator is a_i+a_j>0. -/
theorem secant_square_bound {i j : Fin m} {x z : Vec 2}
    (hi : P.Active i x) (hj : P.Active j z) :
    (dot (P.branchGradient j z - P.branchGradient i x) (radialDirection z))^2 ≤
      pairCurvature x z (P.branchGradient i x) (P.branchGradient j z) *
        (4 * (P.a i)^2 / (P.a i + P.a j) * (z 0)^2 + 4 * P.deficit i z) := by
  have ha : 0 < P.a i + P.a j := add_pos (P.a_pos i) (P.a_pos j)
  have hU : 0 ≤ 4 * (P.a i)^2 / (P.a i + P.a j) * (z 0)^2 := by positivity
  have he : 0 ≤ P.deficit i z := P.deficit_nonneg i z
  have heb : 0 ≤ P.deficit j x := P.deficit_nonneg j x
  have hw := QuadraticGauge.weighted_square_bound
    (a := (P.a i + P.a j) * (horizontalStep x z)^2) (b := P.deficit i z)
    (ξ := 2 * P.a i * horizontalStep x z * z 0) (ζ := 2 * P.deficit i z)
    (U := 4 * (P.a i)^2 / (P.a i + P.a j) * (z 0)^2) (W := 4 * P.deficit i z)
    (mul_nonneg ha.le (sq_nonneg _)) he hU (by positivity)
    (by apply le_of_eq; field_simp; ring) (by nlinarith)
  rw [P.secant_radial_identity hj, P.curvature_identity hi hj]
  exact hw.trans (mul_le_mul_of_nonneg_right (by linarith) (add_nonneg hU (by positivity)))

theorem secant_quotient_bound {i j : Fin m} {x z : Vec 2}
    (hi : P.Active i x) (hj : P.Active j z)
    (ht : 0 < pairCurvature x z (P.branchGradient i x) (P.branchGradient j z)) :
    (dot (P.branchGradient j z - P.branchGradient i x) (radialDirection z))^2 /
      pairCurvature x z (P.branchGradient i x) (P.branchGradient j z) ≤
        4 * (P.a i)^2 / (P.a i + P.a j) * (z 0)^2 + 4 * P.deficit i z := by
  apply (div_le_iff₀ ht).mpr
  simpa only [mul_comm] using P.secant_square_bound hi hj

theorem eligible_deficit_le {i : Fin m} {x z g h : Vec 2} {c₁ c₂ : ℝ}
    (hc₁ : 0 ≤ c₁) (hi : P.Active i x) (hp : EligiblePair P.objective c₁ c₂ x z g h) :
    P.deficit i z ≤ pairDecrease x z g := by
  have hg := P.active_eq_gradient hi hp.gradient_x
  have hid := P.decrease_gap_identity (z := z) hi
  rw [hg] at hid
  have hd : 0 ≤ P.objective x - P.objective z :=
    (mul_nonneg hc₁ hp.decrease_pos.le).trans hp.armijo
  have hq := mul_nonneg (P.a_pos i).le (sq_nonneg (horizontalStep x z))
  linarith

theorem eligible_horizontal_sq_le {i : Fin m} {x z g h : Vec 2} {c₁ c₂ : ℝ}
    (hc₁ : 0 ≤ c₁) (hi : P.Active i x) (hp : EligiblePair P.objective c₁ c₂ x z g h) :
    (horizontalStep x z)^2 ≤ pairDecrease x z g / P.minQuadratic := by
  have hg := P.active_eq_gradient hi hp.gradient_x
  have hid := P.decrease_gap_identity (z := z) hi
  rw [hg] at hid
  have hd : 0 ≤ P.objective x - P.objective z :=
    (mul_nonneg hc₁ hp.decrease_pos.le).trans hp.armijo
  have he := P.deficit_nonneg i z
  have hq := mul_le_mul_of_nonneg_right (P.minQuadratic_le i) (sq_nonneg (horizontalStep x z))
  apply (le_div_iff₀ P.minQuadratic_pos).mpr
  nlinarith

/-- The zero-normal-slope-safe determinant identity Q.14. -/
theorem slope_determinant_identity {i : Fin m} {x z : Vec 2} (hi : P.Active i x) :
    P.b i * stepDeterminant x z =
      2 * P.objective x * horizontalStep x z + x 0 * pairDecrease x z (P.branchGradient i x) := by
  dsimp only [Active] at hi
  simp only [hi, branch, pairDecrease, pairStep, branchGradient, dot, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply,
    stepDeterminant, horizontalStep, normalStep]
  ring

theorem old_radial_identity {i j : Fin m} {x z : Vec 2} (hj : P.Active j z) :
    dot (P.branchGradient j z - P.branchGradient i x) (radialDirection x) =
      -2 * pairCurvature x z (P.branchGradient i x) (P.branchGradient j z) +
      (2 * P.a i * horizontalStep x z * z 0 + 2 * P.deficit i z +
        (P.branchGradient j z 0 - P.branchGradient i x 0) * horizontalStep x z) := by
  dsimp only [Active] at hj
  simp only [deficit, hj, branch, pairCurvature, pairStep, branchGradient, radialDirection,
    dot, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Pi.sub_apply, horizontalStep]
  ring

end Family
end Parabolic
end BfgsVerification
