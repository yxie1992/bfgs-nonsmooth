import BfgsVerification.ParabolicPairs

/-! Exact planar algebra and quantitative scalar absorption behind Q.13.
All nonzero denominator conclusions below are derived from inequalities. -/
noncomputable section
open scoped BigOperators
open Matrix
namespace BfgsVerification
namespace Parabolic

def determinant (v w : Vec 2) : ℝ := v 0 * w 1 - v 1 * w 0

theorem determinant_dot_identity (g y s r : Vec 2) :
    determinant g y * determinant s r = dot g s * dot y r - dot g r * dot y s := by
  simp only [determinant, dot, Fin.sum_univ_two]
  ring

theorem abs_coordinate_of_sqNorm_le {n : ℕ} {v : Vec n} {G : ℝ}
    (hG : 0 ≤ G) (hv : sqNorm v ≤ G^2) (i : Fin n) : |v i| ≤ G := by
  have hi : (v i)^2 ≤ sqNorm v :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  apply (sq_le_sq₀ (abs_nonneg _) hG).mp
  simpa only [sq_abs] using hi.trans hv

theorem determinant_gradient_bound {g h : Vec 2} {G : ℝ}
    (hG : 0 ≤ G) (hg : ∀ i, |g i| ≤ G) (hh : ∀ i, |h i| ≤ G) :
    |determinant g (h-g)| ≤ 4 * G^2 := by
  have hy (i : Fin 2) : |h i-g i| ≤ 2*G :=
    (abs_sub _ _).trans (by linarith [hg i, hh i])
  calc
    |determinant g (h-g)| ≤ |g 0 * (h 1-g 1)| + |g 1 * (h 0-g 0)| := abs_sub _ _
    _ = |g 0| * |h 1-g 1| + |g 1| * |h 0-g 0| := by rw [abs_mul, abs_mul]
    _ ≤ G * (2*G) + G * (2*G) := add_le_add
      (mul_le_mul (hg 0) (hy 1) (abs_nonneg _) hG)
      (mul_le_mul (hg 1) (hy 0) (abs_nonneg _) hG)
    _ = 4*G^2 := by ring

/-- Quantitative absorption including the exact small-decrease threshold. -/
theorem denominator_absorption {η κ E K a d t F D h : ℝ}
    (hη : 0 < η) (hκ : 0 < κ) (hE : 0 < E) (ha : 0 < a)
    (hd : 0 < d) (ht : κ*d ≤ t) (hF : η ≤ F)
    (hdη : d ≤ η/2)
    (hda : d ≤ a * (η*κ/(4*E))^2) (hdτ : d ≤ η*κ/(4*E))
    (hh : h^2 ≤ d/a)
    (hmain : (2*F-2*d)*t ≤ K*|D| + E*d*(|h|+d)) :
    d ≤ (2*K/(η*κ))*|D| := by
  have hτ : 0 < η*κ/(4*E) := by positivity
  have hhτ : |h| ≤ η*κ/(4*E) := by
    apply (sq_le_sq₀ (abs_nonneg _) hτ.le).mp
    rw [sq_abs]
    exact hh.trans ((div_le_iff₀ ha).mpr (by nlinarith [hda]))
  have hEbound : E*(|h|+d) ≤ η*κ/2 := by
    have hu : E*(|h|+d) ≤ E*(2*(η*κ/(4*E))) :=
      mul_le_mul_of_nonneg_left (by linarith) hE.le
    have he : E*(2*(η*κ/(4*E))) = η*κ/2 := by field_simp; ring
    rwa [he] at hu
  have ht0 : 0 ≤ t := (mul_pos hκ hd).le.trans ht
  have hleft : η*κ*d ≤ (2*F-2*d)*t := by
    calc
      η*κ*d = η*(κ*d) := by ring
      _ ≤ η*t := mul_le_mul_of_nonneg_left ht hη.le
      _ ≤ (2*F-2*d)*t := mul_le_mul_of_nonneg_right (by linarith) ht0
  have herr : E*d*(|h|+d) ≤ (η*κ/2)*d := by
    nlinarith [mul_le_mul_of_nonneg_right hEbound hd.le]
  have hmul : d*(η*κ) ≤ 2*K*|D| := by linarith
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (mul_pos hη hκ)).mpr hmul

/-- A separate absolute-value extraction never divides by the normal slope. -/
theorem horizontal_from_determinant {η F b D h u d G R C : ℝ}
    (hη : 0 < η) (hF : η ≤ F) (hd : 0 ≤ d) (hb : |b| ≤ G) (hu : |u| ≤ R)
    (hR : 0 ≤ R) (hD : d ≤ C*|D|) (hid : b*D = 2*F*h + u*d) :
    |h| ≤ ((G+R*C)/(2*η))*|D| := by
  have hF0 : 0 ≤ F := hη.le.trans hF
  have h1 : |2*F*h| ≤ |b*D| + |u*d| := by
    rw [show 2*F*h = b*D-u*d by linarith]
    exact abs_sub _ _
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg hF0, abs_of_nonneg hd] at h1
  have h2 : |b| *|D| + |u| *d ≤ G*|D| + R*(C*|D|) := add_le_add
    (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
    ((mul_le_mul_of_nonneg_right hu hd).trans (mul_le_mul_of_nonneg_left hD hR))
  have h3 : 2*η*|h| ≤ (G+R*C)*|D| := by
    have hlow := mul_le_mul_of_nonneg_right hF (abs_nonneg h)
    nlinarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 2*η)).mpr
  nlinarith

namespace Family
variable {m : ℕ} (P : Family m)
open TransportedCertificate

theorem determinant_identity {i j : Fin m} {x z : Vec 2} (hi : P.Active i x) :
    determinant (P.branchGradient i x) (P.branchGradient j z-P.branchGradient i x) *
      stepDeterminant x z =
      -pairDecrease x z (P.branchGradient i x) *
        dot (P.branchGradient j z-P.branchGradient i x) (radialDirection x) -
      2 * P.objective x * pairCurvature x z (P.branchGradient i x) (P.branchGradient j z) := by
  have h := determinant_dot_identity (P.branchGradient i x)
    (P.branchGradient j z-P.branchGradient i x) (pairStep x z) (radialDirection x)
  have he : determinant (pairStep x z) (radialDirection x) = stepDeterminant x z := by
    simp only [determinant, pairStep, radialDirection, stepDeterminant, horizontalStep, normalStep,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply]
    ring
  rw [he, P.visibility_identity hi] at h
  simpa only [pairDecrease, pairCurvature, neg_neg] using h

end Family
end Parabolic
end BfgsVerification
