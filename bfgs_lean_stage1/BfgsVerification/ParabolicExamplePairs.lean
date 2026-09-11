import BfgsVerification.ParabolicEnvelopeScale
import BfgsVerification.RadialCertificate

/-! Q's explicit three-branch objective and actual accepted one-step witnesses.
The additional rho parameter includes the printed rho=1/2 construction. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification
namespace Parabolic
namespace Example
open TransportedCertificate

def family : Family 3 where
  a := ![1, 3, 2]
  b := ![1, 0, -1]
  a_pos := by intro i; fin_cases i <;> norm_num
  negative_slope := ⟨2, by change (-1 : ℝ) < 0; norm_num⟩
  positive_slope := ⟨0, by norm_num⟩

def objective : Vec 2 → ℝ := family.objective
def oldPoint (u ε : ℝ) : Vec 2 := ![u, 2*u^2+ε]
def newPoint (u ρ ε : ℝ) : Vec 2 := ![u, 2*u^2-ρ*ε]
def oldGradient (u : ℝ) : Vec 2 := ![2*u, 1]
def newGradient (u : ℝ) : Vec 2 := ![6*u, 0]
def initialMetric (u A ρ ε : ℝ) : Mat 2 :=
  !![A, -2*u*A; -2*u*A, 4*u^2*A+(1+ρ)*ε]

theorem objective_eq_max (x : Vec 2) :
    objective x = max (max ((x 0)^2+x 1) (3*(x 0)^2)) (2*(x 0)^2-x 1) := by
  apply le_antisymm
  · change family.objective x ≤ _
    apply Finset.sup'_le
    intro i _
    fin_cases i
    · simpa [family, Family.branch] using le_max_of_le_left (le_max_left ((x 0)^2+x 1) (3*(x 0)^2))
    · simpa [family, Family.branch] using le_max_of_le_left (le_max_right ((x 0)^2+x 1) (3*(x 0)^2))
    · simpa [family, Family.branch, sub_eq_add_neg] using le_max_right (max ((x 0)^2+x 1) (3*(x 0)^2)) (2*(x 0)^2-x 1)
  · apply max_le
    · apply max_le
      · simpa [objective, family, Family.branch] using family.branch_le 0 x
      · simpa [objective, family, Family.branch] using family.branch_le 1 x
    · simpa [objective, family, Family.branch, sub_eq_add_neg] using family.branch_le 2 x

theorem objective_upper_region {x : Vec 2} (hx : 2*(x 0)^2 < x 1) :
    objective x = family.branch 0 x := by
  rw [objective_eq_max]
  simp only [Family.branch, family, Matrix.cons_val_zero, one_mul]
  rw [max_eq_left (show 3*(x 0)^2 ≤ (x 0)^2+x 1 by linarith),
    max_eq_left (show 2*(x 0)^2-x 1 ≤ (x 0)^2+x 1 by nlinarith [sq_nonneg (x 0)])]

theorem objective_middle_region {x : Vec 2}
    (hlo : -(x 0)^2 < x 1) (hhi : x 1 < 2*(x 0)^2) :
    objective x = family.branch 1 x := by
  rw [objective_eq_max]
  simp only [Family.branch, family, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, zero_mul, add_zero]
  rw [max_eq_right (show (x 0)^2+x 1 ≤ 3*(x 0)^2 by linarith),
    max_eq_left (show 2*(x 0)^2-x 1 ≤ 3*(x 0)^2 by linarith)]

theorem upper_hasGradient {x : Vec 2} (hx : 2*(x 0)^2 < x 1) :
    HasFDerivAt objective (gradientFunctional (oldGradient (x 0))) x := by
  have he : objective =ᶠ[𝓝 x] family.branch 0 := by
    have hc : Continuous (fun w : Vec 2 => 2*(w 0)^2) := by fun_prop
    filter_upwards [(isOpen_lt hc (continuous_apply 1)).mem_nhds hx] with w hw
    exact objective_upper_region hw
  convert (family.branch_hasGradient 0 x).congr_of_eventuallyEq he using 1
  simp [Family.branchGradient, family, oldGradient]

theorem middle_hasGradient {x : Vec 2}
    (hlo : -(x 0)^2 < x 1) (hhi : x 1 < 2*(x 0)^2) :
    HasFDerivAt objective (gradientFunctional (newGradient (x 0))) x := by
  have he : objective =ᶠ[𝓝 x] family.branch 1 := by
    have hc : Continuous (fun w : Vec 2 => 2*(w 0)^2) := by fun_prop
    have hn : Continuous (fun w : Vec 2 => -(w 0)^2) := by fun_prop
    filter_upwards [(isOpen_lt hn (continuous_apply 1)).mem_nhds hlo,
      (isOpen_lt (continuous_apply 1) hc).mem_nhds hhi] with w hw hw'
    exact objective_middle_region hw hw'
  convert (family.branch_hasGradient 1 x).congr_of_eventuallyEq he using 1
  simp [Family.branchGradient, family, newGradient]
  <;> ring

theorem pair_gradients {u ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hsmall : ρ*ε < 3*u^2) :
    HasFDerivAt objective (gradientFunctional (oldGradient u)) (oldPoint u ε) ∧
    HasFDerivAt objective (gradientFunctional (newGradient u)) (newPoint u ρ ε) := by
  constructor
  · exact upper_hasGradient (x := oldPoint u ε) (by change 2*u^2 < 2*u^2+ε; linarith)
  · exact middle_hasGradient (x := newPoint u ρ ε) (by change -u^2 < 2*u^2-ρ*ε; linarith)
      (by change 2*u^2-ρ*ε < 2*u^2; nlinarith [mul_pos hρ hε])

theorem pair_values {u ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hsmall : ρ*ε < 3*u^2) :
    objective (oldPoint u ε) = 3*u^2+ε ∧ objective (newPoint u ρ ε) = 3*u^2 := by
  constructor
  · rw [objective_upper_region (by simp [oldPoint]; linarith)]
    simp [family, Family.branch, oldPoint]
    <;> ring
  · rw [objective_middle_region (by simp [newPoint]; linarith)
      (by simp [newPoint]; nlinarith [mul_pos hρ hε])]
    simp [family, Family.branch, newPoint]

theorem pair_decrease (u ρ ε : ℝ) :
    pairDecrease (oldPoint u ε) (newPoint u ρ ε) (oldGradient u) = (1+ρ)*ε := by
  simp [pairDecrease, pairStep, oldPoint, newPoint, oldGradient, dot, Fin.sum_univ_two]
  <;> ring

theorem pair_curvature (u ρ ε : ℝ) :
    pairCurvature (oldPoint u ε) (newPoint u ρ ε) (oldGradient u) (newGradient u) = (1+ρ)*ε := by
  simp [pairCurvature, pairStep, oldPoint, newPoint, oldGradient, newGradient, dot, Fin.sum_univ_two]
  <;> ring

theorem radial_numerator (u ρ ε : ℝ) :
    RadialCertificate.radialNumerator 0 (newPoint u ρ ε) (oldGradient u) (newGradient u) = 2*u^2+ρ*ε := by
  simp [RadialCertificate.radialNumerator, newPoint, oldGradient, newGradient, dot, Fin.sum_univ_two]
  <;> ring

theorem initialMetric_posDef {u A ρ ε : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hε : 0 < ε) :
    (initialMetric u A ρ ε).PosDef := by
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [initialMetric]
  · intro v hv
    have he : dotProduct (star v) ((initialMetric u A ρ ε).mulVec v) =
        A*(v 0-2*u*v 1)^2+(1+ρ)*ε*(v 1)^2 := by
      simp [initialMetric, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      <;> ring
    rw [he]
    by_cases h1 : v 1 = 0
    · have h0 : v 0 ≠ 0 := by
        intro hz
        apply hv
        ext i
        fin_cases i <;> assumption
      simp only [h1, mul_zero, sub_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero]
      exact mul_pos hA (sq_pos_of_ne_zero h0)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hA.le (sq_nonneg _))
        (mul_pos (mul_pos (by linarith) hε) (sq_pos_of_ne_zero h1))

theorem initialMetric_step (u A ρ ε : ℝ) :
    bfgsStep (initialMetric u A ρ ε) (oldGradient u) 1 = pairStep (oldPoint u ε) (newPoint u ρ ε) := by
  ext i
  fin_cases i <;> simp [bfgsStep, initialMetric, oldGradient, pairStep, oldPoint, newPoint,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem pair_eligible {u ρ ε c₁ c₂ : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hsmall : ρ*ε < 3*u^2) (hc₁ : c₁*(1+ρ) ≤ 1) (hc₂ : 0 ≤ c₂) :
    EligiblePair objective c₁ c₂ (oldPoint u ε) (newPoint u ρ ε) (oldGradient u) (newGradient u) := by
  obtain ⟨hg, hh⟩ := pair_gradients hρ hε hsmall
  obtain ⟨hx, hz⟩ := pair_values hρ hε hsmall
  refine ⟨hg, hh, ?_, ?_, ?_, ?_⟩
  · rw [pair_decrease]; positivity
  · rw [pair_decrease, hx, hz]
    nlinarith [mul_le_mul_of_nonneg_right hc₁ hε.le]
  · rw [pair_decrease, hx, hz]
    nlinarith [mul_pos hρ hε]
  · rw [pair_decrease, pair_curvature]
    nlinarith [mul_nonneg hc₂ (show 0 ≤ (1+ρ)*ε by positivity)]

end Example
end Parabolic
end BfgsVerification
