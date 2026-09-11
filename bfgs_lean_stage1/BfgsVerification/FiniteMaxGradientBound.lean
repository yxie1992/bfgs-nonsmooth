import BfgsVerification.FiniteMaxLocalCorrectness
import BfgsVerification.EuclideanEstimates
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Actual finite maxima with Euclidean Lipschitz branch gradients. No convexity
of the branches or full maximum is needed for the upper estimates. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification
namespace FiniteMaxHessian
open ConvexSubdifferential

/-- Every active branch has the actual derivative of a differentiable maximum.
This follows from local contact, without convexity of either function. -/
theorem active_derivative_eq {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {x : Vec n}
    {A D : Vec n →L[ℝ] ℝ} (hrep : LocalFiniteMax F f x)
    (hF : HasFDerivAt F A x) {i : Fin m}
    (hf : HasFDerivAt (f i) D x) (hi : i ∈ activeIndices F f x) : D = A := by
  have hmin : IsLocalMin (fun z => F z - f i z) x := by
    filter_upwards [hrep] with z hz
    change F x - f i x ≤ F z - f i z
    rw [mem_activeIndices.mp hi, sub_self]
    exact sub_nonneg.mpr (hz.2 (mem_range_self i))
  have heq := hmin.hasFDerivAt_eq_zero (hF.sub hf)
  exact (sub_eq_zero.mp heq).symm

/-- Euclidean Cauchy--Schwarz with a relative squared-norm bound. -/
theorem abs_dot_le_relative {n : ℕ} {u v : Vec n} {a : ℝ}
    (ha : 0 ≤ a) (hu : sqNorm u ≤ a ^ 2 * sqNorm v) :
    |dot u v| ≤ a * sqNorm v := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg ha (sqNorm_nonneg v))).mp
  have hcs := dot_sq_le_sqNorm_mul_sqNorm u v
  have hm := mul_le_mul_of_nonneg_right hu (sqNorm_nonneg v)
  rw [sq_abs]
  nlinarith

/-- Inactive-gap reduction gives a local gradient increment bound at every
nearby point where the actual finite maximum is differentiable. -/
theorem gradient_increment_bound {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {g : Fin m → Vec n → Vec n}
    {x a : Vec n} {L : ℝ} (hrep : LocalFiniteMax F f x)
    (hF : HasFDerivAt F (gradientFunctional a) x)
    (hg : ∀ i z, HasFDerivAt (f i) (gradientFunctional (g i z)) z)
    (hlip : ∀ i z w, sqNorm (g i z - g i w) ≤ L ^ 2 * sqNorm (z - w)) :
    ∀ᶠ z in 𝓝 x, ∀ b, HasFDerivAt F (gradientFunctional b) z →
      sqNorm (b - a) ≤ L ^ 2 * sqNorm (z - x) := by
  filter_upwards [hrep.eventually,
    activeIndices_eventually_subset hF.continuousAt
      (fun i => (hg i x).continuousAt) hrep] with z hz hsub b hb
  obtain ⟨i, hi⟩ := activeIndices_nonempty hz
  have hbi := active_derivative_eq hz hb (hg i z) hi
  have hai := active_derivative_eq hrep hF (hg i x) (hsub hi)
  have hbvec : g i z = b := by
    ext j
    have he := DFunLike.congr_fun hbi (Pi.single j 1)
    simp only [gradientFunctional_apply] at he
    change dotProduct _ (Pi.single j 1) = dotProduct _ (Pi.single j 1) at he
    simpa only [dotProduct_single_one] using he
  have havec : g i x = a := by
    ext j
    have he := DFunLike.congr_fun hai (Pi.single j 1)
    simp only [gradientFunctional_apply] at he
    change dotProduct _ (Pi.single j 1) = dotProduct _ (Pi.single j 1) at he
    simpa only [dotProduct_single_one] using he
  simpa only [hbvec, havec] using hlip i z x

end FiniteMaxHessian
end BfgsVerification
