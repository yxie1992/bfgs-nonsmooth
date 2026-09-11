import BfgsVerification.FiniteMaxGradientBound
import BfgsVerification.ActualSecondDerivativeBounds

/-! The actual Hessian of a finite maximum is bounded by the original Euclidean
branch smoothness constant wherever the objective has two actual derivatives.
The first derivative must exist near the point; only its derivative at the
point is used, with no assumed continuous second derivative. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification
namespace FiniteMaxHessian
open ConvexSubdifferential

/-- Sharp upper quadratic-form bound from actual branch gradients. -/
theorem finiteMax_second_upper {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {g : Fin m → Vec n → Vec n}
    {D : Vec n → (Vec n →L[ℝ] ℝ)}
    {B : Vec n →L[ℝ] Vec n →L[ℝ] ℝ} {x : Vec n} {L : ℝ}
    (hL : 0 ≤ L) (hrep : LocalFiniteMax F f x)
    (hg : ∀ i z, HasFDerivAt (f i) (gradientFunctional (g i z)) z)
    (hlip : ∀ i z w, sqNorm (g i z - g i w) ≤ L ^ 2 * sqNorm (z - w))
    (hfirst : ∀ᶠ z in 𝓝 x, HasFDerivAt F (D z) z)
    (hsecond : HasFDerivAt D B x) (v : Vec n) : B v v ≤ L * sqNorm v := by
  let a : Vec n → Vec n := fun z i => D z (Pi.single i 1)
  have ha (z : Vec n) : gradientFunctional (a z) = D z :=
    gradientFunctional_coordinates (D z)
  have hx0 := mem_of_mem_nhds hfirst
  have hx : HasFDerivAt F (gradientFunctional (a x)) x := by
    rw [ha]
    exact hx0
  have hb := gradient_increment_bound hrep hx hg hlip
  apply second_upper_of_increment hsecond _ v
  filter_upwards [hb, hfirst] with z hz hd
  have hgrad : HasFDerivAt F (gradientFunctional (a z)) z := by rwa [ha]
  have he : (D z - D x) (z - x) = dot (a z - a x) (z - x) := by
    rw [← ha z, ← ha x]
    simp only [ContinuousLinearMap.sub_apply, gradientFunctional_apply]
    exact (sub_dotProduct _ _ _).symm
  rw [he]
  exact (le_abs_self _).trans (abs_dot_le_relative hL (hz (a z) hgrad))

/-- Strong convexity supplies the lower bound for the same actual Hessian. -/
theorem stronglyConvex_second_lower {n : ℕ} {F : Vec n → ℝ}
    {D : Vec n → (Vec n →L[ℝ] ℝ)}
    {B : Vec n →L[ℝ] Vec n →L[ℝ] ℝ} {x : Vec n} {μ : ℝ}
    (hF : ConvexOn ℝ univ F)
    (hstrong : FixedNormal.EuclideanStrongConvexOn univ μ F)
    (hfirst : ∀ᶠ z in 𝓝 x, HasFDerivAt F (D z) z)
    (hsecond : HasFDerivAt D B x) (v : Vec n) : μ * sqNorm v ≤ B v v := by
  let a : Vec n → Vec n := fun z i => D z (Pi.single i 1)
  have ha (z : Vec n) : gradientFunctional (a z) = D z :=
    gradientFunctional_coordinates (D z)
  have hx0 := mem_of_mem_nhds hfirst
  have hx : HasFDerivAt F (gradientFunctional (a x)) x := by
    rw [ha]
    exact hx0
  apply second_lower_of_increment hsecond _ v
  filter_upwards [hfirst] with z hz
  have hgrad : HasFDerivAt F (gradientFunctional (a z)) z := by rwa [ha]
  have he : (D z - D x) (z - x) = dot (a z - a x) (z - x) := by
    rw [← ha z, ← ha x]
    simp only [ContinuousLinearMap.sub_apply, gradientFunctional_apply]
    exact (sub_dotProduct _ _ _).symm
  rw [he]
  exact FixedNormal.strong_support_monotonicity hstrong (mem_univ _) (mem_univ _)
    (convex_supporting_inequality hF hx) (convex_supporting_inequality hF hgrad)

/-- The statement in terms of the literal matrix of the actual second Frechet
 derivative, including symmetry. This is not a global smoothness assumption on
 the nonsmooth maximum. -/
theorem finiteMax_actual_hessian_bounds {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {g : Fin m → Vec n → Vec n}
    {x : Vec n} {μ L : ℝ} (hL : 0 ≤ L)
    (hF : ConvexOn ℝ univ F)
    (hstrong : FixedNormal.EuclideanStrongConvexOn univ μ F)
    (hrep : LocalFiniteMax F f x)
    (hg : ∀ i z, HasFDerivAt (f i) (gradientFunctional (g i z)) z)
    (hlip : ∀ i z w, sqNorm (g i z - g i w) ≤ L ^ 2 * sqNorm (z - w))
    (hfirst : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ F z)
    (hsecond : DifferentiableAt ℝ (fderiv ℝ F) x) :
    (RadialHessian.matrix F x).IsSymm ∧
      ∀ v, μ * sqNorm v ≤ dot v ((RadialHessian.matrix F x).mulVec v) ∧
        dot v ((RadialHessian.matrix F x).mulVec v) ≤ L * sqNorm v := by
  have hd := hfirst.mono fun z hz => hz.hasFDerivAt
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    exact second_symmetric hd hsecond.hasFDerivAt _ _
  · rw [RadialHessian.matrix, RadialHessian.bilinearMatrix_quadratic]
    exact ⟨stronglyConvex_second_lower hF hstrong hd hsecond.hasFDerivAt v,
      finiteMax_second_upper hL hrep hg hlip hd hsecond.hasFDerivAt v⟩

end FiniteMaxHessian
end BfgsVerification
