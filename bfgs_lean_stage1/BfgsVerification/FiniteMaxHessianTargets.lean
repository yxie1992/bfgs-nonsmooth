import BfgsVerification.FiniteMaxHessianBound
import BfgsVerification.FiniteMaxTaylorBound

/-! Exact contracts for the generic finite-maximum calculus used in Module L.
These establish the generic calculus only; literal L branch constants and the
actual BFGS counterexample remain separate instantiations. -/
noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification

/-- The local Taylor model of an actual finite maximum, at an actual
 differentiable point, with the branch Euclidean constant unchanged. -/
def FiniteMaxTaylorTarget : Prop :=
  ∀ {n m : ℕ} {F : Vec n → ℝ} {f : Fin m → Vec n → ℝ}
    {g : Fin m → Vec n → Vec n} {x a : Vec n} {L : ℝ},
    0 ≤ L → ConvexSubdifferential.LocalFiniteMax F f x →
    HasFDerivAt F (gradientFunctional a) x →
    (∀ i z, HasFDerivAt (f i) (gradientFunctional (g i z)) z) →
    (∀ i z w, sqNorm (g i z - g i w) ≤ L ^ 2 * sqNorm (z - w)) →
    ∀ᶠ z in 𝓝 x, F z ≤ F x + dot a (z - x) + (L / 2) * sqNorm (z - x)

theorem finiteMaxTaylor : FiniteMaxTaylorTarget := by
  intro n m F f g x a L hL hrep hF hg hlip
  exact FiniteMaxHessian.finiteMax_local_upper_taylor hL hrep hF hg hlip

/-- Actual second Frechet matrix bounds. The first derivative exists locally;
 the derivative of that field need only exist at the displayed point. -/
def FiniteMaxActualHessianTarget : Prop :=
  ∀ {n m : ℕ} {F : Vec n → ℝ} {f : Fin m → Vec n → ℝ}
    {g : Fin m → Vec n → Vec n} {x : Vec n} {μ L : ℝ},
    0 ≤ L → ConvexOn ℝ univ F →
    FixedNormal.EuclideanStrongConvexOn univ μ F →
    ConvexSubdifferential.LocalFiniteMax F f x →
    (∀ i z, HasFDerivAt (f i) (gradientFunctional (g i z)) z) →
    (∀ i z w, sqNorm (g i z - g i w) ≤ L ^ 2 * sqNorm (z - w)) →
    (∀ᶠ z in 𝓝 x, DifferentiableAt ℝ F z) →
    DifferentiableAt ℝ (fderiv ℝ F) x →
    (RadialHessian.matrix F x).IsSymm ∧
      ∀ v, μ * sqNorm v ≤ dot v ((RadialHessian.matrix F x).mulVec v) ∧
        dot v ((RadialHessian.matrix F x).mulVec v) ≤ L * sqNorm v

theorem finiteMaxActualHessian : FiniteMaxActualHessianTarget := by
  intro n m F f g x μ L hL hF hstrong hrep hg hlip hfirst hsecond
  exact FiniteMaxHessian.finiteMax_actual_hessian_bounds hL hF hstrong hrep hg hlip hfirst hsecond

end BfgsVerification
