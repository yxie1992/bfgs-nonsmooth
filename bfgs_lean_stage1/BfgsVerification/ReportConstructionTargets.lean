import BfgsVerification.AlgebraicSeedCoercive
import BfgsVerification.DScalarTarget
import BfgsVerification.CenteredSpectral
import BfgsVerification.RadialSingularCurvature
import BfgsVerification.PlanarRunTransport

/-! Reviewed exact targets for the ninth report construction tranche. -/
noncomputable section
open scoped Topology BigOperators
open Set Filter MeasureTheory
namespace BfgsVerification
open SeedOrbit DScalar DScalarGeometric ScalarCounterexamples

/-- D’s actual coercive deterministic seed, including all infinite search histories. -/
def CoerciveSeedFailureTarget : Prop :=
  ∀ (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (hc₂ : c₂ < 1),
    let R := coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂
    (∀ a : ℝ, IsCompact {x | coerciveObjective x ≤ a}) ∧
      coerciveObjective coerciveOptimizer = -1 ∧
      (∀ x, -1 ≤ coerciveObjective x) ∧
      (∀ x, coerciveObjective x = -1 → x=coerciveOptimizer) ∧
      R.H 0=1 ∧ Tendsto R.x atTop (𝓝 0) ∧
      Tendsto (fun k => coerciveObjective (R.x k)) atTop (𝓝 0) ∧
      (∀ k, 0 < coerciveObjective (R.x k)) ∧
      (∀ k, coerciveObjective (R.x (k+1)) < coerciveObjective (R.x k)) ∧
      (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential coerciveObjective 0 ∧
      (∀ k, DeterministicLineSearch.fromMetric coerciveObjective (R.x k) (R.H k) c₁ c₂ 5 =
        (some (R.α k),trialHistory (phase k)))

/-- Literal global scalar construction; no assumed interpolation or regularity. -/
def DScalarFunctionTarget : Prop :=
  ∀ (b : ℝ), 2 ≤ b → b ≤ 34 →
    ContDiff ℝ 2 (phi b) ∧ ConvexOn ℝ univ (phi b) ∧
    (∀ x, 0 ≤ phi b x) ∧ (∀ x, phi b x=0 ↔ x=0) ∧
    Tendsto (phi b) (cocompact ℝ) atTop ∧ (∀ a, IsCompact {x : ℝ | phi b x ≤ a}) ∧
    (∀ x, HasDerivAt (phi b) (phiFirst b x) x) ∧
    (∀ x, HasDerivAt (phiFirst b) (phiSecond b x) x) ∧
    (∀ x, 0 ≤ deriv (deriv (phi b)) x ∧ deriv (deriv (phi b)) x ≤ max 6 (102/b)) ∧
    LipschitzWith ⟨max 6 (139264/(5*b^2)), le_trans (by norm_num) (le_max_left _ _)⟩
      (deriv (deriv (phi b))) ∧
    (∀ m, phi b (b*scale m)=(scale m)^3 ∧ HasDerivAt (phi b) ((scale m)^2) (b*scale m) ∧
      HasDerivAt (deriv (phi b)) 0 (b*scale m)) ∧
    (∀ m h, |h| ≤ scale m/2 → phi b (b*scale m+h)=(scale m)^3+(scale m)^2*h) ∧
    (∀ x, x ≤ -1 → phi b x=1-3*(x+1)+3*(x+1)^2) ∧
    (∀ x, -1 ≤ x → x ≤ 0 → phi b x= -x^3) ∧
    (∀ x, b ≤ x → phi b x=1+x-b) ∧
    (∀ m x, b*theta*scale m ≤ x → x ≤ b*scale m →
      phi b x=(theta*scale m)^3+b*(scale m)^3*(1-theta)*
        (theta^2*coordinate b (scale m) x+
          (1-theta^2)*DScalarRamp.primitive b (coordinate b (scale m) x)))

/-- The actual spectral norm is identified with the Euclidean operator norm. -/
def CenteredSpectralConvergenceTarget : Prop :=
  ∀ m n : ℕ,
    (∀ x : Vec (m*n), CenteredSpectral.objective x =
      ‖(Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) (CenteredSpectral.matrix x)‖) ∧
    (∀ R : AdmissibleBFGSRun (m*n) (CenteredSpectral.objective (m := m) (n := n)),
      Tendsto (fun k => CenteredSpectral.objective (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0))

/-- An a.e. classical Hessian bound does not imply the full radial-secant condition. -/
def SingularCurvatureCounterexampleTarget : Prop :=
    StrongConvexOn univ 1 shiftedAbs ∧
    (∀ x, shiftedAbs (-1) ≤ shiftedAbs x) ∧
    (∀ x, shiftedAbs x=shiftedAbs (-1) → x=(-1)) ∧
    IsCompact {x : Vec 1 | shiftedObjective x ≤ 3} ∧
    (∀ᵐ x : ℝ ∂volume, shiftedAbs x ≤ 3 →
      0 ≤ (x+1)^2*deriv (deriv shiftedAbs) x ∧
      (x+1)^2*deriv (deriv shiftedAbs) x ≤ 3) ∧
    ¬ RadialCertificate.HasRadialSecantBounds shiftedObjective {x | shiftedObjective x ≤ 3}
      (OneDimensional.embed (-1))

end BfgsVerification
