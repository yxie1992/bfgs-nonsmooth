import BfgsVerification.TransportedCertificateConvergence
import BfgsVerification.HomogeneousConsequences
import BfgsVerification.ScalarConvergence
import BfgsVerification.RadialConvergence

/-! Exact objective-level targets for the first entire-report execution tranche.
These targets contain no assumed scalar hierarchy, matrix/iterate convergence,
or undisclosed objective regularity. The report remains incomplete beyond them. -/
noncomputable section
open scoped Topology
open Set Filter

namespace BfgsVerification

/-- Source T primary theorem, with actual Euclidean solution-set distance. -/
def TransportedCertificateTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (b : ℝ),
    IsCompact {x : Vec n | F x ≤ b} → ∀ star : Vec n,
    (∀ x, F star ≤ F x) → F (R.x 0) ≤ b →
    TransportedCertificate.HasBandCertificates F {x | F x ≤ b} (F star) R.c₁ R.c₂ →
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ x, F x = F star → x = star) → Tendsto R.x atTop (𝓝 star))

/-- Source H.A in arbitrary finite dimension, without compactness. -/
def HomogeneousDichotomyTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F),
    Homogeneous.PositiveDegreeOne F →
    Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∨
      Tendsto (fun k => F (R.x k)) atTop atBot

/-- Source G scalar convergence for arbitrary positive metric sequences. -/
def ScalarMetricConvergenceTarget : Prop :=
  ∀ {f : ℝ → ℝ} (R : ScalarMetricRun f), IsCompact R.initialSublevel →
    ∀ star : ℝ, (∀ x, f star ≤ f x) →
    (∀ x, f x = f star → x = star) →
    Tendsto (fun k => f (R.x k)) atTop (𝓝 (f star)) ∧ Tendsto R.x atTop (𝓝 star)

/-- The same source conclusion for actual unmodified dimension-one BFGS. -/
def ScalarBFGSConvergenceTarget : Prop :=
  ∀ {F : Vec 1 → ℝ} (R : AdmissibleBFGSRun 1 F), IsCompact R.initialSublevel →
    ∀ star : Vec 1, (∀ x, F star ≤ F x) →
    (∀ x, F x = F star → x = star) →
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star)

/-- The radial sufficient condition underlying Module R's applications. -/
def RadialCertificateConvergenceTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (b : ℝ),
    IsCompact {x : Vec n | F x ≤ b} → ∀ star : Vec n,
    (∀ x, F star ≤ F x) → F (R.x 0) ≤ b →
    RadialCertificate.HasRadialSecantBounds F {x | F x ≤ b} star →
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ x, F x = F star → x = star) → Tendsto R.x atTop (𝓝 star))

end BfgsVerification
