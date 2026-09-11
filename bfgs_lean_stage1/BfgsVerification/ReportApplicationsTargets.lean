import BfgsVerification.AffineCovariance
import BfgsVerification.CenteredRecentering
import BfgsVerification.QuadraticGaugeRates
import BfgsVerification.HomogeneousPlanarEscape
import BfgsVerification.PointwiseCertificateFeasibility
import BfgsVerification.ParabolicUniformSecant

/-! Explicit contracts for concrete families and certificate geometry. Module
Q's contract covers the foundation and denominator only, not its open transport
construction. Every run below is the actual unmodified full-BFGS run. -/
noncomputable section
open scoped BigOperators Topology ENNReal
open Set Filter Matrix Asymptotics
namespace BfgsVerification

def AffineCertificateCovarianceTarget : Prop :=
  ∀ {n : ℕ} (A : Mat n), A.det ≠ 0 → ∀ (b : Vec n) (F : Vec n → ℝ)
    (K : Set (Vec n)) (fstar c₁ c₂ : ℝ),
    TransportedCertificate.HasBandCertificates F K fstar c₁ c₂ ↔
      TransportedCertificate.HasBandCertificates (AffineCertificate.objective A b F)
        (AffineCertificate.forward A b '' K) fstar c₁ c₂

def CenteredSmoothConvergenceTarget : Prop :=
  ∀ {n : ℕ} {F ψ γ : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (star : Vec n),
    (∀ x, F star ≤ F x) → ∀ {U : Set (Vec n)}, IsOpen U → ConvexOn ℝ U ψ →
    CenteredSmoothSublinear.LocallyC11On U ψ → ConvexOn ℝ univ γ →
    Homogeneous.PositiveDegreeOne γ → (∀ x ∈ U, F x = ψ x + γ (x-star)) →
    IsCompact R.initialSublevel → R.initialSublevel ⊆ U →
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      ((∀ x, F x = F star → x = star) → Tendsto R.x atTop (𝓝 star))

def CenteredLocalBasinTarget : Prop :=
  ∀ {n : ℕ} {F ψ γ : Vec n → ℝ}, ConvexOn ℝ univ F →
    ∀ (star : Vec n), (∀ x, F star ≤ F x) → (∀ x, F x = F star → x = star) →
    ∀ {U : Set (Vec n)}, IsOpen U → star ∈ U → ConvexOn ℝ U ψ →
    CenteredSmoothSublinear.LocallyC11On U ψ → ConvexOn ℝ univ γ →
    Homogeneous.PositiveDegreeOne γ → (∀ x ∈ U, F x = ψ x + γ (x-star)) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star + δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
        Tendsto R.x atTop (𝓝 star)

def QuadraticGaugeRatesTarget : Prop :=
  ∀ {m p : ℕ} (Q : Mat m), Q.PosDef → ∀ (γ : Vec p → ℝ),
    ConvexOn ℝ univ γ → Homogeneous.PositiveDegreeOne γ → ∀ μ Λ : ℝ, 0 < μ →
    (∀ v, μ * ‖euclideanVector v‖ ≤ γ v) → (∀ v, γ v ≤ Λ * ‖euclideanVector v‖) →
    ∀ R : AdmissibleBFGSRun (m+p) (QuadraticGauge.objective Q γ),
      ((fun N => QuadraticGauge.objective Q γ (R.x N)) =o[atTop]
        (fun N : ℕ => Real.log (N : ℝ)/(N : ℝ))) ∧
      ((fun N => QuadraticGauge.objective Q γ (R.x N)) =O[atTop]
        (fun N : ℕ => Real.log (N : ℝ)/(N : ℝ))) ∧
      Tendsto (fun N => QuadraticGauge.objective Q γ (R.x N)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0)

def EllipsoidCertificateGeometryTarget : Prop :=
  ∀ {n : ℕ} {W Z : Mat n} (hW : W.PosSemidef) (hZ : Z.PosSemidef),
    (∀ a : Vec n, sSup (dot a '' CertificateGeometry.ellipsoid hW) = Real.sqrt (metricEnergy W a)) ∧
    (∀ P : Mat n,
      P.mulVec '' CertificateGeometry.ellipsoid hZ ⊆ P.mulVec '' CertificateGeometry.ellipsoid hW ↔
        (P * W * Pᵀ - P * Z * Pᵀ).PosSemidef)

def PointwiseCertificateCapacityTarget : Prop :=
  ∀ {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (fstar c₁ c₂ η δ : ℝ),
    c₂ < 1 → 0 < δ →
    ((∃ B : TransportedCertificate.VisibilitySecantCertificate F K fstar c₁ c₂ η, B.δ = δ) ↔
      0 < ⨅ z, PointwiseFeasibility.sourceCapacity F K fstar c₁ c₂ η δ z)

def PlanarHomogeneousEscapeTarget : Prop :=
  ∀ (A : Finset (Vec 2)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun 2 (Homogeneous.finiteMaxLinear A hA)),
    ¬ BddBelow (range (Homogeneous.finiteMaxLinear A hA)) →
    (∀ x, ¬ Homogeneous.Supports (Homogeneous.finiteMaxLinear A hA) x 0) ∧
    Xor' (Tendsto R.x atTop (𝓝 0) ∧
      Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)) atTop (𝓝 0) ∧
      (∀ k, 0 < Homogeneous.finiteMaxLinear A hA (R.x k)) ∧
      StrictAnti (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)))
    (Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)) atTop atBot ∧
      Tendsto (fun k => ‖euclideanVector (R.x k)‖) atTop atTop)

def ParabolicDenominatorTarget : Prop :=
  ∀ {m : ℕ} (P : Parabolic.Family m) {K : Set (Vec 2)}, IsCompact K →
    ∀ {η c₁ c₂ : ℝ}, 0 < η → 0 ≤ c₁ → c₂ < 1 →
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ x ∈ K, ∀ z ∈ K, ∀ g h : Vec 2,
      TransportedCertificate.EligiblePair P.objective c₁ c₂ x z g h →
      η ≤ P.objective x → TransportedCertificate.pairDecrease x z g ≤ δ →
      TransportedCertificate.pairDecrease x z g ≤ C * |Parabolic.Family.stepDeterminant x z| ∧
      |Parabolic.Family.horizontalStep x z| ≤ C * |Parabolic.Family.stepDeterminant x z| ∧
      Parabolic.Family.stepDeterminant x z ≠ 0

end BfgsVerification
