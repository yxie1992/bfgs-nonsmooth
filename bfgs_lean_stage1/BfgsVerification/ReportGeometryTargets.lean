import BfgsVerification.TransportedCertificateVariants
import BfgsVerification.HomogeneousCommonTilt
import BfgsVerification.HomogeneousCardinality
import BfgsVerification.ScalarCertificate
import BfgsVerification.IncomingJumpObstruction
import BfgsVerification.InwardRadial
import BfgsVerification.ConvexGradientLimits

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification

/-- G's exact removal of the expansion allowance on a value-bounded domain. -/
def CertificateNormalizationTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)} {fstar c₁ c₂ : ℝ},
    0 < c₁ → c₂ < 1 → ∀ b : ℝ, (∀ x ∈ K, F x ≤ b) →
    (TransportedCertificate.HasBandCertificates F K fstar c₁ c₂ ↔
      ∀ η : ℝ, 0 < η → (TransportedCertificate.positiveBand F K fstar η).Nonempty →
        ∃ C : TransportedCertificate.BandCertificate F K fstar c₁ c₂ η, C.L = 0)

/-- H.B for actual finite max-linear objectives with the alphabet derived. -/
def RecurrentAffineHullTarget : Prop :=
  ∀ {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun n (Homogeneous.finiteMaxLinear A hA)) (L : ℝ),
    Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)) atTop (𝓝 L) →
    (0 : Vec n) ∈ affineSpan ℝ (Homogeneous.recurrentValues R.g)

/-- H.B's full-slope affine exclusion forces actual value escape. -/
def MaxLinearAffineEscapeTarget : Prop :=
  ∀ {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun n (Homogeneous.finiteMaxLinear A hA)),
    (0 : Vec n) ∉ affineSpan ℝ (A : Set (Vec n)) →
    Tendsto (fun k => Homogeneous.finiteMaxLinear A hA (R.x k)) atTop atBot

/-- R's full supporting-intercept equivalence on compact domains. -/
def RadialInterceptEquivalenceTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ}, ConvexOn ℝ univ F →
    ∀ {K : Set (Vec n)}, IsCompact K → ∀ star : Vec n,
    RadialCertificate.HasRadialSecantBounds F K star ↔
      RadialCertificate.HasInterceptBounds F K star

/-- IR's sufficient full-BFGS conclusion; the converse RS-to-IR approximation
argument is a separate outstanding source obligation. -/
def InwardCertificateConvergenceTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (b : ℝ),
    IsCompact {x : Vec n | F x ≤ b} → ∀ star : Vec n,
    (∀ x, F star ≤ F x) → F (R.x 0) ≤ b →
    RadialCertificate.HasInwardTaylorBounds F {x | F x ≤ b} star →
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ x, F x = F star → x = star) → Tendsto R.x atTop (𝓝 star))

/-- G's obstruction to visibility and secant suppression alone, using actual
common-target eligible pairs on a fixed band, without any field regularity. -/
def IncomingJumpObstructionTarget : Prop :=
  ∀ {ι : Type} {l : Filter ι} [NeBot l] {n r : ℕ} {F : Vec n → ℝ}
    {K : Set (Vec n)} {fstar c₁ c₂ η : ℝ}, c₂ < 1 →
    ∀ (z h : ι → Vec n) (x g : ι → Fin r → Vec n) (coeff : ι → Fin r → ℝ),
    (∀ a, z a ∈ TransportedCertificate.positiveBand F K fstar η) →
    (∀ a j, x a j ∈ TransportedCertificate.positiveBand F K fstar η) →
    (∀ a, HasFDerivAt F (gradientFunctional (h a)) (z a)) →
    (∀ a j, TransportedCertificate.EligiblePair F c₁ c₂ (x a j) (z a) (g a j) (h a)) →
    (∀ j, Tendsto (fun a => TransportedCertificate.pairDecrease (x a j) (z a) (g a j)) l (𝓝 0)) →
    (∀ᶠ a in l, h a = ∑ j, coeff a j • (h a - g a j)) →
    Tendsto (fun a => ∑ j, |coeff a j| *
      Real.sqrt (TransportedCertificate.pairCurvature (x a j) (z a) (g a j) (h a))) l (𝓝 0) →
    ¬ Nonempty (TransportedCertificate.VisibilitySecantCertificate F K fstar c₁ c₂ η)

/-- G's exact scalar characterization, restricted to eligible small pairs. -/
def ScalarCertificateCharacterizationTarget : Prop :=
  ∀ {F : Vec 1 → ℝ} {K : Set (Vec 1)}, ConvexOn ℝ univ F →
    ∀ star : Vec 1, IsCompact K → ∀ {c₁ c₂ η : ℝ}, c₂ < 1 → 0 < η →
    (Nonempty (TransportedCertificate.BandCertificate F K (F star) c₁ c₂ η) ↔
      TransportedCertificate.ScalarEligibleLipschitz F K (F star) c₁ c₂ η)

end BfgsVerification
