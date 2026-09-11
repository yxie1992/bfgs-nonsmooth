import BfgsVerification.ParabolicExampleContrast
import BfgsVerification.TransformedGaugeInverse
import BfgsVerification.ShiftedAbsAccessibility
import BfgsVerification.HomogeneousRelativeInteriorConvergence

/-! Exact objective-level contracts for the fifth report milestone. Auxiliary
metric-fiber and inverse-derivative statements are audited separately. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification

def ParabolicCertificateTarget : Prop :=
  ∀ {m : ℕ} (P : Parabolic.Family m) {K : Set (Vec 2)}, IsCompact K →
    ∀ {η c₁ c₂ : ℝ}, 0 < η → 0 ≤ c₁ → c₂ < 1 →
    ∃ B : TransportedCertificate.BandCertificate P.objective K 0 c₁ c₂ η,
      ∀ x, B.W x = outer (P.calibratedVector x) (P.calibratedVector x)

def ParabolicConvergenceTarget : Prop :=
  ∀ {m : ℕ} (P : Parabolic.Family m) (R : AdmissibleBFGSRun 2 P.objective),
    Tendsto (fun k => P.objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)

def TransformedGaugeConvergenceTarget : Prop :=
  ∀ {n : ℕ} {Φ : ℝ → ℝ} {γ : Vec n → ℝ}, TransformedGauge.IncreasingTransform Φ →
    ConvexOn ℝ univ γ → Homogeneous.PositiveDegreeOne γ →
    Tendsto γ (cocompact (Vec n)) atTop → ∀ (star : Vec n)
      (R : AdmissibleBFGSRun n (TransformedGauge.objective Φ γ star)),
    Tendsto (fun k => TransformedGauge.objective Φ γ star (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 star)

def RelativeInteriorConvergenceTarget : Prop :=
  ∀ {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty)
    (R : AdmissibleBFGSRun n (Homogeneous.finiteMaxLinear A hA)),
    Homogeneous.RelativeInteriorZero A →
    ∃ xstar : Vec n, Tendsto R.x atTop (𝓝 xstar) ∧ Homogeneous.finiteMaxLinear A hA xstar = 0

def RecurrentRelativeInteriorTarget : Prop :=
  ∀ {n : ℕ} (A B : Finset (Vec n)) (hA : A.Nonempty) (hB : B.Nonempty)
    (R : AdmissibleBFGSRun n (Homogeneous.finiteMaxLinear A hA)),
    (B : Set (Vec n)) = Homogeneous.recurrentValues R.g → Homogeneous.RelativeInteriorZero B →
    ∃ xstar : Vec n, Tendsto R.x atTop (𝓝 xstar) ∧ Homogeneous.finiteMaxLinear A hA xstar = 0

def ParabolicEligibleSeparationTarget : Prop :=
  ∀ {K : Set (Vec 2)}, K ∈ 𝓝 (0 : Vec 2) → ∀ {c₁ c₂ : ℝ}, c₁ < 1 → 0 ≤ c₂ →
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → ∀ C : ℝ,
      ∃ x z g h : Vec 2, ∃ H : Mat 2,
        x ∈ K ∧ z ∈ K ∧ η ≤ Parabolic.Example.objective z ∧
        Parabolic.Example.objective z ≤ Parabolic.Example.objective x ∧
        TransportedCertificate.EligiblePair Parabolic.Example.objective c₁ c₂ x z g h ∧
        TransportedCertificate.pairDecrease x z g ≤ δ ∧ H.PosDef ∧
        bfgsStep H g 1 = TransportedCertificate.pairStep x z ∧
        C*TransportedCertificate.pairCurvature x z g h < (RadialCertificate.radialNumerator 0 z g h)^2

def ParabolicNonnecessityTarget : Prop :=
  ∀ {K : Set (Vec 2)}, K ∈ 𝓝 (0 : Vec 2) →
    (∀ R : AdmissibleBFGSRun 2 Parabolic.Example.objective,
      Tendsto (fun k => Parabolic.Example.objective (R.x k)) atTop (𝓝 0) ∧
        Tendsto R.x atTop (𝓝 0)) ∧
      ¬ RadialCertificate.HasRadialSecantBounds Parabolic.Example.objective K 0

open ScalarCounterexamples OneDimensional TransportedCertificate ShiftedAbsAccessibility in
def AccessibleActiveSeparationTarget : Prop :=
    ∃ B : BandCertificate shiftedObjective {x | shiftedObjective x ≤ 3}
        (shiftedObjective (embed (-1))) (1/8) (1/4) (1/4),
      B.W = (fun _ => 1) ∧ Continuous B.W ∧
      (∀ i k, HasFDerivAt shiftedObjective (gradientFunctional (activeGradientApproach i k))
        (activeApproach i k)) ∧
      (∀ i, Tendsto (activeApproach i) atTop (𝓝 0) ∧
        Tendsto (activeGradientApproach i) atTop (𝓝 (activeGradients i))) ∧
      (∀ i k, activeApproach i k ∈ positiveBand shiftedObjective {x | shiftedObjective x ≤ 3}
        (shiftedObjective (embed (-1))) (1/4)) ∧
      (∀ i, 0 < metricEnergy (B.W 0) (activeGradients i)) ∧
      (∀ i, (AccessibleJumpGeometry.tangentSpace (fun j => euclideanVector (activeGradients j))).orthogonalProjection
        (euclideanVector (activeGradients i)) = 0)

end BfgsVerification
