import BfgsVerification.RadialReverse
import BfgsVerification.RadialCentralDifference
import BfgsVerification.AffineImageLifting
import BfgsVerification.CompactSolutionBasin
import BfgsVerification.ObjectiveLogRates
import BfgsVerification.FiniteSampleCertificates
import BfgsVerification.ScalarCounterexamples
import BfgsVerification.AccumulatingKinks

/-! Exact statements for the third report tranche. None asserts whole-report
completion. Derivative and matrix quantities retain their actual definitions. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
open RadialCertificate AffineProjection TransportedCertificate OneDimensional

/-- Exact checked signature of `RadialCertificate.radial_iff_inward_on_compact_sublevel`. -/
def RadialInwardEquivalenceTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (b : ℝ) (hb : F star < b) (hK : IsCompact {x : Vec n | F x ≤ b}),
    HasRadialSecantBounds F {x | F x ≤ b} star ↔
      HasInwardTaylorBounds F {x | F x ≤ b} star

/-- Exact checked signature of `RadialCertificate.local_radial_iff_nested_central`. -/
def LocalRadialCentralEquivalenceTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ x, F star ≤ F x),
    (∃ b : ℝ, F star < b ∧ IsCompact {x : Vec n | F x ≤ b} ∧
      HasRadialSecantBounds F {x | F x ≤ b} star) ↔
    (∃ b : ℝ, F star < b ∧ IsCompact {x : Vec n | F x ≤ b} ∧
      HasNestedCentralBounds F star b)

/-- Exact checked signature of `AffineProjection.projectRun_limit_lift`. -/
def LinearImageLiftingTarget : Prop :=
  ∀ {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) (hA : FullRowRank A) (F : Vec r → ℝ) (R : AdmissibleBFGSRun n (fun x => F (A.mulVec x))) (zstar : Vec r)
    (hz : Tendsto (projectRun A hA F R).x atTop (𝓝 zstar)),
    Tendsto R.x atTop (𝓝 (fiberPoint A (R.H 0) (R.x 0) zstar)) ∧
    A.mulVec (fiberPoint A (R.H 0) (R.x 0) zstar) = zstar ∧
    ∀ x : Vec n, A.mulVec x = zstar →
      metricEnergy (R.H 0)⁻¹ (fiberPoint A (R.H 0) (R.x 0) zstar - R.x 0) ≤
        metricEnergy (R.H 0)⁻¹ (x - R.x 0) ∧
      (metricEnergy (R.H 0)⁻¹ (x - R.x 0) =
          metricEnergy (R.H 0)⁻¹ (fiberPoint A (R.H 0) (R.x 0) zstar - R.x 0) ↔
        x = fiberPoint A (R.H 0) (R.x 0) zstar)

/-- Exact checked signature of `TransportedCertificate.local_transported_certificate_basin_of_compact_solution_set`. -/
def NonuniqueSolutionBasinTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (star : Vec n) (hmin : ∀ x, F star ≤ F x) (b : ℝ) (hb : F star < b)
    (hK : IsCompact {x | F x ≤ b}) {U : Set (Vec n)}
    (hU : ∀ x, F x = F star → U ∈ 𝓝 x) {c₁ c₂ : ℝ}
    (hcert : HasBandCertificates F ({x | F x ≤ b} ∩ U) (F star) c₁ c₂),
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F,
      R.c₁ = c₁ → R.c₂ = c₂ → F (R.x 0) ≤ F star + δ →
      (∀ k, F (R.x k) ≤ b ∧ R.x k ∈ U) ∧
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ x, F x = F star → x = star) → Tendsto R.x atTop (𝓝 star))

/-- Exact checked signature of `AdmissibleBFGSRun.compact_value_rate_of_linear_corrections`. -/
def LinearCorrectionRateTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (star : Vec n)
    (hmin : ∀ x, F star ≤ F x) (hK : IsCompact R.initialSublevel) (C : ℝ)
    (hC : ∀ᶠ N in atTop,
      (∑ k ∈ Finset.range N, R.referenceCorrection star k) ≤ C * (N : ℝ)),
    Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) * (F (R.x N) - F star))
      atTop (𝓝 0)

/-- Exact checked signature of `TransportedCertificate.eligible_pair_realizable`. -/
def EligiblePairRealizabilityTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} {c₁ c₂ : ℝ}
    {x z g h : Vec n} (hp : EligiblePair F c₁ c₂ x z g h),
    ∃ H : Mat n, H.PosDef ∧ bfgsStep H g 1 = pairStep x z ∧
      metricEnergy H g = pairDecrease x z g

/-- Exact checked signature of `TransportedCertificate.positive_band_finite_sample_feasible`. -/
def FiniteSampleFeasibilityTarget : Prop :=
  ∀ {n r : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) {c₁ c₂ : ℝ} (hc₂ : c₂ < 1)
    (x g : Fin r → Vec n) (hdiff : ∀ i, HasFDerivAt F (gradientFunctional (g i)) (x i))
    (hband : ∀ i, F star < F (x i)) (P : Finset (Fin r × Fin r))
    (hp : ∀ p ∈ P, EligiblePair F c₁ c₂ (x p.1) (x p.2) (g p.1) (g p.2)),
    ∃ m C : ℝ, (1 : Mat n).PosSemidef ∧ 0 < m ∧ 0 ≤ C ∧
      (∀ i, m ≤ metricEnergy (1 : Mat n) (g i)) ∧
      (∀ p ∈ P, metricEnergy (1 : Mat n) (g p.2 - g p.1) ≤
        C * pairCurvature (x p.1) (x p.2) (g p.1) (g p.2)) ∧
      (∀ s : Vec n, (stepProjector s * (1 : Mat n) * (stepProjector s)ᵀ -
        stepProjector s * (1 : Mat n) * (stepProjector s)ᵀ).PosSemidef)
/-- Finite and little-o homogeneous bounds for lower-bounded runs, plus the
Euclidean iterate norm rate when the objective is coercive. -/
def HomogeneousRatesTarget : Prop :=
  ∀ {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F),
    Homogeneous.PositiveDegreeOne F → ∀ L : ℝ, (∀ k, L ≤ F (R.x k)) →
    (∀ N : ℕ, 0 < N → F (R.x N) ≤ Real.sqrt (R.homogeneousPotential 0 /
      (∑ k ∈ Finset.range N, (R.q k)⁻¹))) ∧
    Tendsto (fun N : ℕ => (N : ℝ) * F (R.x N)) atTop (𝓝 0) ∧
    (Tendsto F (cocompact (Vec n)) atTop →
      Tendsto (fun N : ℕ => (N : ℝ) * ‖euclideanVector (R.x N)‖) atTop (𝓝 0))

/-- The actual shifted quadratic-plus-absolute-value objective has no global
certificate on the displayed sublevel, while all its scalar runs converge. -/
def ScalarGlobalCertificateNonnecessityTarget : Prop :=
  let f := ScalarCounterexamples.shiftedAbs
  let F := ScalarCounterexamples.shiftedObjective
  StrongConvexOn univ 1 f ∧ (∀ x, f (-1) ≤ f x) ∧
    (∀ x, f x = f (-1) → x = -1) ∧
    (¬ HasBandCertificates F {x | F x ≤ 3} (F (embed (-1))) (1 / 4) (1 / 2)) ∧
    (∀ R : ScalarMetricRun f, Tendsto (fun k => f (R.x k)) atTop (𝓝 (3 / 2)) ∧
      Tendsto R.x atTop (𝓝 (-1))) ∧
    (∀ R : AdmissibleBFGSRun 1 F, Tendsto (fun k => F (R.x k)) atTop (𝓝 (3 / 2)) ∧
      Tendsto R.x atTop (𝓝 (embed (-1))))

/-- The actual accumulating-hinge series defeats certificates in every
neighborhood of the optimizer while every admissible scalar run converges. -/
def ScalarLocalCertificateNonnecessityTarget : Prop :=
  let f := AccumulatingKinks.objective
  let F := AccumulatingKinks.coordinateObjective
  StrongConvexOn univ 1 f ∧ Tendsto f (cocompact ℝ) atTop ∧
    ConvexOn ℝ univ f ∧ (∀ x, f 0 ≤ f x) ∧ (∀ x, f x = f 0 → x = 0) ∧
    (∀ b : ℝ, IsCompact {x | f x ≤ b}) ∧
    (∀ K : Set (Vec 1), K ∈ 𝓝 (0 : Vec 1) →
      ¬ HasBandCertificates F K 0 (1 / 4) (1 / 2)) ∧
    (∀ R : ScalarMetricRun f, Tendsto (fun k => f (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0)) ∧
    (∀ R : AdmissibleBFGSRun 1 F, Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0))

end BfgsVerification
