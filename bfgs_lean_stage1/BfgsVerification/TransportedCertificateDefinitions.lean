import BfgsVerification.ObjectiveDefinitions

/-! Module T's exact objective-pair and positive-band certificate quantifiers.
The field has finite real entries and is constrained only at differentiable
band points. No continuity, boundedness, rank or positive definiteness is imposed. -/

noncomputable section
open Matrix

namespace BfgsVerification.TransportedCertificate

def pairStep {n : ℕ} (x z : Vec n) : Vec n := z - x

def pairDecrease {n : ℕ} (x z g : Vec n) : ℝ := -dot g (pairStep x z)

def pairCurvature {n : ℕ} (x z g h : Vec n) : ℝ := dot (h - g) (pairStep x z)

/-- Eligibility is the source's objective-only pair condition, with actual
derivatives at both endpoints; it does not assert BFGS compatibility. -/
structure EligiblePair {n : ℕ} (F : Vec n → ℝ) (c₁ c₂ : ℝ)
    (x z g h : Vec n) : Prop where
  gradient_x : HasFDerivAt F (gradientFunctional g) x
  gradient_z : HasFDerivAt F (gradientFunctional h) z
  decrease_pos : 0 < pairDecrease x z g
  armijo : c₁ * pairDecrease x z g ≤ F x - F z
  convex_decrease : F x - F z ≤ pairDecrease x z g
  curvature : (1 - c₂) * pairDecrease x z g ≤ pairCurvature x z g h

/-- The actual Euclidean projector perpendicular to the step. Eligible pairs
have nonzero steps; the total formula also makes sense at zero. -/
def stepProjector {n : ℕ} (s : Vec n) : Mat n := 1 - (sqNorm s)⁻¹ • outer s s

def positiveBand {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (fstar η : ℝ) : Set (Vec n) :=
  {x | x ∈ K ∧ fstar + η ≤ F x}

/-- One-sided transported PSD certificate on one positive objective band.
The secant and transport conditions apply only to small eligible pairs in it. -/
structure BandCertificate {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n))
    (fstar c₁ c₂ η : ℝ) where
  W : Vec n → Mat n
  m : ℝ
  C : ℝ
  L : ℝ
  δ : ℝ
  m_pos : 0 < m
  L_nonneg : 0 ≤ L
  delta_pos : 0 < δ
  positive_semidefinite : ∀ x ∈ positiveBand F K fstar η,
    DifferentiableAt ℝ F x → (W x).PosSemidef
  visibility : ∀ x ∈ positiveBand F K fstar η, ∀ g,
    HasFDerivAt F (gradientFunctional g) x → m ≤ metricEnergy (W x) g
  secant : ∀ x z g h,
    x ∈ positiveBand F K fstar η → z ∈ positiveBand F K fstar η →
    EligiblePair F c₁ c₂ x z g h → pairDecrease x z g ≤ δ →
    metricEnergy (W z) (h - g) ≤ C * pairCurvature x z g h
  transport : ∀ x z g h,
    x ∈ positiveBand F K fstar η → z ∈ positiveBand F K fstar η →
    EligiblePair F c₁ c₂ x z g h → pairDecrease x z g ≤ δ →
    ((1 + L * pairDecrease x z g) •
      (stepProjector (pairStep x z) * W x * stepProjector (pairStep x z)) -
      stepProjector (pairStep x z) * W z * stepProjector (pairStep x z)).PosSemidef

/-- Empty positive bands require no certificate. -/
def HasBandCertificates {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n))
    (fstar c₁ c₂ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → (positiveBand F K fstar η).Nonempty →
    Nonempty (BandCertificate F K fstar c₁ c₂ η)

end BfgsVerification.TransportedCertificate
