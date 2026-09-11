import BfgsVerification.LocalizationCorollaries
import BfgsVerification.StrictContours
import BfgsVerification.MovingFrame
import BfgsVerification.ResidualFrames

/-! Explicit propositions for the remaining Module M conclusions. Frame
certificates contain actual geometry and matrix operations, never a scalar
energy recurrence or an assumed principal-minor hierarchy. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter

namespace BfgsVerification

def HessianInvariantTarget : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ) (R : AdmissibleBFGSRun n F) (k : ℕ),
    R.hessian (k + 1) = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k) +
      (R.curvature k)⁻¹ • outer (R.gradientChange k) (R.gradientChange k) ∧
    (R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)).PosSemidef ∧
    (R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)).mulVec (R.displacement k) = 0 ∧
    (R.H (k + 1)).det = (R.α k / R.beta k) * (R.H k).det

def LocalizationTarget : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ), ConvexOn ℝ Set.univ F →
  ∀ xstar : Vec n, (∀ x, F xstar ≤ F x) →
    (∀ x, F x = F xstar → x = xstar) →
    (∀ a : ℝ, IsCompact {x | F x ≤ a}) ∧
    ∀ U : Set (Vec n), U ∈ 𝓝 xstar →
      ∃ δ : ℝ, 0 < δ ∧ {x | F x ≤ F xstar + δ} ⊆ U

def StrictContourTarget : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ) (R : AdmissibleBFGSRun n F),
    IsCompact R.initialSublevel → ∀ ℓ : ℝ,
    Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ) → (∃ z, F z < ℓ) →
    (∀ x z, segment ℝ x z ⊆ frontier {w | F w ≤ ℓ} → x = z) →
    Tendsto R.displacement atTop (𝓝 0)

def ReferenceEnergyTarget : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ) (R : AdmissibleBFGSRun n F) (xstar : Vec n),
    (∀ k, R.referenceEnergy xstar (k + 1) = R.referenceEnergy xstar k -
      (R.referencePairing xstar k) ^ 2 / R.q k + R.referenceCorrection xstar k) ∧
    ((∀ z, F xstar ≤ F z) → ∀ N : ℕ,
      (F (R.x N) - F xstar) ^ 2 * (∑ k ∈ Finset.range N, (R.q k)⁻¹) ≤
        R.referenceEnergy xstar 0 + ∑ k ∈ Finset.range N, R.referenceCorrection xstar k)

def QuadraticCorrectionTarget : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ) (R : AdmissibleBFGSRun n F) (xstar : Vec n),
    (∀ z, F xstar ≤ F z) → (∀ z, F z = F xstar → z = xstar) → ∀ C : ℝ,
    (∀ᶠ N in atTop, (∑ k ∈ Finset.range N, R.referenceCorrection xstar k) ≤ C * (N : ℝ) ^ 2) →
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar)

/-- Source exact-transport data on an arbitrary tail, with squared operator
bounds written explicitly. The starting normalization need not be the identity. -/
structure ExactFrameCertificate {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) where
  J : ℕ
  r : ℕ
  V : ℕ → Matrix (Fin n) (Fin r) ℝ
  T : ℕ → Mat r
  P : ℕ → Mat r
  b : ℕ → Vec r
  m : ℝ
  K : ℝ
  L : ℝ
  C : ℝ
  m_pos : 0 < m
  K_pos : 0 < K
  L_nonneg : 0 ≤ L
  invertible : ∀ k, J ≤ k → (P k).det ≠ 0
  product : ∀ k, J ≤ k → P (k + 1) = P k * T k
  transport : ∀ k, J ≤ k → V (k + 1) = V k * T k +
    EnergyIdentities.rectOuter (R.displacement k) (b k)
  visible : ∀ k, J ≤ k → m ≤ sqNorm ((V k)ᵀ.mulVec (R.g k))
  correction : ∀ k, J ≤ k →
    sqNorm ((V (k + 1))ᵀ.mulVec (R.gradientChange k)) / R.curvature k ≤ C
  product_bound : ∀ k, J ≤ k → ∀ v, sqNorm ((P k)ᵀ.mulVec v) ≤ K * sqNorm v
  inverse_bound : ∀ k, J ≤ k → ∀ v, sqNorm (((P k)⁻¹)ᵀ.mulVec v) ≤ L * sqNorm v

def MovingFrameCriterionTarget : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ) (R : AdmissibleBFGSRun n F) (G : ℝ),
    0 < G → (∀ k, sqNorm (R.g k) ≤ G ^ 2) → Tendsto R.d atTop (𝓝 0) →
    ¬ Nonempty (ExactFrameCertificate R)

/-- Source imperfect-transport data, retaining arbitrary real budget constants.
All frame indices are local to the chosen actual run tail. -/
structure ResidualFrameCertificate {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) where
  J : ℕ
  r : ℕ
  p : ℕ
  U : Matrix (Fin n) (Fin r) ℝ
  orthonormal : Uᵀ * U = 1
  L : ℝ
  m : ℝ
  C₀ : ℝ
  C_T : ℝ
  C_R : ℝ
  m_pos : 0 < m
  V : ℕ → Matrix (Fin n) (Fin p) ℝ
  Z : ℕ → Matrix (Fin n) (Fin p) ℝ
  T : ℕ → Mat p
  b : ℕ → Vec p
  smooth : ∀ k, sqNorm (Uᵀ.mulVec ((R.shift J).gradientChange k)) ≤ L * (R.shift J).curvature k
  visible : ∀ k, m ≤ sqNorm ((V k)ᵀ.mulVec ((R.shift J).g k))
  correction : ∀ k, sqNorm ((V (k + 1))ᵀ.mulVec ((R.shift J).gradientChange k)) ≤
    C₀ * (R.shift J).curvature k
  transport : ∀ k, V (k + 1) = V k * T k +
    EnergyIdentities.rectOuter ((R.shift J).displacement k) (b k) + Z k
  operator_bound : ∀ k, FrameBounds.OperatorSqBound (T k) (1 + C_T * (R.shift J).d k)
  residual_range : ∀ k, (U * Uᵀ) * Z k = Z k
  residual_size : ∀ k, SmoothSubspace.frobSq (Z k) ≤ C_R * (R.shift J).d k

def ResidualFrameCriterionTarget : Prop :=
  ∀ (n : ℕ) (F : Vec n → ℝ) (R : AdmissibleBFGSRun n F) (G : ℝ),
    0 < G → (∀ k, sqNorm (R.g k) ≤ G ^ 2) → Summable R.d →
    ¬ Nonempty (ResidualFrameCertificate R)

end BfgsVerification
