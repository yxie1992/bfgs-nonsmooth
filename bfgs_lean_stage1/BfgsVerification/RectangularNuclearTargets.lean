import BfgsVerification.CenteredRectangularNuclear
import BfgsVerification.FirstDifferencePenalty

/-! Exact source contracts for R's remaining named matrix and fused families. -/
noncomputable section
open scoped BigOperators Topology Matrix.L2OpNorm
open Set Filter
namespace BfgsVerification

def RectangularNuclearNormTarget : Prop := ∀ m n : ℕ, ∀ A : Matrix (Fin m) (Fin n) ℝ,
  RectangularNuclear.nuclear A = ∑ i : Fin n,
    Real.sqrt ((Matrix.isHermitian_transpose_mul_self A).eigenvalues i) ∧
  RectangularNuclear.nuclear A = Matrix.trace (Matrix.posSemidef_conjTranspose_mul_self A).sqrt ∧
  (∀ B : Matrix (Fin m) (Fin n) ℝ, ‖B‖ ≤ 1 →
    RectangularNuclear.pairing A B ≤ RectangularNuclear.nuclear A) ∧
  (∃ B : Matrix (Fin m) (Fin n) ℝ, ‖B‖ ≤ 1 ∧
    RectangularNuclear.pairing A B=RectangularNuclear.nuclear A) ∧
  (RectangularNuclear.nuclear A=0 ↔ A=0) ∧
  (∀ t : ℝ, RectangularNuclear.nuclear (t • A)=‖t‖*RectangularNuclear.nuclear A) ∧
  (∀ B : Matrix (Fin m) (Fin n) ℝ,
    RectangularNuclear.nuclear (A+B) ≤ RectangularNuclear.nuclear A+RectangularNuclear.nuclear B)

theorem rectangularNuclearNorm : RectangularNuclearNormTarget := by
  intro m n A
  exact ⟨RectangularNuclear.nuclear_eq_sum_singularValues A,
    RectangularNuclear.nuclear_eq_trace_sqrt A,(RectangularNuclear.nuclear_variational A).1,
    (RectangularNuclear.nuclear_variational A).2,RectangularNuclear.nuclear_eq_zero_iff A,
    fun t => RectangularNuclear.nuclear_smul t A,fun B => RectangularNuclear.nuclear_add_le A B⟩

def CenteredRectangularNuclearTarget : Prop := ∀ m n : ℕ,
  (∀ R : AdmissibleBFGSRun (m*n) (RectangularNuclear.objective (m := m) (n := n)),
    Tendsto (fun k => RectangularNuclear.objective (m := m) (n := n) (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0)) ∧
  (∀ x g : Vec (m*n),
    HasFDerivAt (RectangularNuclear.objective (m := m) (n := n)) (gradientFunctional g) x →
    ∀ t : ℝ, t ≤ 1 → RadialCertificate.supportingError
      (RectangularNuclear.objective (m := m) (n := n)) x g (RadialCertificate.inwardPoint 0 x t)=0) ∧
  (∀ K : Set (Vec (m*n)), IsCompact K → RadialCertificate.HasRadialSecantBounds
    (RectangularNuclear.objective (m := m) (n := n)) K 0)

theorem centeredRectangularNuclear : CenteredRectangularNuclearTarget := by
  intro m n
  exact ⟨RectangularNuclear.fullBFGS_convergence,
    fun x g hg t ht => RectangularNuclear.inward_error_zero hg ht,
    fun K hK => RectangularNuclear.radial_bounds hK⟩

def MixedNuclearPowersTarget : Prop := ∀ d r : ℕ, ∀ rows cols : Fin r → ℕ,
  ∀ F ψ : Vec d → ℝ, ∀ R : AdmissibleBFGSRun d F,
  ∀ A : ∀ j, Vec d →ₗ[ℝ] Vec (rows j*cols j), ∀ p : Fin r → ℝ,
  (∀ j, 1 ≤ p j) → ∀ star : Vec d, (∀ x, F star ≤ F x) →
  ∀ U : Set (Vec d), IsOpen U → CenteredSmoothSublinear.LocallyC11On U ψ →
  IsCompact R.initialSublevel → R.initialSublevel ⊆ U →
  (∀ x ∈ U, F x=ψ x+∑ j,
    (RectangularNuclear.objective (m := rows j) (n := cols j) (A j (x-star)))^(p j)) →
  Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
    Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
    ((∀ x, F x=F star → x=star) → Tendsto R.x atTop (𝓝 star))

theorem mixedNuclearPowers : MixedNuclearPowersTarget := by
  intro d r rows cols F ψ R A p hp star hmin U hU hsmooth hK hKU hrep
  exact RectangularNuclear.mixed_nuclear_powers_convergence rows cols R A p hp star hmin
    hU hsmooth hK hKU hrep

def FirstDifferenceBasinTarget : Prop := ∀ n : ℕ, ∀ weight : ℝ, 0 ≤ weight →
  ∀ ψ : Vec (n+1) → ℝ, ConvexOn ℝ univ (FirstDifference.objective n weight ψ) →
  ∀ U : Set (Vec (n+1)), IsOpen U → CenteredSmoothSublinear.LocallyC11On U ψ →
  ∀ star : Vec (n+1), star ∈ U →
  (∀ x, FirstDifference.objective n weight ψ star ≤ FirstDifference.objective n weight ψ x) →
  (∀ x, FirstDifference.objective n weight ψ x=FirstDifference.objective n weight ψ star → x=star) →
  ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun (n+1) (FirstDifference.objective n weight ψ),
    FirstDifference.objective n weight ψ (R.x 0) ≤ FirstDifference.objective n weight ψ star+δ →
    (∀ k, R.x k ∈ U) ∧
    Tendsto (fun k => FirstDifference.objective n weight ψ (R.x k)) atTop
      (𝓝 (FirstDifference.objective n weight ψ star)) ∧ Tendsto R.x atTop (𝓝 star)

theorem firstDifferenceBasin : FirstDifferenceBasinTarget := by
  intro n weight hweight ψ hF U hU hψ star hs hmin hu
  exact FirstDifference.local_fullBFGS hweight hF hU hψ hs hmin hu

end BfgsVerification
