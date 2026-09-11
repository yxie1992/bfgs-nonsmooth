import BfgsVerification.NormalSpikeVariableHessian
import BfgsVerification.NormalSpikeVariableRadialHessian

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.NormalSpike
open FixedNormal RadialCertificate

def VariableSpikeConvergenceTarget : Prop :=
  ∀ n : ℕ, ∀ c : Vec (n+1), Real.sqrt (sqNorm c) < 1 →
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun (n+2) (printedVariableObjective n c),
      printedVariableObjective n c (R.x 0) < ε →
        Tendsto (fun k => printedVariableObjective n c (R.x k)) atTop (𝓝 0) ∧
          Tendsto R.x atTop (𝓝 0)

def VariableSpikeSeparationTarget : Prop :=
  ∀ n : ℕ, ∀ c : Vec (n+1), Real.sqrt (sqNorm c) < 1 →
    ∀ K : Set (Vec (n+2)), K ∈ 𝓝 0 →
      ¬ HasRadialSecantBounds (printedVariableObjective n c) K 0

def VariableSpikeNonsplittingTarget : Prop :=
  ∀ n : ℕ, ∀ c : Vec (n+1), Real.sqrt (sqNorm c) < 1 → c ≠ 0 →
    ∀ U : Set (Vec (n+2)), IsOpen U → (0 : Vec (n+2)) ∈ U →
      ∀ S : Vec (n+2) → ℝ, ∀ h : ℝ → ℝ, DifferentiableOn ℝ S U →
        ¬ (∀ x ∈ U, printedVariableObjective n c x = S x+h (x 0))

def VariableSpikeGeometryTarget : Prop :=
  ∀ n : ℕ, ∀ c : Vec (n+1), Real.sqrt (sqNorm c) < 1 →
    ConvexOn ℝ univ (printedVariableObjective n c) ∧
    EuclideanStrongConvexOn univ (1-Real.sqrt (sqNorm c)) (printedVariableObjective n c) ∧
    printedVariableObjective n c 0 = 0 ∧
    (∀ x, printedVariableObjective n c 0 ≤ printedVariableObjective n c x) ∧
    (∀ x, printedVariableObjective n c x = printedVariableObjective n c 0 → x = 0) ∧
    (∀ x ∈ variableRegion (Fin.cons 0 c),
      DifferentiableAt ℝ (printedVariableObjective n c) x ↔ x 0 ≠ 0) ∧
    (∀ x ∈ variableRegion (Fin.cons 0 c), ∀ g,
      Homogeneous.Supports (printedVariableObjective n c) x g →
        tangentProjection (normal n) g = variableTangent (normal n) (Fin.cons 0 c) x) ∧
    (∀ u : Vec (n+1), ∀ v : ℝ,
      printedVariableObjective n c (Fin.cons v u) =
        (1/2 : ℝ)*(sqNorm u+v^2)+|(1+dot c u)*v|+sourcePrimitive v) ∧
    (∀ u : Vec (n+1), ∀ v : ℝ,
      variableTangent (normal n) (Fin.cons 0 c) (Fin.cons v u) = Fin.cons 0 (u+|v| • c))

def VariableSpikeHessianTarget : Prop :=
  ∀ n : ℕ, ∀ c : Vec (n+1), ∀ x : Vec (n+2), ∀ σ : ℝ,
    RadialHessian.matrix (variableQuadraticBranch (normal n) (Fin.cons 0 c) σ) x =
      (1 : Mat (n+2))+σ • (outer (Fin.cons 0 c) (normal n)+outer (normal n) (Fin.cons 0 c)) ∧
    (|σ| ≤ 1 → ∀ v : Vec (n+2),
      (1-Real.sqrt (sqNorm c))*sqNorm v ≤
        dot v ((RadialHessian.matrix (variableQuadraticBranch (normal n) (Fin.cons 0 c) σ) x).mulVec v))

theorem variableSpikeConvergence : VariableSpikeConvergenceTarget := printed_variable_local_fullBFGS

theorem variableSpikeSeparation : VariableSpikeSeparationTarget := by
  intro n c hc K hK
  exact printed_variable_no_radial_secant n c hc hK

theorem variableSpikeNonsplitting : VariableSpikeNonsplittingTarget := by
  intro n c _ hc U hU h0 S h hS hrep
  exact printed_variable_no_local_smooth_scalar_split n c hc hU h0 S h hS hrep

theorem variableSpikeGeometry : VariableSpikeGeometryTarget := by
  intro n c hc
  have hnorm : Real.sqrt (sqNorm (Fin.cons 0 c)) < 1 := by
    simpa only [extended_coupling_sqNorm] using hc
  refine ⟨variableObjective_convex (normal_unit n) (extended_coupling_tangent n c)
    (Real.sqrt_nonneg _) (Real.sq_sqrt (sqNorm_nonneg _)) hnorm.le,
    printed_variable_strongConvex n c, variableObjective_zero _ _, variableObjective_minimum _ _,
    variableObjective_unique_minimum _ _, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simpa only [normal_coordinate] using
      variableObjective_differentiable_iff_on_region (normal_unit n) (extended_coupling_tangent n c) x hx
  · intro x hx g hg
    exact variable_support_tangent (normal_unit n) (extended_coupling_tangent n c) (variableRegion_positive hx) hg
  · intro u v
    exact printed_variable_formula n c u v
  · intro u v
    exact printed_variable_tangent_formula n c u v

theorem variableSpikeHessian : VariableSpikeHessianTarget := by
  intro n c x σ
  refine ⟨variableQuadraticBranch_hessian_matrix _ _ _ _, ?_⟩
  intro hσ v
  simpa only [extended_coupling_sqNorm] using
    variableQuadraticBranch_hessian_lower (normal_unit n) (extended_coupling_tangent n c) σ hσ x v

end BfgsVerification.NormalSpike
