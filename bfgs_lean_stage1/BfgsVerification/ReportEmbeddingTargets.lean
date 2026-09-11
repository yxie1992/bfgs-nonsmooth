import BfgsVerification.DEmbeddingTarget
import BfgsVerification.LQuadraticSeed

/-! Exact targets for the actual D objective and deterministic embedding,
and L's concrete quadratic seed geometry. L orbit existence is a separate obligation. -/
noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.DEmbedding
open SeedCycle SeedOrbit DScalarGeometric DeterministicLineSearch

def ObjectiveGeometryTarget : Prop :=
    (∀ x, objective x=Finset.univ.sup' Finset.univ_nonempty (fun i => branch i x)) ∧
    (∀ i, ConvexOn ℝ univ (branch i) ∧ ContDiff ℝ 2 (branch i)) ∧
    ConvexOn ℝ univ objective ∧
    objective 0=0 ∧ (∀ x, 0 ≤ objective x) ∧ (∀ x, objective x=0 ↔ x=0) ∧
    (∀ a, IsCompact {x | objective x ≤ a}) ∧
    ¬ DifferentiableAt ℝ objective (0 : Vec 2) ∧
    (∀ h, Tendsto (fun t : ℝ => (objective (t • h)-objective 0)/t)
      (𝓝[>] 0) (𝓝 (max 0 (h 1)))) ∧
    (∀ i x, (RadialHessian.matrix (branch i) x).PosSemidef ∧
      ((64 : ℝ) • (1 : Mat 2)-RadialHessian.matrix (branch i) x).PosSemidef) ∧
    (∀ i x y, FrameNorms.euclideanOpNorm
      (RadialHessian.matrix (branch i) x-RadialHessian.matrix (branch i) y)
      ≤ 60000*‖euclideanVector (x-y)‖)

def EmbeddingFailureTarget : Prop :=
    Tendsto (fun n => SeedEmbedding.point (center n) ((scale n)^2) 0) atTop (𝓝 0) ∧
    Tendsto (fun n => objective (SeedEmbedding.point (center n) ((scale n)^2) 0)) atTop (𝓝 0) ∧
    (∀ n, center n≠0 ∧ objective (center n)=(scale n)^3 ∧ 0<objective (center n) ∧
      (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential objective (center n) ∧
      Tendsto (fun t : ℝ => (objective (center n+t • descentDirection)-objective (center n))/t)
        (𝓝[>] 0) (𝓝 (-((scale n)^2)))) ∧
    (∀ V ∈ 𝓝 (0 : Vec 2), ∀ᶠ n in atTop,
      (∀ k, SeedEmbedding.point (center n) ((scale n)^2) k ∈ V) ∧
      ∀ k q, trialPhase q=phase k → center n+(scale n)^2 • SeedEmbedding.trialPoint k q ∈ V) ∧
    (∀ (c₁ c₂ : ℝ) (hc₁ : 0<c₁) (hc₁' : c₁≤1/3) (hc : c₁<c₂) (hc₂ : c₂<1)
        (n : ℕ) (hn : 1≤n),
      let R := run hn c₁ c₂ hc₁ hc₁' hc hc₂
      R.H 0=1 ∧ (∀ k, (R.H k).PosDef) ∧
      Tendsto R.x atTop (𝓝 (center n)) ∧
      Tendsto (fun k => objective (R.x k)) atTop (𝓝 (objective (center n))) ∧
      (∀ k, objective (center n)<objective (R.x k)) ∧
      (∀ k, objective (R.x (k+1))<objective (R.x k)) ∧
      (∀ k, fromMetric objective (R.x k) (R.H k) c₁ c₂ 5=
        (some (R.α k),trialHistory (phase k))) ∧
      (∀ k, (trialHistory (phase k)).length≤5) ∧
      (∀ k q, trialPhase q=phase k →
        HasFDerivAt objective (gradientFunctional ((scale n)^2 • SeedOrbit.gradient seedC seedD (trialActive q)))
          (R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1)) ∧
      (∀ m j, R.x (3*m+j.val)=center n+(scale n)^2 • (seedRatio^m • SeedOrbit.point seedC seedD seedRatio j) ∧
        R.H (3*m+j.val)=seedRatio^m • metric seedC seedD j ∧
        R.g (3*m+j.val)=(scale n)^2 • SeedOrbit.gradient seedC seedD j ∧
        R.α (3*m+j.val)=length j))

end BfgsVerification.DEmbedding

namespace BfgsVerification.LQuadraticSeed
open SeedCycle SeedOrbit

def QuadraticSeedTarget : Prop :=
  ∀ μ : ℝ, 0<μ →
    (∀ x, objective μ x=μ/2*sqNorm x+SeedOrbit.objective seedC seedD x) ∧
    (∀ x, objective μ x=Finset.univ.sup' Finset.univ_nonempty (fun i => branch μ i x)) ∧
    FixedNormal.EuclideanStrongConvexOn univ μ (objective μ) ∧
    StrongConvexOn univ μ (fun x : EuclideanSpace ℝ (Fin 2) => objective μ (fun i => x i)) ∧
    (∀ i, ConvexOn ℝ univ (branch μ i) ∧ ContDiff ℝ 2 (branch μ i)) ∧
    (∀ i x, RadialHessian.matrix (branch μ i) x=μ • (1 : Mat 2)) ∧
    Tendsto (objective μ) (cocompact (Vec 2)) atTop ∧
    (∀ a, IsCompact {x | objective μ x ≤ a}) ∧
    gbar=(129/257 : ℝ) • g0+(128/257 : ℝ) • g1 ∧
    gbar ∈ convexHull ℝ slopes ∧
    (∀ g ∈ convexHull ℝ slopes, ‖euclideanVector gbar‖ ≤ ‖euclideanVector g‖) ∧
    minimizer μ=(-μ⁻¹) • gbar ∧ minimizer μ ≠ 0 ∧
    objective μ (minimizer μ)=-1/(514*μ) ∧
    (∀ x, objective μ (minimizer μ) ≤ objective μ x) ∧
    (∀ x, objective μ x=objective μ (minimizer μ) → x=minimizer μ) ∧
    (∀ i, branch μ i (minimizer μ)=objective μ (minimizer μ) ↔ i=0 ∨ i=1) ∧
    ¬ DifferentiableAt ℝ (objective μ) (minimizer μ) ∧
    objective μ 0=0 ∧
    ConvexSubdifferential.subdifferential (objective μ) 0=convexHull ℝ slopes ∧
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential (objective μ) 0

end BfgsVerification.LQuadraticSeed
