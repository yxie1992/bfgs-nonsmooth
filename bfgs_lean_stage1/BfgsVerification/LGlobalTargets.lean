import BfgsVerification.LGlobalVerification

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix Polynomial
namespace BfgsVerification.LGlobalTargets
open SeedOrbit SeedCycle LNormalizedReturn DeterministicLineSearch
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def GlobalFailureTarget : Prop :=
  ∀ {μ : ℝ}, 0<μ → ∀ U : Set (Vec 2), U∈𝓝 (0 : Vec 2) →
    ∃ R : AdmissibleBFGSRun 2 (LQuadraticSeed.objective μ),
      R.c₁=1/10000 ∧ R.c₂=1/2 ∧
      Tendsto R.x atTop (𝓝 0) ∧ Tendsto R.H atTop (𝓝 0) ∧
      Tendsto (fun k => LQuadraticSeed.objective μ (R.x k)) atTop (𝓝 0) ∧
      (∀ k, 0<LQuadraticSeed.objective μ (R.x k)) ∧
      (∀ k, LQuadraticSeed.objective μ (R.x (k+1))<LQuadraticSeed.objective μ (R.x k)) ∧
      (∀ k, R.α k=length (phase k)) ∧
      (∀ k, fromMetric (LQuadraticSeed.objective μ) (R.x k) (R.H k) (1/10000) (1/2) 5=
        (some (R.α k),trialHistory (phase k))) ∧
      (∀ k, R.x k∈U) ∧
      (∀ k q, trialPhase q=phase k →
        DifferentiableAt ℝ (LQuadraticSeed.objective μ)
          (R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1) ∧
        0<LQuadraticSeed.objective μ (R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1) ∧
        R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1∈U) ∧
      (∀ q : ℕ → Fin 9, (∀ k, trialPhase (q k)=phase k) →
        Tendsto (fun k => R.x k+trialLength (q k) • bfgsStep (R.H k) (R.g k) 1) atTop (𝓝 0)) ∧
      (∀ k, LQuadraticSeed.objective μ (R.x (k+1))<LQuadraticSeed.objective μ (R.x k)+
          (1/10000)*dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) ∧
        (1/2)*dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k))<
          dot (R.g (k+1)) (bfgsStep (R.H k) (R.g k) (R.α k))) ∧
      (0 : Vec 2)∉ConvexSubdifferential.subdifferential (LQuadraticSeed.objective μ) 0

theorem globalFailure : GlobalFailureTarget := LGlobalFailure.source_global_failure

def SpectrumTarget : Prop := ∀ μ : ℝ,

    ∃ ls lu : ℝ, (38/1000 < ls ∧ ls < 39/1000) ∧
      (1564/1000 < lu ∧ lu < 1565/1000) ∧
      ∃ E : LBlockSplitting.Coordinates ≃L[ℝ] State,
        (∀ w, E w 4=w.1 1) ∧
        (∀ w, (fderiv ℝ (returnMap μ) seed) (E w)=E
          (LBlockSplitting.diagonalMap ![ls,seedRatio] w.1,
           LBlockSplitting.diagonalMap ![seedRatio⁻¹,seedRatio⁻¹,lu] w.2)) ∧
        (fderiv ℝ (returnMap μ) seed).toLinearMap.charpoly=
          (X-C seedRatio⁻¹)^2*(X-C ls)*(X-C lu)*(X-C seedRatio)

theorem spectrum : SpectrumTarget := LReturnSpectrum.actual_spectral_contract

def LocalInverseTarget : Prop := ∀ μ : ℝ,

    ∃ S : State → State, ContDiffAt ℝ ⊤ S seed ∧ S seed=seed ∧
      (∀ᶠ x in 𝓝 seed, S (returnMap μ x)=x) ∧
      (∀ᶠ y in 𝓝 seed, returnMap μ (S y)=y)

theorem localInverse : LocalInverseTarget := LReturnLocalInverse.actual_local_inverse

end BfgsVerification.LGlobalTargets
