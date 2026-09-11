import BfgsVerification.ReportEmbeddingEndToEnd
import BfgsVerification.DLiteralTargets
import BfgsVerification.LGlobalTargets
import BfgsVerification.LIdentityGeometry
import BfgsVerification.LStableInvariantManifold
import Lean.Util.CollectAxioms

/-! Bounded original-claim review, 2026-09-11.
These literal propositions are fixed in this standalone audit source. The
reproduction command does not generate expectations from library target aliases.
They preserve all quantifiers and expand the local-L geometry/run conjunctions.
Only existing main-library modules are imported. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Matrix Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000


namespace BfgsVerification.DEmbedding
open SeedCycle SeedOrbit DScalarGeometric DeterministicLineSearch

def Review20ObjectiveGeometryTarget : Prop :=
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

def Review20EmbeddingFailureTarget : Prop :=
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

theorem review20ObjectiveGeometry : Review20ObjectiveGeometryTarget := objectiveGeometry

theorem review20EmbeddingFailure : Review20EmbeddingFailureTarget := embeddingFailure

end BfgsVerification.DEmbedding


namespace BfgsVerification.DLiteralTargets
open SeedOrbit SeedCycle

def Review20NonStrictRunTarget : Prop :=
  ∀c₁ c₂ : ℝ, ∀hc₁ : 0 < c₁, ∀hc₁' : c₁ ≤ 1/3, ∀hc : c₁ < c₂, ∀hc₂ : c₂ < 1,
  (let R := SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂
   ∀k : ℕ,
    NonStrictLineSearch.fromMetric (objective seedC seedD) (R.x k) (R.H k) c₁ c₂ 5 =
      (some (R.α k),trialHistory (phase k)) ∧
    NonStrictLineSearch.fromMetric (objective seedC seedD) (R.x k) (R.H k) c₁ c₂ 5 =
      DeterministicLineSearch.fromMetric (objective seedC seedD) (R.x k) (R.H k) c₁ c₂ 5) ∧
  (let R := coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂
   ∀k : ℕ,
    NonStrictLineSearch.fromMetric coerciveObjective (R.x k) (R.H k) c₁ c₂ 5 =
      (some (R.α k),trialHistory (phase k)) ∧
    NonStrictLineSearch.fromMetric coerciveObjective (R.x k) (R.H k) c₁ c₂ 5 =
      DeterministicLineSearch.fromMetric coerciveObjective (R.x k) (R.H k) c₁ c₂ 5) ∧
  (∀n : ℕ, ∀hn : 1 ≤ n,
   let R := DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂
   ∀k : ℕ,
    NonStrictLineSearch.fromMetric DEmbedding.objective (R.x k) (R.H k) c₁ c₂ 5 =
      (some (R.α k),trialHistory (phase k)) ∧
    NonStrictLineSearch.fromMetric DEmbedding.objective (R.x k) (R.H k) c₁ c₂ 5 =
      DeterministicLineSearch.fromMetric DEmbedding.objective (R.x k) (R.H k) c₁ c₂ 5)

theorem review20NonStrictRun : Review20NonStrictRunTarget := nonStrictRun

end BfgsVerification.DLiteralTargets


namespace BfgsVerification.LQuadraticSeed
open SeedCycle SeedOrbit

def Review20QuadraticSeedTarget : Prop :=
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

theorem review20QuadraticSeed : Review20QuadraticSeedTarget := quadraticSeed

end BfgsVerification.LQuadraticSeed


namespace BfgsVerification.LGlobalTargets
open SeedOrbit SeedCycle LNormalizedReturn DeterministicLineSearch
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Review20GlobalFailureTarget : Prop :=
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

def Review20SpectrumTarget : Prop := ∀ μ : ℝ,

    ∃ ls lu : ℝ, (38/1000 < ls ∧ ls < 39/1000) ∧
      (1564/1000 < lu ∧ lu < 1565/1000) ∧
      ∃ E : LBlockSplitting.Coordinates ≃L[ℝ] State,
        (∀ w, E w 4=w.1 1) ∧
        (∀ w, (fderiv ℝ (returnMap μ) seed) (E w)=E
          (LBlockSplitting.diagonalMap ![ls,seedRatio] w.1,
           LBlockSplitting.diagonalMap ![seedRatio⁻¹,seedRatio⁻¹,lu] w.2)) ∧
        (fderiv ℝ (returnMap μ) seed).toLinearMap.charpoly=
          (X-C seedRatio⁻¹)^2*(X-C ls)*(X-C lu)*(X-C seedRatio)

def Review20LocalInverseTarget : Prop := ∀ μ : ℝ,

    ∃ S : State → State, ContDiffAt ℝ ⊤ S seed ∧ S seed=seed ∧
      (∀ᶠ x in 𝓝 seed, S (returnMap μ x)=x) ∧
      (∀ᶠ y in 𝓝 seed, returnMap μ (S y)=y)

theorem review20GlobalFailure : Review20GlobalFailureTarget := globalFailure

theorem review20Spectrum : Review20SpectrumTarget := spectrum

theorem review20LocalInverse : Review20LocalInverseTarget := localInverse

end BfgsVerification.LGlobalTargets


namespace BfgsVerification.LWhitening
open AffineWhitening SeedOrbit LScalarGeometric DeterministicLineSearch
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Review20IdentityFailureTarget (F : Vec 2 → ℝ) : Prop :=
  ∃R : ℕ → AdmissibleBFGSRun 2 F,
    (∀m,(R m).H 0=1) ∧ Tendsto (fun m => (R m).x 0) atTop (𝓝 (0 : Vec 2)) ∧
    (∀m,(R m).c₁=1/10000 ∧ (R m).c₂=1/2 ∧
      Tendsto (R m).x atTop (𝓝 (failureCenter m)) ∧
      Tendsto (R m).H atTop (𝓝 0) ∧
      Tendsto (fun k => F ((R m).x k)) atTop (𝓝 ((scale m)^2*LEmbedding.offset)) ∧
      0<(scale m)^2*LEmbedding.offset ∧
      (0 : Vec 2)∉ConvexSubdifferential.subdifferential F (failureCenter m) ∧
      (∀k,(scale m)^2*LEmbedding.offset<F ((R m).x k) ∧
        F ((R m).x (k+1))<F ((R m).x k) ∧ (R m).α k=length (phase k) ∧
        fromMetric F ((R m).x k) ((R m).H k) (1/10000) (1/2) 5=
          (some ((R m).α k),trialHistory (phase k)) ∧
        F ((R m).x (k+1))<F ((R m).x k)+
          (1/10000)*dot ((R m).g k) (bfgsStep ((R m).H k) ((R m).g k) ((R m).α k)) ∧
        (1/2)*dot ((R m).g k) (bfgsStep ((R m).H k) ((R m).g k) ((R m).α k))<
          dot ((R m).g (k+1)) (bfgsStep ((R m).H k) ((R m).g k) ((R m).α k))) ∧
      (∀k q,trialPhase q=phase k →
        DifferentiableAt ℝ F ((R m).x k+trialLength q • bfgsStep ((R m).H k) ((R m).g k) 1) ∧
        0<F ((R m).x k+trialLength q • bfgsStep ((R m).H k) ((R m).g k) 1)) ∧
      ∀q : ℕ → Fin 9,(∀k,trialPhase (q k)=phase k) →
        Tendsto (fun k => (R m).x k+trialLength (q k) • bfgsStep ((R m).H k) ((R m).g k) 1)
          atTop (𝓝 (failureCenter m))) ∧
    ∀U : Set (Vec 2),U∈𝓝 (0 : Vec 2) → ∃N : ℕ,∀m≥N,∀k,(R m).x k∈U ∧
      ∀q : Fin 9,trialPhase q=phase k →
        (R m).x k+trialLength q • bfgsStep ((R m).H k) ((R m).g k) 1∈U

end BfgsVerification.LWhitening


namespace BfgsVerification.LWhitening
open AffineWhitening AffineProjection EnergyIdentities

def Review20ObjectiveGeometryTarget (F : Vec 2 → ℝ) : Prop :=
  ConvexOn ℝ univ F ∧ FixedNormal.EuclideanStrongConvexOn univ lowerConstant F ∧
    F 0=0 ∧ (∀x,lowerConstant/2*sqNorm x≤F x) ∧ (∀x,F x=0→x=0) ∧
    (∀a,IsCompact {x | F x≤a}) ∧ Tendsto F (cocompact (Vec 2)) atTop ∧
    ¬DifferentiableAt ℝ F (0 : Vec 2)

def Review20SmoothLocalFailureTarget : Prop :=
  0<lowerConstant ∧ lowerConstant≤upperConstant ∧ Review20ObjectiveGeometryTarget smoothObjective ∧
    (∀i : Fin 4,ContDiff ℝ 1 (smoothBranch i) ∧
      FixedNormal.EuclideanStrongConvexOn univ lowerConstant (smoothBranch i) ∧
      (∀z,HasFDerivAt (smoothBranch i) (gradientFunctional (smoothGradient i z)) z) ∧
      ∀x y,sqNorm (smoothGradient i x-smoothGradient i y)≤upperConstant^2*sqNorm (x-y)) ∧
    (∀x,smoothObjective x=Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 4 => smoothBranch i x)) ∧
    (∀x : Vec 2,(∀ᶠ z in 𝓝 x,DifferentiableAt ℝ smoothObjective z) →
      DifferentiableAt ℝ (fderiv ℝ smoothObjective) x →
      (RadialHessian.matrix smoothObjective x).IsSymm ∧ ∀v,
        lowerConstant*sqNorm v≤dot v ((RadialHessian.matrix smoothObjective x).mulVec v) ∧
        dot v ((RadialHessian.matrix smoothObjective x).mulVec v)≤upperConstant*sqNorm v) ∧
    Review20IdentityFailureTarget smoothObjective ∧ Tendsto failureCenter atTop (𝓝 (0 : Vec 2))

def Review20StepLocalFailureTarget : Prop :=
  0<lowerConstant ∧ lowerConstant≤upperConstant ∧ Review20ObjectiveGeometryTarget stepObjective ∧
    fixedHessian.PosDef ∧
    (∀x : Vec 2,DifferentiableAt ℝ stepObjective x →
      DifferentiableAt ℝ (fderiv ℝ stepObjective) x ∧
      RadialHessian.matrix stepObjective x=fixedHessian ∧ ∀v,
        lowerConstant*sqNorm v≤dot v ((RadialHessian.matrix stepObjective x).mulVec v) ∧
        dot v ((RadialHessian.matrix stepObjective x).mulVec v)≤upperConstant*sqNorm v) ∧
    Countable LStepEmbedding.CountableIndex ∧
    (∀x,IsGreatest (range (fun j => stepAffine j x+LStepEmbedding.countableOffset j)) (stepResidual x)) ∧
    (∀x,stepObjective x=metricEnergy fixedHessian x/2+stepResidual x) ∧
    Review20IdentityFailureTarget stepObjective ∧ Tendsto failureCenter atTop (𝓝 (0 : Vec 2))

theorem review20SmoothLocalFailure : Review20SmoothLocalFailureTarget := smoothLocalFailure

theorem review20StepLocalFailure : Review20StepLocalFailureTarget := stepLocalFailure

end BfgsVerification.LWhitening


namespace BfgsVerification.LReturnStableGraph
open LNormalizedReturn AnalyticStableGraph

def Review20LStableInvariantManifoldTarget : Prop := ∀ (μ : ℝ) (W : Set State), W∈𝓝 seed →
    ∃ E : LBlockSplitting.Coordinates ≃L[ℝ] State,
    ∃ h : Vec 2 → Vec 3, ∃ V : Set (Vec 2), IsOpen V ∧ (0 : Vec 2)∈V ∧
      chart seed E h 0=seed ∧ ContDiffOn ℝ ∞ (chart seed E h) V ∧
      Topology.IsEmbedding (fun a : V => chart seed E h a) ∧
      HasFDerivAt (chart seed E h)
        (E.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 3))) 0 ∧
      Module.finrank ℝ (LinearMap.range
        (E.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 3))).toLinearMap)=2 ∧
      (LinearMap.range
        (E.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 3))).toLinearMap : Set State)=
        linearStableSet (fderiv ℝ (returnMap μ) seed) ∧
      (∀ eps : ℝ, 0<eps → ∃ a∈V, 0<scale (chart seed E h a) ∧ scale (chart seed E h a)<eps) ∧
      (∀ a∈V, ∃ w : ℕ → State, w 0=chart seed E h a ∧
        (∀ n, w n∈W) ∧ Tendsto w atTop (𝓝 seed) ∧ ∀ n, w (n+1)=returnMap μ (w n)) ∧
      ∃ V₀ : Set (Vec 2), IsOpen V₀ ∧ (0 : Vec 2)∈V₀ ∧ V₀⊆V ∧
        ∀ a∈V₀, ∃ b∈V, returnMap μ (chart seed E h a)=chart seed E h b

theorem review20LStableInvariantManifold : Review20LStableInvariantManifoldTarget := lStableInvariantManifold

end BfgsVerification.LReturnStableGraph


namespace BfgsVerification.DEmbedding
/-- The actual objective, initial states, accepted iterates, stored matrices,
gradients and accepted lengths do not change with the allowed line-search
parameters. This is equality of the constructed functions, before using limits. -/
theorem review20ParameterIndependence {n : ℕ} (hn : 1≤n)
    (c₁ c₂ d₁ d₂ : ℝ) (hc₁ : 0<c₁) (hc₁' : c₁≤1/3)
    (hc : c₁<c₂) (hc₂ : c₂<1) (hd₁ : 0<d₁) (hd₁' : d₁≤1/3)
    (hd : d₁<d₂) (hd₂ : d₂<1) :
    let R := run hn c₁ c₂ hc₁ hc₁' hc hc₂
    let S := run hn d₁ d₂ hd₁ hd₁' hd hd₂
    R.x=S.x ∧ R.H=S.H ∧ R.g=S.g ∧ R.α=S.α := by
  exact ⟨rfl,rfl,rfl,rfl⟩
end BfgsVerification.DEmbedding


/- The following checks use strict definitional equality of the actual theorem
TYPE and the frozen literal proposition. A proof search or propositionally
implied weaker statement cannot make a check pass. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.DEmbedding.objectiveGeometry
  let expected ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.DEmbedding.Review20ObjectiveGeometryTarget
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType actual) expected do
    throwError "NEGATIVE_STRICT_FAIL|BfgsVerification.DEmbedding.objectiveGeometry"
  Lean.logInfo "NEGATIVE_STRICT_PASS|BfgsVerification.DEmbedding.objectiveGeometry|BfgsVerification.DEmbedding.Review20ObjectiveGeometryTarget"

run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.DEmbedding.embeddingFailure
  let expected ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.DEmbedding.Review20EmbeddingFailureTarget
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType actual) expected do
    throwError "NEGATIVE_STRICT_FAIL|BfgsVerification.DEmbedding.embeddingFailure"
  Lean.logInfo "NEGATIVE_STRICT_PASS|BfgsVerification.DEmbedding.embeddingFailure|BfgsVerification.DEmbedding.Review20EmbeddingFailureTarget"

run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.DLiteralTargets.nonStrictRun
  let expected ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.DLiteralTargets.Review20NonStrictRunTarget
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType actual) expected do
    throwError "NEGATIVE_STRICT_FAIL|BfgsVerification.DLiteralTargets.nonStrictRun"
  Lean.logInfo "NEGATIVE_STRICT_PASS|BfgsVerification.DLiteralTargets.nonStrictRun|BfgsVerification.DLiteralTargets.Review20NonStrictRunTarget"

run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.LQuadraticSeed.quadraticSeed
  let expected ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.LQuadraticSeed.Review20QuadraticSeedTarget
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType actual) expected do
    throwError "NEGATIVE_STRICT_FAIL|BfgsVerification.LQuadraticSeed.quadraticSeed"
  Lean.logInfo "NEGATIVE_STRICT_PASS|BfgsVerification.LQuadraticSeed.quadraticSeed|BfgsVerification.LQuadraticSeed.Review20QuadraticSeedTarget"

run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.LGlobalTargets.globalFailure
  let expected ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.LGlobalTargets.Review20GlobalFailureTarget
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType actual) expected do
    throwError "NEGATIVE_STRICT_FAIL|BfgsVerification.LGlobalTargets.globalFailure"
  Lean.logInfo "NEGATIVE_STRICT_PASS|BfgsVerification.LGlobalTargets.globalFailure|BfgsVerification.LGlobalTargets.Review20GlobalFailureTarget"

run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.LGlobalTargets.spectrum
  let expected ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.LGlobalTargets.Review20SpectrumTarget
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType actual) expected do
    throwError "NEGATIVE_STRICT_FAIL|BfgsVerification.LGlobalTargets.spectrum"
  Lean.logInfo "NEGATIVE_STRICT_PASS|BfgsVerification.LGlobalTargets.spectrum|BfgsVerification.LGlobalTargets.Review20SpectrumTarget"

run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.LGlobalTargets.localInverse
  let expected ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.LGlobalTargets.Review20LocalInverseTarget
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType actual) expected do
    throwError "NEGATIVE_STRICT_FAIL|BfgsVerification.LGlobalTargets.localInverse"
  Lean.logInfo "NEGATIVE_STRICT_PASS|BfgsVerification.LGlobalTargets.localInverse|BfgsVerification.LGlobalTargets.Review20LocalInverseTarget"

run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.LWhitening.smoothLocalFailure
  let expected ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.LWhitening.Review20SmoothLocalFailureTarget
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType actual) expected do
    throwError "NEGATIVE_STRICT_FAIL|BfgsVerification.LWhitening.smoothLocalFailure"
  Lean.logInfo "NEGATIVE_STRICT_PASS|BfgsVerification.LWhitening.smoothLocalFailure|BfgsVerification.LWhitening.Review20SmoothLocalFailureTarget"

run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.LWhitening.stepLocalFailure
  let expected ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.LWhitening.Review20StepLocalFailureTarget
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType actual) expected do
    throwError "NEGATIVE_STRICT_FAIL|BfgsVerification.LWhitening.stepLocalFailure"
  Lean.logInfo "NEGATIVE_STRICT_PASS|BfgsVerification.LWhitening.stepLocalFailure|BfgsVerification.LWhitening.Review20StepLocalFailureTarget"

run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.LReturnStableGraph.lStableInvariantManifold
  let expected ← Lean.Meta.mkConstWithFreshMVarLevels `BfgsVerification.LReturnStableGraph.Review20LStableInvariantManifoldTarget
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType actual) expected do
    throwError "NEGATIVE_STRICT_FAIL|BfgsVerification.LReturnStableGraph.lStableInvariantManifold"
  Lean.logInfo "NEGATIVE_STRICT_PASS|BfgsVerification.LReturnStableGraph.lStableInvariantManifold|BfgsVerification.LReturnStableGraph.Review20LStableInvariantManifoldTarget"

#check BfgsVerification.DEmbedding.Review20ObjectiveGeometryTarget
#print axioms BfgsVerification.DEmbedding.Review20ObjectiveGeometryTarget

#check BfgsVerification.DEmbedding.Review20EmbeddingFailureTarget
#print axioms BfgsVerification.DEmbedding.Review20EmbeddingFailureTarget

#check BfgsVerification.DEmbedding.review20ObjectiveGeometry
#print axioms BfgsVerification.DEmbedding.review20ObjectiveGeometry

#check BfgsVerification.DEmbedding.review20EmbeddingFailure
#print axioms BfgsVerification.DEmbedding.review20EmbeddingFailure

#check BfgsVerification.DLiteralTargets.Review20NonStrictRunTarget
#print axioms BfgsVerification.DLiteralTargets.Review20NonStrictRunTarget

#check BfgsVerification.DLiteralTargets.review20NonStrictRun
#print axioms BfgsVerification.DLiteralTargets.review20NonStrictRun

#check BfgsVerification.LQuadraticSeed.Review20QuadraticSeedTarget
#print axioms BfgsVerification.LQuadraticSeed.Review20QuadraticSeedTarget

#check BfgsVerification.LQuadraticSeed.review20QuadraticSeed
#print axioms BfgsVerification.LQuadraticSeed.review20QuadraticSeed

#check BfgsVerification.LGlobalTargets.Review20GlobalFailureTarget
#print axioms BfgsVerification.LGlobalTargets.Review20GlobalFailureTarget

#check BfgsVerification.LGlobalTargets.Review20SpectrumTarget
#print axioms BfgsVerification.LGlobalTargets.Review20SpectrumTarget

#check BfgsVerification.LGlobalTargets.Review20LocalInverseTarget
#print axioms BfgsVerification.LGlobalTargets.Review20LocalInverseTarget

#check BfgsVerification.LGlobalTargets.review20GlobalFailure
#print axioms BfgsVerification.LGlobalTargets.review20GlobalFailure

#check BfgsVerification.LGlobalTargets.review20Spectrum
#print axioms BfgsVerification.LGlobalTargets.review20Spectrum

#check BfgsVerification.LGlobalTargets.review20LocalInverse
#print axioms BfgsVerification.LGlobalTargets.review20LocalInverse

#check BfgsVerification.LWhitening.Review20IdentityFailureTarget
#print axioms BfgsVerification.LWhitening.Review20IdentityFailureTarget

#check BfgsVerification.LWhitening.Review20ObjectiveGeometryTarget
#print axioms BfgsVerification.LWhitening.Review20ObjectiveGeometryTarget

#check BfgsVerification.LWhitening.Review20SmoothLocalFailureTarget
#print axioms BfgsVerification.LWhitening.Review20SmoothLocalFailureTarget

#check BfgsVerification.LWhitening.Review20StepLocalFailureTarget
#print axioms BfgsVerification.LWhitening.Review20StepLocalFailureTarget

#check BfgsVerification.LWhitening.review20SmoothLocalFailure
#print axioms BfgsVerification.LWhitening.review20SmoothLocalFailure

#check BfgsVerification.LWhitening.review20StepLocalFailure
#print axioms BfgsVerification.LWhitening.review20StepLocalFailure

#check BfgsVerification.LReturnStableGraph.Review20LStableInvariantManifoldTarget
#print axioms BfgsVerification.LReturnStableGraph.Review20LStableInvariantManifoldTarget

#check BfgsVerification.LReturnStableGraph.review20LStableInvariantManifold
#print axioms BfgsVerification.LReturnStableGraph.review20LStableInvariantManifold

#check BfgsVerification.DEmbedding.review20ParameterIndependence
#print axioms BfgsVerification.DEmbedding.review20ParameterIndependence

run_cmd Lean.Elab.Command.liftTermElabM do
  let names : List Lean.Name := [
    `BfgsVerification.DEmbedding.Review20ObjectiveGeometryTarget,
    `BfgsVerification.DEmbedding.Review20EmbeddingFailureTarget,
    `BfgsVerification.DEmbedding.review20ObjectiveGeometry,
    `BfgsVerification.DEmbedding.review20EmbeddingFailure,
    `BfgsVerification.DLiteralTargets.Review20NonStrictRunTarget,
    `BfgsVerification.DLiteralTargets.review20NonStrictRun,
    `BfgsVerification.LQuadraticSeed.Review20QuadraticSeedTarget,
    `BfgsVerification.LQuadraticSeed.review20QuadraticSeed,
    `BfgsVerification.LGlobalTargets.Review20GlobalFailureTarget,
    `BfgsVerification.LGlobalTargets.Review20SpectrumTarget,
    `BfgsVerification.LGlobalTargets.Review20LocalInverseTarget,
    `BfgsVerification.LGlobalTargets.review20GlobalFailure,
    `BfgsVerification.LGlobalTargets.review20Spectrum,
    `BfgsVerification.LGlobalTargets.review20LocalInverse,
    `BfgsVerification.LWhitening.Review20IdentityFailureTarget,
    `BfgsVerification.LWhitening.Review20ObjectiveGeometryTarget,
    `BfgsVerification.LWhitening.Review20SmoothLocalFailureTarget,
    `BfgsVerification.LWhitening.Review20StepLocalFailureTarget,
    `BfgsVerification.LWhitening.review20SmoothLocalFailure,
    `BfgsVerification.LWhitening.review20StepLocalFailure,
    `BfgsVerification.LReturnStableGraph.Review20LStableInvariantManifoldTarget,
    `BfgsVerification.LReturnStableGraph.review20LStableInvariantManifold,
    `BfgsVerification.DEmbedding.review20ParameterIndependence,
    `BfgsVerification.DEmbedding.objectiveGeometry,
    `BfgsVerification.DEmbedding.embeddingFailure,
    `BfgsVerification.DLiteralTargets.nonStrictRun,
    `BfgsVerification.LQuadraticSeed.quadraticSeed,
    `BfgsVerification.LGlobalTargets.globalFailure,
    `BfgsVerification.LGlobalTargets.spectrum,
    `BfgsVerification.LGlobalTargets.localInverse,
    `BfgsVerification.LWhitening.smoothLocalFailure,
    `BfgsVerification.LWhitening.stepLocalFailure,
    `BfgsVerification.LReturnStableGraph.lStableInvariantManifold,
    `BfgsVerification.DEmbedding.actualData,
    `BfgsVerification.DEmbedding.actualOracleData,
    `BfgsVerification.DEmbedding.run,
    `BfgsVerification.SeedEmbedding.run,
    `BfgsVerification.LReturnStableOrbit.source_positive_return_orbit,
    `BfgsVerification.LReturnStableOrbit.source_oracle_orbit,
    `BfgsVerification.LReturnStableGraph.source_splitting,
    `BfgsVerification.LReturnStableGraph.source_smooth_stable_graph,
    `BfgsVerification.LGlobalFailure.actual_orbit_data,
    `BfgsVerification.LSeedCopies.data,
    `BfgsVerification.LSeedCopies.data_spec,
    `BfgsVerification.LActualCopies.smoothData,
    `BfgsVerification.LActualCopies.stepData,
    `BfgsVerification.LWhitening.initialMetric,
    `BfgsVerification.LWhitening.coordinateMatrix,
    `BfgsVerification.LWhitening.failureFamily,
    `BfgsVerification.DeterministicLineSearch.actual_coordinateGradient,
    `BfgsVerification.LNormalizedOracle.Conditions.physical_reject]
  for n in names do
    let actual ← Lean.Meta.mkConstWithFreshMVarLevels n
    let ty ← Lean.Meta.inferType actual
    let axioms ← Lean.collectAxioms n
    let j := Lean.Json.mkObj [("name",Lean.toJson n.toString),
      ("type",Lean.toJson (toString (← Lean.Meta.ppExpr ty))),
      ("axioms",Lean.toJson (axioms.toList.map Lean.Name.toString))]
    Lean.logInfo ("NEGATIVE_REPORT|" ++ j.compress)
  Lean.logInfo "NEGATIVE_AUDIT_COMPLETE"
