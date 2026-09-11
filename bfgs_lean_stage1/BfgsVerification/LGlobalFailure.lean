import BfgsVerification.LReturnStableOrbit
import BfgsVerification.LFlattenNeighborhood

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.LGlobalFailure
open SeedOrbit SeedCycle LNormalizedReturn DeterministicLineSearch
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem actual_orbit_data (μ c₁ c₂ : ℝ) (hc₁ : 0<c₁) (hc₁' : c₁≤1/3) (hc₂ : 0<c₂)
    (U : Set (Vec 2)) (hU : U∈𝓝 (0 : Vec 2)) :
    ∃ D : LFlatten.Data μ c₁ c₂,
      Tendsto D.state atTop (𝓝 seed) ∧
      (∀ k, D.x k∈U) ∧
      (∀ k q, trialPhase q=phase k →
        D.x k+trialLength q • bfgsStep (D.H k) (D.g k) 1∈U) := by
  obtain ⟨V,hVo,hVs,hV⟩ := LFlatten.physical_neighborhood μ U hU
  obtain ⟨w,hw,ht,hp,hc,hn⟩ := LReturnStableOrbit.source_oracle_orbit μ c₁ c₂
    hc₁ hc₁' hc₂ V (hVo.mem_nhds hVs)
  let D : LFlatten.Data μ c₁ c₂ := ⟨w,hp,hc,hn⟩
  exact ⟨D,ht,D.whole_run_in_neighborhood hw hV⟩

/-- An actual infinite full-BFGS trajectory, with no assumed orbit, iterate limit,
matrix limit, or spectral hypothesis. Every accepted and rejected physical
query lies in the arbitrarily prescribed neighborhood of the nonstationary origin. -/
theorem actual_global_failure {μ c₁ c₂ : ℝ} (hμ : 0<μ)
    (hc₁ : 0<c₁) (hc₁' : c₁≤1/3) (hc : c₁<c₂) (hc₂ : c₂<1)
    (U : Set (Vec 2)) (hU : U∈𝓝 (0 : Vec 2)) :
    ∃ R : AdmissibleBFGSRun 2 (LQuadraticSeed.objective μ),
      R.c₁=c₁ ∧ R.c₂=c₂ ∧
      Tendsto R.x atTop (𝓝 0) ∧ Tendsto R.H atTop (𝓝 0) ∧
      Tendsto (fun k => LQuadraticSeed.objective μ (R.x k)) atTop (𝓝 0) ∧
      (∀ k, 0<LQuadraticSeed.objective μ (R.x k)) ∧
      (∀ k, LQuadraticSeed.objective μ (R.x (k+1))<LQuadraticSeed.objective μ (R.x k)) ∧
      (∀ k, R.α k=length (phase k)) ∧
      (∀ k, fromMetric (LQuadraticSeed.objective μ) (R.x k) (R.H k) c₁ c₂ 5=
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
          c₁*dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) ∧
        c₂*dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k))<
          dot (R.g (k+1)) (bfgsStep (R.H k) (R.g k) (R.α k))) ∧
      (0 : Vec 2)∉ConvexSubdifferential.subdifferential (LQuadraticSeed.objective μ) 0 := by
  obtain ⟨D,ht,hp,hq⟩ := actual_orbit_data μ c₁ c₂ hc₁ hc₁' (hc₁.trans hc) U hU
  obtain ⟨hx,hH,hv,hpos,hdec,hsearch,hdiff,hqt,hnon⟩ := D.failure_contract hμ.le hc₁ hc hc₂ ht
  refine ⟨D.run hμ.le hc₁ hc hc₂,rfl,rfl,hx,hH,hv,hpos,hdec,fun _ => rfl,
    hsearch,hp,?_,hqt,D.strict_accept,hnon⟩
  intro k q hphase
  exact ⟨hdiff k q hphase,D.all_trial_values_positive k q hphase,hq k q hphase⟩

/-- Literal source line-search parameters, with every query in any prescribed
physical neighborhood. The concrete objective geometry is separately proved
in LQuadraticSeed.quadratic_seed_contract. -/
theorem source_global_failure {μ : ℝ} (hμ : 0<μ) (U : Set (Vec 2)) (hU : U∈𝓝 (0 : Vec 2)) :
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
      (0 : Vec 2)∉ConvexSubdifferential.subdifferential (LQuadraticSeed.objective μ) 0 :=
  actual_global_failure hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) U hU

end BfgsVerification.LGlobalFailure
