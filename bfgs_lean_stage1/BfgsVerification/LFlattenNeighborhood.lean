import BfgsVerification.LFlattenLimits

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.LFlatten
open SeedOrbit SeedCycle LNormalizedReturn LNormalizedOracle DeterministicLineSearch
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- One normalized neighborhood controls all physical accepted phases and all
nine actual queries. No uniform-in-time trajectory estimate is assumed. -/
theorem physical_neighborhood (μ : ℝ) (U : Set (Vec 2)) (hU : U∈𝓝 (0 : Vec 2)) :
    ∃ V : Set State, IsOpen V ∧ seed∈V ∧ ∀ w∈V,
      (∀ j, physicalPoint μ w j∈U) ∧ (∀ q, physicalQuery μ w q∈U) := by
  have hp : ∀ᶠ w in 𝓝 seed, ∀ j, physicalPoint μ w j∈U := by
    apply eventually_all.mpr
    intro j
    have hh : Tendsto (fun w => physicalPoint μ w j) (𝓝 seed) (𝓝 0) := by
      simpa only [physicalPoint,seed_scale,zero_smul] using (physicalPoint_continuous_seed μ j).tendsto
    exact hh hU
  have hq : ∀ᶠ w in 𝓝 seed, ∀ q, physicalQuery μ w q∈U := by
    apply eventually_all.mpr
    intro q
    have hh : Tendsto (fun w => physicalQuery μ w q) (𝓝 seed) (𝓝 0) := by
      simpa only [physicalQuery,seed_scale,zero_smul] using (physicalQuery_continuous_seed μ q).tendsto
    exact hh hU
  obtain ⟨V,hV,hVo,hs⟩ := mem_nhds_iff.mp (hp.and hq)
  exact ⟨V,hVo,hs,fun w hw => hV hw⟩

namespace Data
variable {μ c₁ c₂ : ℝ}

theorem phase_parameters (D : Data μ c₁ c₂) (m : ℕ) (j : Fin 3) :
    D.x (3*m+j.val)=physicalPoint μ (D.state m) j ∧
    D.H (3*m+j.val)=physicalMetric μ (D.state m) j ∧
    D.g (3*m+j.val)=phaseGradient μ (D.state m) j ∧ D.alpha (3*m+j.val)=length j := by
  have hp : period (3*m+j.val)=m := by dsimp [period]; omega
  have hj : phase (3*m+j.val)=j := by apply Fin.ext; dsimp [phase]; omega
  rw [D.gradient_eq]
  simp [x,H,alpha,hp,hj]

theorem whole_run_in_neighborhood (D : Data μ c₁ c₂) {U : Set (Vec 2)} {V : Set State}
    (hv : ∀ m, D.state m∈V)
    (hV : ∀ w∈V, (∀ j, physicalPoint μ w j∈U) ∧ (∀ q, physicalQuery μ w q∈U)) :
    (∀ k, D.x k∈U) ∧
    (∀ k q, trialPhase q=phase k → D.x k+trialLength q • bfgsStep (D.H k) (D.g k) 1∈U) := by
  refine ⟨fun k => (hV _ (hv (period k))).1 (phase k),?_⟩
  intro k q hq
  rw [D.actual_trial_eq k q hq]
  exact (hV _ (hv (period k))).2 q

/-- Every listed conclusion concerns the actual full-BFGS run. The normalized
sequence convergence premise is kept separate and must be supplied by dynamics. -/
theorem failure_contract (D : Data μ c₁ c₂) (hμ : 0≤μ) (hc₁ : 0<c₁) (hc : c₁<c₂) (hc₂ : c₂<1)
    (ht : Tendsto D.state atTop (𝓝 seed)) :
    let R := D.run hμ hc₁ hc hc₂
    Tendsto R.x atTop (𝓝 0) ∧ Tendsto R.H atTop (𝓝 0) ∧
    Tendsto (fun k => LQuadraticSeed.objective μ (R.x k)) atTop (𝓝 0) ∧
    (∀ k, 0<LQuadraticSeed.objective μ (R.x k)) ∧
    (∀ k, LQuadraticSeed.objective μ (R.x (k+1))<LQuadraticSeed.objective μ (R.x k)) ∧
    (∀ k, fromMetric (LQuadraticSeed.objective μ) (R.x k) (R.H k) c₁ c₂ 5=
      (some (R.α k),trialHistory (phase k))) ∧
    (∀ k q, trialPhase q=phase k → DifferentiableAt ℝ (LQuadraticSeed.objective μ)
      (R.x k+trialLength q • bfgsStep (R.H k) (R.g k) 1)) ∧
    (∀ q : ℕ → Fin 9, (∀ k, trialPhase (q k)=phase k) →
      Tendsto (fun k => R.x k+trialLength (q k) • bfgsStep (R.H k) (R.g k) 1) atTop (𝓝 0)) ∧
    (0 : Vec 2)∉ConvexSubdifferential.subdifferential (LQuadraticSeed.objective μ) 0 := by
  refine ⟨D.point_tendsto ht,D.metric_tendsto ht,D.value_tendsto hμ ht,D.value_positive,
    ?_,D.actual_search,?_,D.actual_trials_tendsto ht,LQuadraticSeed.origin_nonstationary hμ⟩
  · exact (D.run hμ hc₁ hc hc₂).objective_strict_decrease
  · intro k q hq
    exact (D.all_trial_derivatives k q hq).differentiableAt

end Data
end BfgsVerification.LFlatten
