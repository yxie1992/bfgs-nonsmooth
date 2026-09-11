import BfgsVerification.DEmbeddingCenter

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.DEmbedding
open SeedCycle SeedOrbit DScalarGeometric DeterministicLineSearch

/-- The actual fixed objective, source centers, full matrices, and deterministic
oracle produce bad starts arbitrarily close to the unique minimizer. All
convergence conclusions are derived from the displayed concrete trajectory. -/
theorem deterministic_embedding_failure :
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
        R.α (3*m+j.val)=length j)) := by
  refine ⟨initial_points_tendsto, initial_values_tendsto, ?_,
    fun V hV => trajectories_uniformly_small hV, ?_⟩
  · intro n
    exact ⟨center_ne_zero n, center_value n, center_positive n,
      center_nonstationary n, center_directional_derivative n⟩
  · intro c₁ c₂ hc₁ hc₁' hc hc₂ n hn
    exact ⟨run_initial_matrix hn hc₁ hc₁' hc hc₂,
      (run hn c₁ c₂ hc₁ hc₁' hc hc₂).positive_definite,
      run_point_tendsto hn hc₁ hc₁' hc hc₂, run_value_tendsto hn hc₁ hc₁' hc hc₂,
      run_value_above_center hn hc₁ hc₁' hc hc₂, run_value_strict_decrease hn hc₁ hc₁' hc hc₂,
      run_search hn hc₁ hc₁' hc hc₂, fun k => trialHistory_length_le (phase k),
      run_all_trials_differentiable hn hc₁ hc₁' hc hc₂, run_phase_parameters hn hc₁ hc₁' hc hc₂⟩

end BfgsVerification.DEmbedding
