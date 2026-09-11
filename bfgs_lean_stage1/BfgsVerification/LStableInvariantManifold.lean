import BfgsVerification.LStableManifoldTargets
import BfgsVerification.InvariantGraphCoordinates

noncomputable section
open scoped Topology ContDiff
open Set Filter
namespace BfgsVerification.LReturnStableGraph
open LNormalizedReturn AnalyticStableGraph

def LStableInvariantManifoldTarget : Prop := ∀ (μ : ℝ) (W : Set State), W∈𝓝 seed →
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

/-- The literal source stable manifold, including explicit local forward
invariance of the same smooth embedded graph. -/
theorem lStableInvariantManifold : LStableInvariantManifoldTarget := by
  intro μ W hW
  obtain ⟨E,hscale,A,L,hA,hL,hconj⟩ := source_splitting μ
  obtain ⟨h,V,hV,hV0,h0,hc,hd,hchart,hchartd,hsol,hInv⟩ :=
    exists_smooth_invariant_graph_of_splitting (analytic_returnMap_seed μ)
      (seed_fixed μ) (LReturnOrbitCore.return_hasStrictFDerivAt μ).hasFDerivAt E A L hA hL hconj W hW
  have hs (a : Vec 2) : scale (chart seed E h a)=a 1 := by
    change seed 4+E (a,h a) 4=a 1
    rw [hscale]
    have hz : seed 4=0 := seed_scale
    rw [hz,zero_add]
  refine ⟨E,h,V,hV,hV0,?_,hchart,chart_isEmbedding seed E hc,hchartd,?_,
    stable_inclusion_range _ E A L hA hL hconj,?_,hsol,hInv⟩
  · simp [chart,h0]
  · simpa using stable_inclusion_dimension E
  · intro eps heps
    obtain ⟨a,ha,ha0,hae⟩ := positive_parameter_in_neighborhood (hV.mem_nhds hV0) heps
    exact ⟨a,ha,by rwa [hs],by rwa [hs]⟩

end BfgsVerification.LReturnStableGraph
