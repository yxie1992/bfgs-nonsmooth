import BfgsVerification.LReturnStableGraph
import BfgsVerification.StableGraphEmbedding

noncomputable section
open scoped Topology ContDiff
open Set Filter
namespace BfgsVerification.LReturnStableGraph
open LNormalizedReturn AnalyticStableGraph

theorem positive_parameter_in_neighborhood {V : Set (Vec 2)} (hV : V∈𝓝 (0 : Vec 2))
    {eps : ℝ} (heps : 0<eps) : ∃ a∈V, 0<a 1 ∧ a 1<eps := by
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hV
  let e : Vec 2 := ![0,1]
  let r := min R (eps/2)
  let t := r/(‖e‖+1)
  have hr : 0<r := lt_min hR (half_pos heps)
  have hd : 0<‖e‖+1 := by positivity
  have ht : 0<t := div_pos hr hd
  have heq : t*(‖e‖+1)=r := div_mul_cancel₀ _ hd.ne'
  have hnorm : ‖t • e‖<R := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    have hrR : r≤R := min_le_left _ _
    nlinarith
  have hteps : t<eps := by
    have hre : r≤eps/2 := min_le_right _ _
    have hn := norm_nonneg e
    nlinarith
  refine ⟨t • e,hball (by simpa only [Metric.mem_ball,dist_zero_right] using hnorm),?_,?_⟩
  · simpa [e] using ht
  · simpa [e] using hteps

/-- Literal geometric contract: an actual smooth embedded two-dimensional
graph through the actual fixed point, with tangent equal to the actual stable
set of the derivative, containing positive physical scales and consisting of
actual forward orbits in every prescribed neighborhood. -/
def LStableManifoldTarget : Prop := ∀ (μ : ℝ) (W : Set State), W∈𝓝 seed →
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
      ∀ a∈V, ∃ w : ℕ → State, w 0=chart seed E h a ∧
        (∀ n, w n∈W) ∧ Tendsto w atTop (𝓝 seed) ∧ ∀ n, w (n+1)=returnMap μ (w n)

theorem lStableManifold : LStableManifoldTarget := by
  intro μ W hW
  obtain ⟨E,hscale,A,L,hA,hL,hconj,h,V,hV,hV0,h0,hc,hd,hchart,hchartd,hs,hsol⟩ :=
    source_smooth_stable_graph μ W hW
  refine ⟨E,h,V,hV,hV0,?_,hchart,chart_isEmbedding seed E hc,hchartd,?_,
    stable_inclusion_range _ E A L hA hL hconj,?_,hsol⟩
  · simp [chart,h0]
  · simpa using stable_inclusion_dimension E
  · intro eps heps
    obtain ⟨a,ha,ha0,hae⟩ := positive_parameter_in_neighborhood (hV.mem_nhds hV0) heps
    exact ⟨a,ha,by rwa [hs],by rwa [hs]⟩

end BfgsVerification.LReturnStableGraph
