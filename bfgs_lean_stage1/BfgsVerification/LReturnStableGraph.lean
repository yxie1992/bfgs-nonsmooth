import BfgsVerification.StableGraphCoordinates
import BfgsVerification.LReturnStableOrbit

noncomputable section
open scoped Topology ContDiff
open Set Filter
namespace BfgsVerification.LReturnStableGraph
open LNormalizedReturn LBlockSplitting SeedOrbit LShapeDerivative LShapeSpectrum LShapeSpectralAlgebra

theorem source_splitting (μ : ℝ) :
    ∃ E : Coordinates ≃L[ℝ] LNormalizedReturn.State, (∀ z, E z 4=z.1 1) ∧
      ∃ A : Vec 2 →L[ℝ] Vec 2, ∃ L : Vec 3 ≃L[ℝ] Vec 3,
        ‖A‖<1 ∧ ‖L.symm.toContinuousLinearMap‖<1 ∧
        (fderiv ℝ (returnMap μ) seed).comp E.toContinuousLinearMap=
          E.toContinuousLinearMap.comp (A.prodMap L.toContinuousLinearMap) := by
  obtain ⟨ls,lu,hs,hu,hsroot,huroot,hfactor⟩ := source_shape_roots
  have hr := tight_ratio root_tight_box.1 root_tight_box.2
  have hs0 : 0<ls := by linarith [hs.1]
  have hsr : ls<seedRatio := by linarith [hs.2,hr.1]
  have hu1 : 1<lu := by linarith [hu.1]
  have hr2 : 2<1/seedRatio := (lt_div_iff₀ source_ratio_pos_lt_one.1).mpr (by linarith [hr.2])
  rw [one_div] at hr2
  have hua : lu<seedRatio⁻¹ := by linarith [hu.2]
  apply block_splitting (LReturnOrbitCore.actual_block μ)
    source_ratio_pos_lt_one.1 source_ratio_pos_lt_one.2 hs0 hsr hu1 hua
    source_jacobian_offdiag_positive.ne'
  · dsimp [characteristic] at hsroot
    nlinarith
  · dsimp [characteristic] at huroot
    nlinarith

/-- The literal return map has an actual smooth two-parameter stable graph.
Its parameterization derivative is the checked stable-coordinate inclusion,
and the physical scale is exactly the second parameter. -/
theorem source_smooth_stable_graph (μ : ℝ) (W : Set LNormalizedReturn.State) (hW : W∈𝓝 seed) :
    ∃ E : Coordinates ≃L[ℝ] LNormalizedReturn.State, (∀ z, E z 4=z.1 1) ∧
      ∃ A : Vec 2 →L[ℝ] Vec 2, ∃ L : Vec 3 ≃L[ℝ] Vec 3,
        ‖A‖<1 ∧ ‖L.symm.toContinuousLinearMap‖<1 ∧
        (fderiv ℝ (returnMap μ) seed).comp E.toContinuousLinearMap=
          E.toContinuousLinearMap.comp (A.prodMap L.toContinuousLinearMap) ∧
      ∃ h : Vec 2 → Vec 3, ∃ V : Set (Vec 2), IsOpen V ∧ (0 : Vec 2)∈V ∧ h 0=0 ∧
        ContDiffOn ℝ ∞ h V ∧ HasFDerivAt h (0 : Vec 2 →L[ℝ] Vec 3) 0 ∧
        ContDiffOn ℝ ∞ (AnalyticStableGraph.chart seed E h) V ∧
        HasFDerivAt (AnalyticStableGraph.chart seed E h)
          (E.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 3))) 0 ∧
        (∀ a, scale (AnalyticStableGraph.chart seed E h a)=a 1) ∧
        ∀ a∈V, ∃ w : ℕ → LNormalizedReturn.State, w 0=AnalyticStableGraph.chart seed E h a ∧
          (∀ n, w n∈W) ∧ Tendsto w atTop (𝓝 seed) ∧ ∀ n, w (n+1)=returnMap μ (w n) := by
  obtain ⟨E,hscale,A,L,hA,hL,hconj⟩ := source_splitting μ
  obtain ⟨h,V,hV,hV0,h0,hc,hd,hchart,hchartd,hsol⟩ :=
    AnalyticStableGraph.exists_smooth_graph_of_splitting (analytic_returnMap_seed μ)
      (seed_fixed μ) (LReturnOrbitCore.return_hasStrictFDerivAt μ).hasFDerivAt E A L hA hL hconj W hW
  refine ⟨E,hscale,A,L,hA,hL,hconj,h,V,hV,hV0,h0,hc,hd,hchart,hchartd,?_,hsol⟩
  intro a
  change seed 4+E (a,h a) 4=a 1
  rw [hscale]
  have hs : seed 4=0 := seed_scale
  rw [hs,zero_add]

end BfgsVerification.LReturnStableGraph
