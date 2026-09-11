import BfgsVerification.StableGraphCoordinates
import BfgsVerification.StableGraphInvariance

noncomputable section
open scoped Topology ContDiff
open Set Filter
namespace BfgsVerification.AnalyticStableGraph

variable {S U X : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem exists_smooth_invariant_graph_of_splitting {T : X → X} {P : X} {F : X →L[ℝ] X}
    (hT : AnalyticAt ℝ T P) (hfix : T P=P) (hd : HasFDerivAt T F P)
    (E : (S×U) ≃L[ℝ] X) (A : S →L[ℝ] S) (L : U ≃L[ℝ] U)
    (hA : ‖A‖<1) (hL : ‖L.symm.toContinuousLinearMap‖<1)
    (hconj : F.comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp (A.prodMap L.toContinuousLinearMap))
    (W : Set X) (hW : W∈𝓝 P) :
    ∃ h : S → U, ∃ V : Set S, IsOpen V ∧ (0 : S)∈V ∧ h 0=0 ∧
      ContDiffOn ℝ ∞ h V ∧ HasFDerivAt h (0 : S →L[ℝ] U) 0 ∧
      ContDiffOn ℝ ∞ (chart P E h) V ∧
      HasFDerivAt (chart P E h) (E.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ S U)) 0 ∧
      (∀ a∈V, ∃ w : ℕ → X, w 0=chart P E h a ∧ (∀ n, w n∈W) ∧
        Tendsto w atTop (𝓝 P) ∧ ∀ n, w (n+1)=T (w n)) ∧
      ∃ V₀ : Set S, IsOpen V₀ ∧ (0 : S)∈V₀ ∧ V₀⊆V ∧
        ∀ a∈V₀, ∃ b∈V, T (chart P E h a)=chart P E h b := by
  let D := A.prodMap L.toContinuousLinearMap
  let T' : S×U → S×U := fun z => E.symm (T (P+E z)-P)
  have hT0 : T' 0=0 := by simp [T',hfix]
  have hin : AnalyticAt ℝ (fun z : S×U => P+E z) 0 :=
    analyticAt_const.add (E.toContinuousLinearMap.analyticAt 0)
  have hTm : AnalyticAt ℝ (fun z : S×U => T (P+E z)-P) 0 :=
    (hT.comp_of_eq hin (by simp)).sub analyticAt_const
  have hT' : AnalyticAt ℝ T' 0 := (E.symm.toContinuousLinearMap.analyticAt _).comp hTm
  have hindi : HasFDerivAt (fun z : S×U => P+E z) E.toContinuousLinearMap 0 :=
    E.toContinuousLinearMap.hasFDerivAt.const_add P
  have hd' : HasFDerivAt T F (P+E 0) := by simpa using hd
  have hout := E.symm.toContinuousLinearMap.hasFDerivAt.comp (0 : S×U) ((hd'.comp (0 : S×U) hindi).sub_const P)
  have heq : E.symm.toContinuousLinearMap.comp (F.comp E.toContinuousLinearMap)=D := by
    apply ContinuousLinearMap.ext
    intro z
    have hh := congrArg (fun Q : (S×U) →L[ℝ] X => Q z) hconj
    change F (E z)=E (D z) at hh
    change E.symm (F (E z))=D z
    rw [hh,E.symm_apply_apply]
  have hTd : HasFDerivAt T' D 0 := hout.congr_fderiv heq
  have hW' : {z : S×U | P+E z∈W}∈𝓝 0 := by
    have ht : Tendsto (fun z : S×U => P+E z) (𝓝 0) (𝓝 P) := by
      simpa using (continuous_const.add E.continuous).continuousAt.tendsto (x := 0)
    exact ht hW
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp hW'
  obtain ⟨h,V,hV,hV0,h0,hc,hder,hsol,hInv⟩ := exists_smooth_locally_invariant_graph A L T' hT' hT0 hTd hA hL (half_pos heps)
  refine ⟨h,V,hV,hV0,h0,hc,hder,chart_contDiffOn P E hc,chart_hasFDerivAt P E hder,?_,?_⟩
  · intro a ha
    obtain ⟨w,hw0,hw,ht,hrec⟩ := hsol a ha
    refine ⟨fun n => P+E (w n),?_,?_,?_,?_⟩
    · change P+E (w 0)=chart P E h a
      rw [hw0]; rfl
    · intro n
      exact hball (by simpa only [Metric.mem_ball,dist_zero_right] using (hw n).trans_lt (half_lt_self heps))
    · have hh : Tendsto (fun z : S×U => P+E z) (𝓝 0) (𝓝 P) := by
        simpa using (continuous_const.add E.continuous).continuousAt.tendsto (x := 0)
      exact hh.comp ht
    · intro n
      dsimp only
      rw [hrec]
      change P+E (E.symm (T (P+E (w n))-P))=T (P+E (w n))
      rw [E.apply_symm_apply]
      abel
  · obtain ⟨V₀,hV₀,hV₀0,hV₀V,hV₀map⟩ := hInv
    refine ⟨V₀,hV₀,hV₀0,hV₀V,?_⟩
    intro a ha
    obtain ⟨b,hb,he⟩ := hV₀map a ha
    refine ⟨b,hb,?_⟩
    have hh := congrArg E he
    change E (E.symm (T (chart P E h a)-P))=E (b,h b) at hh
    rw [E.apply_symm_apply] at hh
    change T (chart P E h a)=P+E (b,h b)
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

end BfgsVerification.AnalyticStableGraph
