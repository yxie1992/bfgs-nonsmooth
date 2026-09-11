import BfgsVerification.AnalyticStableGraph

noncomputable section
open scoped Topology ContDiff
open Set Filter
namespace BfgsVerification.AnalyticStableGraph

variable {S U X : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

def chart (P : X) (E : (S×U) ≃L[ℝ] X) (h : S → U) (a : S) : X := P+E (a,h a)

theorem chart_inverse (P : X) (E : (S×U) ≃L[ℝ] X) (h : S → U) (a : S) :
    (E.symm (chart P E h a-P)).1=a := by simp [chart]

theorem chart_injective (P : X) (E : (S×U) ≃L[ℝ] X) (h : S → U) :
    Function.Injective (chart P E h) := by
  intro a b hab
  simpa only [chart_inverse] using congrArg (fun x => (E.symm (x-P)).1) hab

theorem chart_contDiffOn (P : X) (E : (S×U) ≃L[ℝ] X) {h : S → U} {V : Set S}
    (hc : ContDiffOn ℝ ∞ h V) : ContDiffOn ℝ ∞ (chart P E h) V :=
  contDiffOn_const.add (E.toContinuousLinearMap.contDiff.comp_contDiffOn (contDiffOn_id.prodMk hc))

theorem chart_hasFDerivAt (P : X) (E : (S×U) ≃L[ℝ] X) {h : S → U}
    (hd : HasFDerivAt h (0 : S →L[ℝ] U) 0) :
    HasFDerivAt (chart P E h) (E.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ S U)) 0 := by
  have hp := (hasFDerivAt_id (𝕜 := ℝ) (0 : S)).prodMk hd
  have he := (E.toContinuousLinearMap.hasFDerivAt.comp (0 : S) hp).const_add P
  apply he.congr_fderiv
  ext a
  rfl

theorem exists_smooth_graph_of_splitting {T : X → X} {P : X} {F : X →L[ℝ] X}
    (hT : AnalyticAt ℝ T P) (hfix : T P=P) (hd : HasFDerivAt T F P)
    (E : (S×U) ≃L[ℝ] X) (A : S →L[ℝ] S) (L : U ≃L[ℝ] U)
    (hA : ‖A‖<1) (hL : ‖L.symm.toContinuousLinearMap‖<1)
    (hconj : F.comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp (A.prodMap L.toContinuousLinearMap))
    (W : Set X) (hW : W∈𝓝 P) :
    ∃ h : S → U, ∃ V : Set S, IsOpen V ∧ (0 : S)∈V ∧ h 0=0 ∧
      ContDiffOn ℝ ∞ h V ∧ HasFDerivAt h (0 : S →L[ℝ] U) 0 ∧
      ContDiffOn ℝ ∞ (chart P E h) V ∧
      HasFDerivAt (chart P E h) (E.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ S U)) 0 ∧
      ∀ a∈V, ∃ w : ℕ → X, w 0=chart P E h a ∧ (∀ n, w n∈W) ∧
        Tendsto w atTop (𝓝 P) ∧ ∀ n, w (n+1)=T (w n) := by
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
  obtain ⟨h,V,hV,hV0,h0,hc,hder,hsol⟩ := exists_smooth_stable_graph A L T' hT' hT0 hTd hA hL (half_pos heps)
  refine ⟨h,V,hV,hV0,h0,hc,hder,chart_contDiffOn P E hc,chart_hasFDerivAt P E hder,?_⟩
  intro a ha
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

end BfgsVerification.AnalyticStableGraph
