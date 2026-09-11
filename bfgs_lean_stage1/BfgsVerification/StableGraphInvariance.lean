import BfgsVerification.StableOrbitUniqueness

noncomputable section
open scoped Topology ContDiff
open Set Filter
namespace BfgsVerification.AnalyticStableGraph

variable {S U : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]

/-- The smooth stable graph is locally forward invariant. Uniqueness of small
actual convergent orbits identifies its forward image with the same graph. -/
theorem exists_smooth_locally_invariant_graph (A : S →L[ℝ] S) (L : U ≃L[ℝ] U)
    (T : S×U → S×U) (hT : AnalyticAt ℝ T 0) (hT0 : T 0=0)
    (hTd : HasFDerivAt T (A.prodMap L.toContinuousLinearMap) 0)
    (hA : ‖A‖<1) (hB : ‖L.symm.toContinuousLinearMap‖<1) {r : ℝ} (hr : 0<r) :
    ∃ h : S → U, ∃ V : Set S, IsOpen V ∧ (0 : S)∈V ∧ h 0=0 ∧
      ContDiffOn ℝ ∞ h V ∧ HasFDerivAt h (0 : S →L[ℝ] U) 0 ∧
      (∀ a∈V, ∃ w : ℕ → S×U, w 0=(a,h a) ∧ (∀ n, ‖w n‖≤r) ∧
        Tendsto w atTop (𝓝 0) ∧ ∀ n, w (n+1)=T (w n)) ∧
      ∃ V₀ : Set S, IsOpen V₀ ∧ (0 : S)∈V₀ ∧ V₀⊆V ∧
        ∀ a∈V₀, ∃ b∈V, T (a,h a)=(b,h b) := by
  obtain ⟨R,hR,hRr,huniq⟩ := exists_unique_orbits_radius A L T hT hT0 hTd hA hB hr
  obtain ⟨h,V,hV,hV0,h0,hc,hd,hsol⟩ := exists_smooth_stable_graph A L T hT hT0 hTd hA hB hR
  have hi : ContinuousAt (fun a : S => (a,h a)) 0 := continuousAt_id.prodMk hd.continuousAt
  have hi0 : (0,h (0 : S))=(0 : S×U) := by rw [h0]; rfl
  have ht0 : Tendsto (fun a : S => (T (a,h a)).1) (𝓝 0) (𝓝 0) := by
    have hTc : ContinuousAt T (0,h (0 : S)) := by simpa only [hi0] using (hT.contDiffAt (n := 1)).continuousAt
    have ht : ContinuousAt (fun a : S => T (a,h a)) 0 := hTc.comp (f := fun a : S => (a,h a)) (x := (0 : S)) hi
    simpa only [hi0,hT0,Prod.fst_zero] using ht.fst.tendsto
  have hpre : {a : S | (T (a,h a)).1∈V}∈𝓝 0 := ht0 (hV.mem_nhds hV0)
  obtain ⟨V₀,hV₀sub,hV₀open,hV₀0⟩ := mem_nhds_iff.mp (inter_mem (hV.mem_nhds hV0) hpre)
  refine ⟨h,V,hV,hV0,h0,hc,hd,?_,V₀,hV₀open,hV₀0,fun a ha => (hV₀sub ha).1,?_⟩
  · intro a ha
    obtain ⟨w,hw0,hw,ht,hrec⟩ := hsol a ha
    exact ⟨w,hw0,fun n => (hw n).trans hRr,ht,hrec⟩
  · intro a ha
    have haV := (hV₀sub ha).1
    have hbV := (hV₀sub ha).2
    let b := (T (a,h a)).1
    obtain ⟨w,hw0,hw,hwt,hwrec⟩ := hsol a haV
    obtain ⟨v,hv0,hv,hvt,hvrec⟩ := hsol b hbV
    have hshift : Tendsto (fun n => w (n+1)) atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 1).mpr hwt
    have hfirst : (w 1).1=(v 0).1 := by rw [hv0,hwrec 0,hw0]
    have he := huniq (fun n => w (n+1)) v (fun n => hw (n+1)) hv hshift hvt hfirst
      (fun n => hwrec (n+1)) hvrec
    have he0 := congrArg (fun z : ℕ → S×U => z 0) he
    change w 1=v 0 at he0
    rw [hwrec 0,hw0,hv0] at he0
    exact ⟨b,hbV,he0⟩

end BfgsVerification.AnalyticStableGraph
