import BfgsVerification.StableGraphTangent

noncomputable section
open scoped Topology ContDiff BoundedContinuousFunction ZeroAtInfty
open Set Filter
namespace BfgsVerification.AnalyticStableGraph

variable {S U : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]

/-- A smooth graph of actual forward stable orbits, tangent to the stable
coordinate subspace. The graph and its zero unstable derivative are derived. -/
theorem exists_smooth_stable_graph_from_remainder (A : S →L[ℝ] S) (L : U ≃L[ℝ] U)
    (N : S×U → S×U) (hN : AnalyticAt ℝ N 0) (hN0 : N 0=0)
    (hNd : HasFDerivAt N (0 : (S×U) →L[ℝ] (S×U)) 0)
    (hA : ‖A‖<1) (hB : ‖L.symm.toContinuousLinearMap‖<1) {r : ℝ} (hr : 0<r) :
    ∃ h : S → U, ∃ V : Set S, IsOpen V ∧ (0 : S)∈V ∧ h 0=0 ∧
      ContDiffOn ℝ ∞ h V ∧ HasFDerivAt h (0 : S →L[ℝ] U) 0 ∧
      ∀ a∈V, ∃ w : ℕ → S×U, w 0=(a,h a) ∧ (∀ n, ‖w n‖≤r) ∧
        Tendsto w atTop (𝓝 0) ∧ ∀ n, w (n+1)=(A (w n).1,L (w n).2)+N (w n) := by
  obtain ⟨g,V,hV,hV0,hg0,hgc,hgd,hsol⟩ :=
    exists_smooth_stable_sequence A L.symm.toContinuousLinearMap N hN hN0 hNd hA hB hr
  let h : S → U := fun a => initialUnstable (g a)
  refine ⟨h,V,hV,hV0,?_,?_,?_,?_⟩
  · simp [h,hg0]
  · exact (initialUnstable : Seq S U →L[ℝ] U).contDiff.comp_contDiffOn hgc
  · have hd := (initialUnstable : Seq S U →L[ℝ] U).hasFDerivAt.comp (0 : S) hgd
    exact hd.congr_fderiv (initialUnstable_comp_derivative A L.symm.toContinuousLinearMap hA hB)
  · intro a ha
    obtain ⟨w,hwg,hw,hw0,hwrec⟩ := hsol a ha
    refine ⟨w,?_,fun n => (LocalStableOrbit.sequence_norm_apply w n).trans hw,
      LocalStableOrbit.sequence_tendsto w,?_⟩
    · apply Prod.ext hw0
      change (w 0).2=initialUnstable (g a)
      rw [← hwg]
      rfl
    · intro n
      apply Prod.ext (hwrec n).1
      have he := congrArg L (hwrec n).2
      simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] at he
      exact sub_eq_iff_eq_add.mp he.symm

theorem exists_smooth_stable_graph (A : S →L[ℝ] S) (L : U ≃L[ℝ] U)
    (T : S×U → S×U) (hT : AnalyticAt ℝ T 0) (hT0 : T 0=0)
    (hTd : HasFDerivAt T (A.prodMap L.toContinuousLinearMap) 0)
    (hA : ‖A‖<1) (hB : ‖L.symm.toContinuousLinearMap‖<1) {r : ℝ} (hr : 0<r) :
    ∃ h : S → U, ∃ V : Set S, IsOpen V ∧ (0 : S)∈V ∧ h 0=0 ∧
      ContDiffOn ℝ ∞ h V ∧ HasFDerivAt h (0 : S →L[ℝ] U) 0 ∧
      ∀ a∈V, ∃ w : ℕ → S×U, w 0=(a,h a) ∧ (∀ n, ‖w n‖≤r) ∧
        Tendsto w atTop (𝓝 0) ∧ ∀ n, w (n+1)=T (w n) := by
  let D := A.prodMap L.toContinuousLinearMap
  let N : S×U → S×U := fun x => T x-D x
  have hN : AnalyticAt ℝ N 0 := hT.sub (D.analyticAt 0)
  have hNd : HasFDerivAt N (0 : (S×U) →L[ℝ] (S×U)) 0 := by
    simpa only [D,sub_self] using hTd.sub D.hasFDerivAt
  have hN0 : N 0=0 := by simp [N,hT0]
  obtain ⟨h,V,hV,hV0,h0,hc,hd,hsol⟩ :=
    exists_smooth_stable_graph_from_remainder A L N hN hN0 hNd hA hB hr
  refine ⟨h,V,hV,hV0,h0,hc,hd,?_⟩
  intro a ha
  obtain ⟨w,hw0,hw,ht,hrec⟩ := hsol a ha
  refine ⟨w,hw0,hw,ht,?_⟩
  intro n
  rw [hrec]
  change D (w n)+(T (w n)-D (w n))=T (w n)
  abel

end BfgsVerification.AnalyticStableGraph
