import BfgsVerification.BoundedSequenceNonlinear
import BfgsVerification.AnalyticFixedPointGraph
import BfgsVerification.LocalStableOrbit

noncomputable section
open scoped Topology ContDiff BoundedContinuousFunction ZeroAtInfty
open Set Filter
namespace BfgsVerification.AnalyticStableGraph

variable {S U : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]

theorem transform_eq_of_recurrence (A : S →L[ℝ] S) (B : U →L[ℝ] U)
    (N : S×U → S×U) (L : Seq S U → Seq S U) (a : S) (w : Seq S U)
    (hL : ∀ k, L w k=N (w k)) (ha : (w 0).1=a)
    (hrec : ∀ n, (w (n+1)).1=A (w n).1+(N (w n)).1 ∧
      (w n).2=B ((w (n+1)).2-(N (w n)).2)) : transform A B L (a,w)=w := by
  apply BoundedContinuousFunction.ext
  intro n
  apply Prod.ext
  · cases n with
    | zero => simpa [transform,seedMap_apply,linearStep_apply,nonlinearStep_apply,
        seedValue,linearValue,nonlinearValue] using ha.symm
    | succ k => simpa [transform,seedMap_apply,linearStep_apply,nonlinearStep_apply,
        seedValue,linearValue,nonlinearValue,hL] using (hrec k).1.symm
  · simpa [transform,seedMap_apply,linearStep_apply,nonlinearStep_apply,
      seedValue,linearValue,nonlinearValue,hL,map_sub,sub_eq_add_neg,apply_ite] using (hrec n).2.symm

/-- The implicit-function sequence is the actual vanishing-at-infinity orbit
constructed by contraction. The identification uses local uniqueness, not an
assumption that all bounded sequences vanish. -/
theorem exists_smooth_stable_sequence (A : S →L[ℝ] S) (B : U →L[ℝ] U)
    (N : S×U → S×U) (hN : AnalyticAt ℝ N 0) (hN0 : N 0=0)
    (hNd : HasFDerivAt N (0 : (S×U) →L[ℝ] (S×U)) 0)
    (hA : ‖A‖<1) (hB : ‖B‖<1) {r : ℝ} (hr : 0<r) :
    ∃ g : S → Seq S U, ∃ V : Set S, IsOpen V ∧ (0 : S)∈V ∧ g 0=0 ∧
      ContDiffOn ℝ ∞ g V ∧
      HasFDerivAt g
        ((ParametricFixedPoint.oneSubEquiv (linearStep A B) (linearStep_norm_lt A B hA hB)).symm.toContinuousLinearMap.comp seedMap) 0 ∧
      ∀ a∈V, ∃ w : LocalStableOrbit.Sequence S U, w.toBCF=g a ∧ ‖w‖≤r ∧
        (w 0).1=a ∧ ∀ n, (w (n+1)).1=A (w n).1+(N (w n)).1 ∧
          (w n).2=B ((w (n+1)).2-(N (w n)).2) := by
  obtain ⟨L,hL,hL0,hLd,R0,hR0,hLpoint⟩ := BoundedAnalytic.exists_analytic_lift_zero hN hN0 hNd
  obtain ⟨g,V,hV,hV0,hg0,hgc,hgd,hge,hgu⟩ :=
    ParametricFixedPoint.exists_smooth_fixedPoint_graph (seedMap : S →L[ℝ] Seq S U)
      (linearStep A B) (linearStep_norm_lt A B hA hB)
      (transform_zero A B hL0) (transform_analytic A B hL) (transform_hasFDerivAt A B hLd.hasFDerivAt)
  obtain ⟨eps,heps,hepsU⟩ := Metric.mem_nhds_iff.mp hgu
  obtain ⟨δ,hδ,K,hK,hAK,hBK⟩ := LocalStableOrbit.contraction_parameters A B hA hB
  have hNs := (hN.contDiffAt (n := 1)).hasStrictFDerivAt' hNd le_rfl
  obtain ⟨R,hR,hRle,hLip⟩ := LocalStableOrbit.small_lipschitz_ball hNs hδ
    (lt_min hr (lt_min (half_pos hR0) (half_pos heps)))
  have hRr : R≤r := hRle.trans (min_le_left _ _)
  have hRR0 : R<R0 := (hRle.trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (half_lt_self hR0)
  have hReps : R<eps := (hRle.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (half_lt_self heps)
  refine ⟨g,V∩Metric.ball 0 R,hV.inter Metric.isOpen_ball,⟨hV0,by simpa using hR⟩,
    hg0,hgc.mono inter_subset_left,hgd,?_⟩
  intro a ha
  have haR : ‖a‖≤R := (by simpa only [Metric.mem_ball,dist_zero_right] using ha.2 : ‖a‖<R).le
  obtain ⟨w,hw,hw0,hwrec⟩ := LocalStableOrbit.stable_sequence_exists A B N a
    hNs.continuousAt hN0 hR.le hδ.le hK haR hAK hBK hLip
  have hNL : ∀ k, L w.toBCF k=N (w k) := hLpoint w.toBCF (hw.trans_lt hRR0)
  have hfix := transform_eq_of_recurrence A B N L a w.toBCF hNL hw0 hwrec
  have hpair : (a,w.toBCF)∈Metric.ball (0 : S×Seq S U) eps := by
    rw [Metric.mem_ball,dist_zero_right,Prod.norm_def]
    exact (max_le haR hw).trans_lt hReps
  have hident : w.toBCF=g a := hepsU hpair hfix
  exact ⟨w,hident,hw.trans hRr,hw0,hwrec⟩

end BfgsVerification.AnalyticStableGraph
