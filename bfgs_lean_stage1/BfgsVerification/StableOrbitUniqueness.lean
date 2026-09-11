import BfgsVerification.AnalyticStableGraph

noncomputable section
open scoped Topology ZeroAtInfty
open Set Filter
namespace BfgsVerification.AnalyticStableGraph

variable {S U : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]

theorem sequenceMap_fixed_of_forward (A : S →L[ℝ] S) (L : U ≃L[ℝ] U)
    (N : S×U → S×U) (hN : ContinuousAt N 0) (hN0 : N 0=0)
    (w : LocalStableOrbit.Sequence S U)
    (hrec : ∀ n, w (n+1)=(A (w n).1,L (w n).2)+N (w n)) :
    LocalStableOrbit.sequenceMap A L.symm.toContinuousLinearMap N (w 0).1 hN hN0 w=w := by
  ext n
  · cases n with
    | zero => rfl
    | succ n => exact (congrArg Prod.fst (hrec n)).symm
  · have he := congrArg Prod.snd (hrec n)
    have he' : (w (n+1)).2-(N (w n)).2=L (w n).2 := by
      change (w (n+1)).2=L (w n).2+(N (w n)).2 at he
      exact sub_eq_iff_eq_add.mpr he
    change L.symm ((w (n+1)).2-(N (w n)).2)=(w n).2
    rw [he',L.symm_apply_apply]

/-- Actual small convergent forward orbits with the same initial stable
coordinate coincide. The contraction constants and radius are derived from
the actual derivative, not supplied orbit-wise. -/
theorem exists_unique_orbits_radius (A : S →L[ℝ] S) (L : U ≃L[ℝ] U)
    (T : S×U → S×U) (hT : AnalyticAt ℝ T 0) (hT0 : T 0=0)
    (hTd : HasFDerivAt T (A.prodMap L.toContinuousLinearMap) 0)
    (hA : ‖A‖<1) (hB : ‖L.symm.toContinuousLinearMap‖<1) {r : ℝ} (hr : 0<r) :
    ∃ R : ℝ, 0<R ∧ R≤r ∧ ∀ w v : ℕ → S×U,
      (∀ n, ‖w n‖≤R) → (∀ n, ‖v n‖≤R) →
      Tendsto w atTop (𝓝 0) → Tendsto v atTop (𝓝 0) →
      (w 0).1=(v 0).1 →
      (∀ n, w (n+1)=T (w n)) → (∀ n, v (n+1)=T (v n)) → w=v := by
  let D := A.prodMap L.toContinuousLinearMap
  let N : S×U → S×U := fun x => T x-D x
  have hNs : HasStrictFDerivAt N (0 : (S×U) →L[ℝ] (S×U)) 0 := by
    have hd : HasFDerivAt N (0 : (S×U) →L[ℝ] (S×U)) 0 := by
      simpa only [D,sub_self] using hTd.sub D.hasFDerivAt
    exact ((hT.sub (D.analyticAt 0)).contDiffAt (n := 1)).hasStrictFDerivAt' hd le_rfl
  have hN0 : N 0=0 := by simp [N,hT0]
  obtain ⟨δ,hδ,K,hK,hAK,hBK⟩ := LocalStableOrbit.contraction_parameters A L.symm.toContinuousLinearMap hA hB
  obtain ⟨R,hR,hRr,hLip⟩ := LocalStableOrbit.small_lipschitz_ball hNs hδ hr
  refine ⟨R,hR,hRr,?_⟩
  intro w v hw hv hwt hvt hfirst hwrec hvrec
  let w' : LocalStableOrbit.Sequence S U :=
    { toFun := w
      continuous_toFun := continuous_of_discreteTopology
      zero_at_infty' := by simpa only [cocompact_eq_atTop] using hwt }
  let v' : LocalStableOrbit.Sequence S U :=
    { toFun := v
      continuous_toFun := continuous_of_discreteTopology
      zero_at_infty' := by simpa only [cocompact_eq_atTop] using hvt }
  have hrec (z : ℕ → S×U) (hz : ∀ n, z (n+1)=T (z n)) (n : ℕ) :
      z (n+1)=(A (z n).1,L (z n).2)+N (z n) := by
    rw [hz]
    change T (z n)=D (z n)+(T (z n)-D (z n))
    abel
  have hfw := sequenceMap_fixed_of_forward A L N hNs.continuousAt hN0 w' (hrec w hwrec)
  have hfv := sequenceMap_fixed_of_forward A L N hNs.continuousAt hN0 v' (hrec v hvrec)
  have hh := LocalStableOrbit.sequenceMap_difference A L.symm.toContinuousLinearMap N (w 0).1
    hNs.continuousAt hN0 hδ.le K.coe_nonneg hAK hBK hLip
    ((LocalStableOrbit.sequence_norm_le hR.le).mpr hw : ‖w'‖≤R)
    ((LocalStableOrbit.sequence_norm_le hR.le).mpr hv : ‖v'‖≤R)
  change LocalStableOrbit.sequenceMap A L.symm.toContinuousLinearMap N (w 0).1 hNs.continuousAt hN0 w'=w' at hfw
  change LocalStableOrbit.sequenceMap A L.symm.toContinuousLinearMap N (v 0).1 hNs.continuousAt hN0 v'=v' at hfv
  rw [hfw,hfirst,hfv] at hh
  have hK' : (K : ℝ)<1 := hK
  have hnorm : ‖w'-v'‖=0 := by nlinarith [norm_nonneg (w'-v')]
  have he : w'=v' := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  exact congrArg (fun z : LocalStableOrbit.Sequence S U => (z : ℕ → S×U)) he

end BfgsVerification.AnalyticStableGraph
