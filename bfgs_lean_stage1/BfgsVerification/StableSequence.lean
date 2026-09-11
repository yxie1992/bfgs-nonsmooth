import BfgsVerification.StableSequenceEstimates

noncomputable section
open scoped Topology ZeroAtInfty NNReal
open Set Filter
namespace BfgsVerification.LocalStableOrbit

variable {S U : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]

theorem stable_sequence_exists (A : S →L[ℝ] S) (B : U →L[ℝ] U) (N : S×U → S×U)
    (a : S) (hN : ContinuousAt N 0) (hN0 : N 0=0) {R δ : ℝ} {K : ℝ≥0}
    (hR : 0≤R) (hδ : 0≤δ) (hK : K<1) (ha : ‖a‖≤R)
    (hA : ‖A‖+δ≤K) (hB : ‖B‖*(1+δ)≤K)
    (hLip : ∀ x y, ‖x‖≤R → ‖y‖≤R → ‖N x-N y‖≤δ*‖x-y‖) :
    ∃ w : Sequence S U, ‖w‖≤R ∧ (w 0).1=a ∧
      ∀ n, (w (n+1)).1=A (w n).1+(N (w n)).1 ∧
        (w n).2=B ((w (n+1)).2-(N (w n)).2) := by
  let ball : Set (Sequence S U) := {w | ‖w‖≤R}
  let f : Sequence S U → Sequence S U := sequenceMap A B N a hN hN0
  have hK' : (K : ℝ)<1 := hK
  have hmap : MapsTo f ball ball := by
    intro w hw
    exact sequenceMap_ball A B N a hN hN0 hR hδ ha
      (hA.trans hK'.le) (hB.trans hK'.le) hLip hw
  have hclosed : IsClosed ball := isClosed_le continuous_norm continuous_const
  have hcon : ContractingWith K (hmap.restrict f ball ball) := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul (fun w v => ?_)⟩
    change dist (f w.val) (f v.val)≤(K : ℝ)*dist w.val v.val
    simpa only [dist_eq_norm] using
      sequenceMap_difference A B N a hN hN0 hδ K.coe_nonneg hA hB hLip w.property v.property
  obtain ⟨w, hw, hfix, _, _⟩ := ContractingWith.exists_fixedPoint' hclosed.isComplete hmap hcon
    (x := 0) (show (0 : Sequence S U)∈ball by simpa [ball] using hR) (edist_ne_top _ _)
  refine ⟨w,hw,?_,?_⟩
  · exact (congrArg (fun v : Sequence S U => (v 0).1) hfix).symm
  · intro n
    exact ⟨(congrArg (fun v : Sequence S U => (v (n+1)).1) hfix).symm,
      congrArg (fun v : Sequence S U => (v n).2) hfix |>.symm⟩

theorem nonlinear_stable_orbit (A : S →L[ℝ] S) (L : U ≃L[ℝ] U) (N : S×U → S×U)
    (a : S) (hN : ContinuousAt N 0) (hN0 : N 0=0) {R δ : ℝ} {K : ℝ≥0}
    (hR : 0≤R) (hδ : 0≤δ) (hK : K<1) (ha : ‖a‖≤R)
    (hA : ‖A‖+δ≤K) (hB : ‖L.symm.toContinuousLinearMap‖*(1+δ)≤K)
    (hLip : ∀ x y, ‖x‖≤R → ‖y‖≤R → ‖N x-N y‖≤δ*‖x-y‖) :
    ∃ w : ℕ → S×U, (∀ n, ‖w n‖≤R) ∧ Tendsto w atTop (𝓝 0) ∧
      (w 0).1=a ∧ ∀ n, w (n+1)=(A (w n).1,L (w n).2)+N (w n) := by
  obtain ⟨w, hw, ha', hrec⟩ := stable_sequence_exists A L.symm.toContinuousLinearMap N a
    hN hN0 hR hδ hK ha hA hB hLip
  refine ⟨w,fun n => (sequence_norm_apply w n).trans hw,sequence_tendsto w,ha',?_⟩
  intro n
  apply Prod.ext
  · exact (hrec n).1
  · have he := congrArg L (hrec n).2
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at he
    exact sub_eq_iff_eq_add.mp he.symm

end BfgsVerification.LocalStableOrbit
