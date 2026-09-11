import BfgsVerification.AnalyticStableSequence

noncomputable section
open scoped Topology BoundedContinuousFunction
open Set Filter
namespace BfgsVerification.AnalyticStableGraph

variable {S U : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]

theorem bounded_backward_orbit_zero (B : U →L[ℝ] U) (hB : ‖B‖<1)
    (w : Seq S U) (hrec : ∀ n, (w n).2=B (w (n+1)).2) (n : ℕ) : (w n).2=0 := by
  have hbound (m : ℕ) : ∀ k, ‖(w k).2‖≤‖B‖^m*‖w‖ := by
    induction m with
    | zero => intro k; simpa using (norm_snd_le _).trans (w.norm_coe_le_norm k)
    | succ m hm =>
      intro k
      calc
        ‖(w k).2‖=‖B (w (k+1)).2‖ := by rw [hrec]
        _≤‖B‖*‖(w (k+1)).2‖ := B.le_opNorm _
        _≤‖B‖*(‖B‖^m*‖w‖) := mul_le_mul_of_nonneg_left (hm (k+1)) (norm_nonneg B)
        _=‖B‖^(m+1)*‖w‖ := by rw [pow_succ]; ring
  have ht : Tendsto (fun m : ℕ => ‖B‖^m*‖w‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg B) hB).mul_const ‖w‖
  exact norm_le_zero_iff.mp (ge_of_tendsto' (x := (atTop : Filter ℕ)) ht (fun m => hbound m n))

theorem linear_graph_derivative_unstable_zero (A : S →L[ℝ] S) (B : U →L[ℝ] U)
    (hA : ‖A‖<1) (hB : ‖B‖<1) (a : S) (n : ℕ) :
    (((ParametricFixedPoint.oneSubEquiv (linearStep A B) (linearStep_norm_lt A B hA hB)).symm
      (seedMap a)) n).2=0 := by
  let M := ParametricFixedPoint.oneSubEquiv (linearStep A B) (linearStep_norm_lt A B hA hB)
  let w := M.symm (seedMap a)
  have he : w-linearStep A B w=seedMap a := M.apply_symm_apply (seedMap a)
  apply bounded_backward_orbit_zero B hB w
  intro k
  have hs := congrArg (fun v : Seq S U => (v k).2) he
  have hseed : (seedValue (U := U) a k).2=0 := by unfold seedValue; split_ifs <;> rfl
  change (w k).2-B (w (k+1)).2=(seedValue a k).2 at hs
  rw [hseed] at hs
  exact sub_eq_zero.mp hs

def initialUnstable : Seq S U →L[ℝ] U :=
  (ContinuousLinearMap.snd ℝ S U).comp (BoundedContinuousFunction.evalCLM ℝ 0)

theorem initialUnstable_apply (w : Seq S U) : initialUnstable w=(w 0).2 := rfl

theorem initialUnstable_comp_derivative (A : S →L[ℝ] S) (B : U →L[ℝ] U)
    (hA : ‖A‖<1) (hB : ‖B‖<1) :
    initialUnstable.comp
      ((ParametricFixedPoint.oneSubEquiv (linearStep A B) (linearStep_norm_lt A B hA hB)).symm.toContinuousLinearMap.comp seedMap)=
      (0 : S →L[ℝ] U) := by
  ext a
  exact linear_graph_derivative_unstable_zero A B hA hB a 0

end BfgsVerification.AnalyticStableGraph
