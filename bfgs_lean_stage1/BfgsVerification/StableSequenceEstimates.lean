import BfgsVerification.StableSequenceTransform

noncomputable section
open scoped Topology ZeroAtInfty
open Set Filter
namespace BfgsVerification.LocalStableOrbit

variable {S U : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

theorem remainder_norm_bound {N : S×U → S×U} {R δ : ℝ} (hR : 0≤R) (hN0 : N 0=0)
    (hLip : ∀ x y, ‖x‖≤R → ‖y‖≤R → ‖N x-N y‖≤δ*‖x-y‖) {x : S×U} (hx : ‖x‖≤R) :
    ‖N x‖≤δ*‖x‖ := by
  simpa only [hN0, sub_zero] using hLip x 0 hx (by simpa using hR)

theorem stable_expression_bound (A : S →L[ℝ] S) {x y : S×U} {D δ : ℝ}
    (hδ : 0≤δ) (hx : ‖x‖≤D) (hy : ‖y‖≤δ*D) :
    ‖A x.1+y.1‖≤(‖A‖+δ)*D := by
  have hx' := (norm_fst_le x).trans hx
  have hy' := (norm_fst_le y).trans hy
  have ha := A.le_opNorm x.1
  have hm := mul_le_mul_of_nonneg_left hx' (norm_nonneg A)
  have ht := norm_add_le (A x.1) y.1
  nlinarith

theorem unstable_expression_bound (B : U →L[ℝ] U) {x y : S×U} {D δ : ℝ}
    (hx : ‖x‖≤D) (hy : ‖y‖≤δ*D) :
    ‖B (x.2-y.2)‖≤‖B‖*(1+δ)*D := by
  have hx' := (norm_snd_le x).trans hx
  have hy' := (norm_snd_le y).trans hy
  have ht := norm_sub_le x.2 y.2
  have hbound : ‖x.2-y.2‖≤(1+δ)*D := by nlinarith
  exact (B.le_opNorm _).trans (by nlinarith [mul_le_mul_of_nonneg_left hbound (norm_nonneg B)])

theorem sequenceMap_ball (A : S →L[ℝ] S) (B : U →L[ℝ] U) (N : S×U → S×U)
    (a : S) (hN : ContinuousAt N 0) (hN0 : N 0=0) {R δ : ℝ} (hR : 0≤R) (hδ : 0≤δ)
    (ha : ‖a‖≤R) (hA : ‖A‖+δ≤1) (hB : ‖B‖*(1+δ)≤1)
    (hLip : ∀ x y, ‖x‖≤R → ‖y‖≤R → ‖N x-N y‖≤δ*‖x-y‖)
    {w : Sequence S U} (hw : ‖w‖≤R) : ‖sequenceMap A B N a hN hN0 w‖≤R := by
  have hw' (n : ℕ) : ‖w n‖≤R := (sequence_norm_apply w n).trans hw
  have hNw (n : ℕ) : ‖N (w n)‖≤δ*R :=
    (remainder_norm_bound hR hN0 hLip (hw' n)).trans (mul_le_mul_of_nonneg_left (hw' n) hδ)
  apply (sequence_norm_le hR).mpr
  intro n
  rw [Prod.norm_def]
  apply max_le
  · cases n with
    | zero => exact ha
    | succ n =>
      exact (stable_expression_bound A hδ (hw' n) (hNw n)).trans (by nlinarith [mul_le_mul_of_nonneg_right hA hR])
  · exact (unstable_expression_bound B (hw' (n+1)) (hNw n)).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hB hR])

theorem sequenceMap_difference (A : S →L[ℝ] S) (B : U →L[ℝ] U) (N : S×U → S×U)
    (a : S) (hN : ContinuousAt N 0) (hN0 : N 0=0) {R δ K : ℝ} (hδ : 0≤δ) (hK : 0≤K)
    (hA : ‖A‖+δ≤K) (hB : ‖B‖*(1+δ)≤K)
    (hLip : ∀ x y, ‖x‖≤R → ‖y‖≤R → ‖N x-N y‖≤δ*‖x-y‖)
    {w v : Sequence S U} (hw : ‖w‖≤R) (hv : ‖v‖≤R) :
    ‖sequenceMap A B N a hN hN0 w-sequenceMap A B N a hN hN0 v‖≤K*‖w-v‖ := by
  have hdiff (n : ℕ) : ‖w n-v n‖≤‖w-v‖ := sequence_norm_apply (w-v) n
  have hNdiff (n : ℕ) : ‖N (w n)-N (v n)‖≤δ*‖w-v‖ :=
    (hLip (w n) (v n) ((sequence_norm_apply w n).trans hw) ((sequence_norm_apply v n).trans hv)).trans
      (mul_le_mul_of_nonneg_left (hdiff n) hδ)
  apply (sequence_norm_le (mul_nonneg hK (norm_nonneg _))).mpr
  intro n
  rw [Prod.norm_def]
  apply max_le
  · cases n with
    | zero => simpa only [ZeroAtInftyContinuousMap.sub_apply, Prod.fst_sub,
        sequenceMap_fst_zero, sub_self, norm_zero] using mul_nonneg hK (norm_nonneg (w-v))
    | succ n =>
      have hh : ((sequenceMap A B N a hN hN0 w-sequenceMap A B N a hN hN0 v) (n+1)).1 =
          A (w n-v n).1+(N (w n)-N (v n)).1 := by
        simp only [ZeroAtInftyContinuousMap.sub_apply, Prod.fst_sub, sequenceMap_fst_succ, map_sub]
        abel
      rw [hh]
      exact (stable_expression_bound A hδ (hdiff n) (hNdiff n)).trans
        (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  · have hh : ((sequenceMap A B N a hN hN0 w-sequenceMap A B N a hN hN0 v) n).2 =
        B ((w (n+1)-v (n+1)).2-(N (w n)-N (v n)).2) := by
      simp only [ZeroAtInftyContinuousMap.sub_apply, Prod.snd_sub, sequenceMap_snd, ← map_sub]
      congr 1
      abel
    rw [hh]
    exact (unstable_expression_bound B (hdiff (n+1)) (hNdiff n)).trans
      (mul_le_mul_of_nonneg_right hB (norm_nonneg _))

end BfgsVerification.LocalStableOrbit
