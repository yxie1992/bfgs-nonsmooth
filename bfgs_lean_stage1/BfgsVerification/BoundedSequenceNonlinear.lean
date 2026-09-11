import BfgsVerification.BoundedSequenceLinear

noncomputable section
open scoped Topology BoundedContinuousFunction
open Set Filter
namespace BfgsVerification.AnalyticStableGraph

variable {S U : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

def nonlinearValue (B : U →L[ℝ] U) (w : Seq S U) (n : ℕ) : S×U :=
  ((match n with | 0 => 0 | k+1 => (w k).1), -B (w n).2)

theorem nonlinearValue_bound (B : U →L[ℝ] U) (w : Seq S U) (n : ℕ) :
    ‖nonlinearValue B w n‖≤max 1 ‖B‖*‖w‖ := by
  have hs (k : ℕ) : ‖(w k).1‖≤max 1 ‖B‖*‖w‖ := by
    exact ((norm_fst_le _).trans (w.norm_coe_le_norm k)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 ‖B‖) (norm_nonneg w))
  have hu (k : ℕ) : ‖-B (w k).2‖≤max 1 ‖B‖*‖w‖ := by
    rw [norm_neg]
    exact (B.le_opNorm _).trans (mul_le_mul (le_max_right _ _)
      ((norm_snd_le _).trans (w.norm_coe_le_norm k)) (norm_nonneg _) (le_max_of_le_left zero_le_one))
  cases n with
  | zero => simpa only [nonlinearValue,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] using hu 0
  | succ k => exact max_le (hs k) (hu (k+1))

def nonlinearSequence (B : U →L[ℝ] U) (w : Seq S U) : Seq S U :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (nonlinearValue B w)
    (max 1 ‖B‖*‖w‖) (nonlinearValue_bound B w)

theorem nonlinearSequence_apply (B : U →L[ℝ] U) (w : Seq S U) (n : ℕ) :
    nonlinearSequence B w n=nonlinearValue B w n := rfl

def nonlinearOperator (B : U →L[ℝ] U) : Seq S U →ₗ[ℝ] Seq S U where
  toFun := nonlinearSequence B
  map_add' w v := by
    ext n <;> cases n <;> simp [nonlinearSequence_apply,nonlinearValue,add_comm]
  map_smul' c w := by
    ext n <;> cases n <;> simp [nonlinearSequence_apply,nonlinearValue,add_comm]

theorem nonlinearOperator_bound (B : U →L[ℝ] U) (w : Seq S U) :
    ‖nonlinearOperator B w‖≤max 1 ‖B‖*‖w‖ := by
  exact (BoundedContinuousFunction.norm_le
    (mul_nonneg (le_max_of_le_left zero_le_one) (norm_nonneg w))).mpr (nonlinearValue_bound B w)

def nonlinearStep (B : U →L[ℝ] U) : Seq S U →L[ℝ] Seq S U :=
  (nonlinearOperator B : Seq S U →ₗ[ℝ] Seq S U).mkContinuous (max 1 ‖B‖) (nonlinearOperator_bound (S := S) B)

theorem nonlinearStep_apply (B : U →L[ℝ] U) (w : Seq S U) (n : ℕ) :
    nonlinearStep B w n=nonlinearValue B w n := rfl

def transform (A : S →L[ℝ] S) (B : U →L[ℝ] U) (L : Seq S U → Seq S U)
    (p : S×Seq S U) : Seq S U := seedMap p.1+linearStep A B p.2+nonlinearStep B (L p.2)

theorem transform_zero (A : S →L[ℝ] S) (B : U →L[ℝ] U) {L : Seq S U → Seq S U}
    (hL : L 0=0) : transform A B L 0=0 := by simp [transform,hL]

theorem transform_analytic (A : S →L[ℝ] S) (B : U →L[ℝ] U) {L : Seq S U → Seq S U}
    (hL : AnalyticAt ℝ L 0) : AnalyticAt ℝ (transform A B L) 0 := by
  unfold transform
  exact (((seedMap : S →L[ℝ] Seq S U).analyticAt 0).comp (f := fun p : S×Seq S U => p.1) (x := (0 : S×Seq S U)) analyticAt_fst).add
    (((linearStep A B).analyticAt 0).comp (f := fun p : S×Seq S U => p.2) (x := (0 : S×Seq S U)) analyticAt_snd) |>.add
      (((nonlinearStep B : Seq S U →L[ℝ] Seq S U).analyticAt (L 0)).comp (f := fun p : S×Seq S U => L p.2) (x := (0 : S×Seq S U)) (hL.comp (f := fun p : S×Seq S U => p.2) (x := (0 : S×Seq S U)) analyticAt_snd))

theorem transform_hasFDerivAt (A : S →L[ℝ] S) (B : U →L[ℝ] U) {L : Seq S U → Seq S U}
    (hL : HasFDerivAt L (0 : Seq S U →L[ℝ] Seq S U) 0) :
    HasFDerivAt (transform A B L) (seedMap.coprod (linearStep A B)) 0 := by
  have hs := (seedMap : S →L[ℝ] Seq S U).hasFDerivAt.comp (0 : S×Seq S U) (hasFDerivAt_fst (𝕜 := ℝ))
  have hl := (linearStep A B).hasFDerivAt.comp (0 : S×Seq S U) (hasFDerivAt_snd (𝕜 := ℝ))
  have hn := (nonlinearStep B).hasFDerivAt.comp (0 : S×Seq S U)
    (hL.comp (0 : S×Seq S U) (hasFDerivAt_snd (𝕜 := ℝ)))
  have hd := hs.add hl |>.add hn
  apply hd.congr_fderiv
  ext p n <;> simp [ContinuousLinearMap.coprod_apply]

end BfgsVerification.AnalyticStableGraph
