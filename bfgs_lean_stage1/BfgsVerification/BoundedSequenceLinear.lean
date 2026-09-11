import BfgsVerification.BoundedAnalyticDerivative
import Mathlib.Analysis.Analytic.Constructions

noncomputable section
open scoped Topology BoundedContinuousFunction
open Set Filter
namespace BfgsVerification.AnalyticStableGraph

variable {S U : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

abbrev Seq (S U : Type*) [NormedAddCommGroup S] [NormedAddCommGroup U] := ℕ →ᵇ (S×U)

def seedValue (a : S) (n : ℕ) : S×U := if n=0 then (a,0) else 0

theorem seedValue_bound (a : S) (n : ℕ) : ‖seedValue (U := U) a n‖≤‖a‖ := by
  unfold seedValue
  split_ifs <;> simp

def seedSequence (a : S) : Seq S U :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (seedValue a) ‖a‖ (seedValue_bound a)

theorem seedSequence_apply (a : S) (n : ℕ) : seedSequence (U := U) a n=seedValue a n := rfl

def seedLinear : S →ₗ[ℝ] Seq S U where
  toFun := seedSequence
  map_add' a b := by
    ext n <;> simp only [seedSequence_apply,BoundedContinuousFunction.add_apply,seedValue]
    all_goals split_ifs <;> simp
  map_smul' c a := by
    ext n <;> simp only [seedSequence_apply,BoundedContinuousFunction.smul_apply,seedValue]
    all_goals split_ifs <;> simp

theorem seedLinear_bound (a : S) : ‖seedLinear (U := U) a‖≤1*‖a‖ := by
  rw [one_mul]
  exact (BoundedContinuousFunction.norm_le (norm_nonneg a)).mpr (seedValue_bound a)

def seedMap : S →L[ℝ] Seq S U := (seedLinear : S →ₗ[ℝ] Seq S U).mkContinuous 1 (seedLinear_bound (U := U))

theorem seedMap_apply (a : S) (n : ℕ) : seedMap (U := U) a n=seedValue a n := rfl

def linearValue (A : S →L[ℝ] S) (B : U →L[ℝ] U) (w : Seq S U) (n : ℕ) : S×U :=
  ((match n with | 0 => 0 | k+1 => A (w k).1), B (w (n+1)).2)

theorem linearValue_bound (A : S →L[ℝ] S) (B : U →L[ℝ] U) (w : Seq S U) (n : ℕ) :
    ‖linearValue A B w n‖≤max ‖A‖ ‖B‖*‖w‖ := by
  have hs (k : ℕ) : ‖A (w k).1‖≤max ‖A‖ ‖B‖*‖w‖ := by
    exact (A.le_opNorm _).trans (mul_le_mul (le_max_left _ _)
      ((norm_fst_le _).trans (w.norm_coe_le_norm k)) (norm_nonneg _) (le_max_of_le_left (norm_nonneg A)))
  have hu (k : ℕ) : ‖B (w k).2‖≤max ‖A‖ ‖B‖*‖w‖ := by
    exact (B.le_opNorm _).trans (mul_le_mul (le_max_right _ _)
      ((norm_snd_le _).trans (w.norm_coe_le_norm k)) (norm_nonneg _) (le_max_of_le_left (norm_nonneg A)))
  cases n with
  | zero => simpa only [linearValue,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] using hu 1
  | succ k => exact max_le (hs k) (hu (k+2))

def linearSequence (A : S →L[ℝ] S) (B : U →L[ℝ] U) (w : Seq S U) : Seq S U :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (linearValue A B w)
    (max ‖A‖ ‖B‖*‖w‖) (linearValue_bound A B w)

theorem linearSequence_apply (A : S →L[ℝ] S) (B : U →L[ℝ] U) (w : Seq S U) (n : ℕ) :
    linearSequence A B w n=linearValue A B w n := rfl

def linearOperator (A : S →L[ℝ] S) (B : U →L[ℝ] U) : Seq S U →ₗ[ℝ] Seq S U where
  toFun := linearSequence A B
  map_add' w v := by
    ext n <;> cases n <;> simp [linearSequence_apply,linearValue]
  map_smul' c w := by
    ext n <;> cases n <;> simp [linearSequence_apply,linearValue]

theorem linearOperator_bound (A : S →L[ℝ] S) (B : U →L[ℝ] U) (w : Seq S U) :
    ‖linearOperator A B w‖≤max ‖A‖ ‖B‖*‖w‖ := by
  exact (BoundedContinuousFunction.norm_le
    (mul_nonneg (le_max_of_le_left (norm_nonneg A)) (norm_nonneg w))).mpr (linearValue_bound A B w)

def linearStep (A : S →L[ℝ] S) (B : U →L[ℝ] U) : Seq S U →L[ℝ] Seq S U :=
  (linearOperator A B).mkContinuous (max ‖A‖ ‖B‖) (linearOperator_bound A B)

theorem linearStep_apply (A : S →L[ℝ] S) (B : U →L[ℝ] U) (w : Seq S U) (n : ℕ) :
    linearStep A B w n=linearValue A B w n := rfl

theorem linearStep_norm (A : S →L[ℝ] S) (B : U →L[ℝ] U) :
    ‖linearStep A B‖≤max ‖A‖ ‖B‖ :=
  (linearOperator A B).mkContinuous_norm_le (le_max_of_le_left (norm_nonneg A))
    (linearOperator_bound A B)

theorem linearStep_norm_lt (A : S →L[ℝ] S) (B : U →L[ℝ] U)
    (hA : ‖A‖<1) (hB : ‖B‖<1) : ‖linearStep A B‖<1 :=
  (linearStep_norm A B).trans_lt (max_lt hA hB)

end BfgsVerification.AnalyticStableGraph
