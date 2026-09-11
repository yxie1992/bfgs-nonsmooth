import BfgsVerification.DBoxDenominators
import BfgsVerification.DEmbeddingTarget

noncomputable section
open scoped Topology
open Filter
namespace BfgsVerification.DEuclideanLocality
open SeedOrbit SeedCycle
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem euclidean_add (x y : Vec 2) : euclideanVector (x+y)=euclideanVector x+euclideanVector y := rfl

theorem euclidean_smul (t : ℝ) (x : Vec 2) : euclideanVector (t • x)=t • euclideanVector x := rfl

def maxTrialNorm : ℝ := Finset.univ.sup' Finset.univ_nonempty
  (fun q : Fin 9 => ‖euclideanVector (trial seedC seedD seedRatio (trialPhase q) (trialLength q))‖)

theorem trial_le_max (q : Fin 9) :
    ‖euclideanVector (trial seedC seedD seedRatio (trialPhase q) (trialLength q))‖  ≤  maxTrialNorm :=
  Finset.le_sup' (fun q : Fin 9 =>
    ‖euclideanVector (trial seedC seedD seedRatio (trialPhase q) (trialLength q))‖) (Finset.mem_univ q)

theorem max_nonneg : 0  ≤  maxTrialNorm := (norm_nonneg _).trans (trial_le_max 0)

theorem initial_sq_eq : ‖euclideanVector (point seedC seedD seedRatio 0)‖^2=
    DAuxiliaryRaw.initial_square seedC seedD := by
  rw [FrameNorms.euclidean_norm_sq]
  change sqNorm (point seedC seedD seedRatio 0)=_
  simp only [sqNorm,Fin.sum_univ_two,point,initialPoint,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,DAuxiliaryRaw.initial_square,
    seedRatio,AlgebraicSeed.ratio,AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U,div_eq_mul_inv]
  ring

theorem fourth_trial_sq_eq : ‖euclideanVector (trial seedC seedD seedRatio 2 1)‖^2=
    DAuxiliaryRaw.trial_four_square seedC seedD := by
  rw [FrameNorms.euclidean_norm_sq]
  change sqNorm (trial seedC seedD seedRatio 2 1)=_
  simp only [sqNorm,Fin.sum_univ_two,trial,point,initialPoint,direction,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,DAuxiliaryRaw.trial_four_square,
    seedRatio,AlgebraicSeed.ratio,AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U,div_eq_mul_inv]
  norm_num
  ring

theorem initial_norm_lt_fourth_trial :
    ‖euclideanVector (point seedC seedD seedRatio 0)‖ < 
      ‖euclideanVector (trial seedC seedD seedRatio 2 1)‖ := by
  have h := DBoxDenominators.auxiliary_bounds AlgebraicSeed.root_spec.1
  rw [←initial_sq_eq] at h
  rw [←fourth_trial_sq_eq] at h
  nlinarith [norm_nonneg (euclideanVector (point seedC seedD seedRatio 0)),
    norm_nonneg (euclideanVector (trial seedC seedD seedRatio 2 1))]

theorem base_le_max (j : Fin 3) : ‖euclideanVector (point seedC seedD seedRatio j)‖  ≤  maxTrialNorm := by
  fin_cases j
  · exact initial_norm_lt_fourth_trial.le.trans (trial_le_max 4)
  · have h := trial_le_max 0
    change ‖euclideanVector (trial seedC seedD seedRatio 0 (length 0))‖  ≤  maxTrialNorm at h
    rwa [phase_zero_step] at h
  · have h := trial_le_max 3
    change ‖euclideanVector (trial seedC seedD seedRatio 1 (length 1))‖  ≤  maxTrialNorm at h
    rwa [phase_one_step] at h

theorem scaled_le {x : Vec 2} {t : ℝ} (ht : 0 ≤ t) (hu : t ≤ 1)
    (hx : ‖euclideanVector x‖  ≤  maxTrialNorm) : ‖euclideanVector (t • x)‖  ≤  maxTrialNorm := by
  rw [euclidean_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
  exact (mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans (by simpa using hx)

theorem orbit_le_max (k : ℕ) : ‖euclideanVector (orbitPoint k)‖  ≤  maxTrialNorm :=
  scaled_le (orbitScale_pos k).le (orbitScale_le_one k) (base_le_max (phase k))

theorem actual_trial_eq_scaled (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    SeedEmbedding.trialPoint k q=
      orbitScale k • trial seedC seedD seedRatio (trialPhase q) (trialLength q) := by
  simp only [SeedEmbedding.trialPoint,orbitPoint,orbitMetric,orbitGradient,
    bfgsStep_scale_matrix,source_direction,one_smul]
  rw [smul_comm (trialLength q) (orbitScale k),←smul_add,hq]
  rfl

theorem actual_trial_le_max (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    ‖euclideanVector (SeedEmbedding.trialPoint k q)‖  ≤  maxTrialNorm := by
  rw [actual_trial_eq_scaled k q hq]
  exact scaled_le (orbitScale_pos k).le (orbitScale_le_one k) (trial_le_max q)

def sourceBound (n : ℕ) : ℝ := DScalarGeometric.scale n*‖euclideanVector (![2,-32] : Vec 2)‖+
    (DScalarGeometric.scale n)^2*maxTrialNorm

theorem translated_bound (n : ℕ) {z : Vec 2} (hz : ‖euclideanVector z‖  ≤  maxTrialNorm) :
    ‖euclideanVector (DEmbedding.center n+(DScalarGeometric.scale n)^2 • z)‖ ≤ sourceBound n := by
  have hn := norm_add_le (euclideanVector (DEmbedding.center n))
    (euclideanVector ((DScalarGeometric.scale n)^2 • z))
  rw [←euclidean_add] at hn
  rw [DEmbedding.center,euclidean_smul,norm_smul,euclidean_smul,norm_smul,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (DScalarGeometric.scale_pos n),
    abs_of_nonneg (sq_nonneg _)] at hn
  exact hn.trans (add_le_add_left (mul_le_mul_of_nonneg_left hz (sq_nonneg _)) _)

theorem source_bound_tendsto : Tendsto sourceBound atTop (𝓝 0) := by
  have h := ((DEmbedding.scale_tendsto.mul_const ‖euclideanVector (![2,-32] : Vec 2)‖).add
    ((DEmbedding.scale_tendsto.pow 2).mul_const maxTrialNorm))
  simpa only [sourceBound,zero_mul,zero_pow (by decide : 2≠0),add_zero] using h

/-- Literal D448, with the maximum over the original nine actual trials;
the initial accepted point is included by a separately proved norm comparison. -/
def EuclideanLocalityTarget : Prop :=
  (∀n k : ℕ, ‖euclideanVector (SeedEmbedding.point (DEmbedding.center n)
    ((DScalarGeometric.scale n)^2) k)‖ ≤ sourceBound n) ∧
  (∀n k : ℕ, ∀q : Fin 9, trialPhase q=phase k →
    ‖euclideanVector (DEmbedding.center n+(DScalarGeometric.scale n)^2 • SeedEmbedding.trialPoint k q)‖
       ≤ sourceBound n) ∧ Tendsto sourceBound atTop (𝓝 0)

theorem euclideanLocality : EuclideanLocalityTarget :=
  ⟨fun n k => translated_bound n (orbit_le_max k),
    fun n k q hq => translated_bound n (actual_trial_le_max k q hq),source_bound_tendsto⟩

end BfgsVerification.DEuclideanLocality
