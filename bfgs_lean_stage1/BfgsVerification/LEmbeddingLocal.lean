import BfgsVerification.LEmbeddingObjective

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.LEmbedding
open SeedOrbit SeedCycle LScalarGeometric

def copyCenter (n : ℕ) : Vec 2 := scale n • center
def copyPoint (n : ℕ) (y : Vec 2) : Vec 2 := copyCenter n+scale n • y
def offset : ℝ := 1+mu/2*sqNorm center
def localDomain : Set (Vec 2) := {y | ‖y‖<1 ∧ ∀i : Fin 3,|dot (slope i) y|<1/2}

theorem localDomain_open : IsOpen localDomain := by
  have h : IsOpen {y : Vec 2 | ∀i : Fin 3,|dot (slope i) y|<1/2} := by
    rw [show {y : Vec 2 | ∀i : Fin 3,|dot (slope i) y|<1/2}=
      ⋂i : Fin 3,{y : Vec 2 | |dot (slope i) y|<1/2} from by ext y; simp]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_lt _ continuous_const
    exact (gradientFunctional (slope i)).continuous.abs
  exact (isOpen_lt continuous_norm continuous_const).inter h

theorem zero_mem_localDomain : (0 : Vec 2)∈localDomain := by
  simp [localDomain,dot]

theorem localDomain_nhds : localDomain∈𝓝 (0 : Vec 2) := localDomain_open.mem_nhds zero_mem_localDomain

theorem copy_argument (n : ℕ) (i : Fin 3) (y : Vec 2) :
    dot (slope i) (copyPoint n y)=parameter i*scale n+scale n*dot (slope i) y := by
  change dotProduct (slope i) (scale n • center+scale n • y)=_
  rw [dotProduct_add,dotProduct_smul,dotProduct_smul]
  change scale n*parameter i+scale n*dot (slope i) y=_
  ring

theorem scalar_copy (n : ℕ) (i : Fin 3) {y : Vec 2} (hy : |dot (slope i) y|≤1/2) :
    residualBranch i.castSucc (copyPoint n y)=(scale n)^2*(1+dot (slope i) y) := by
  rw [residualBranch_old,copy_argument]
  have hh : |scale n*dot (slope i) y|≤scale n/2 := by
    rw [abs_mul,abs_of_pos (scale_pos n)]
    nlinarith [mul_le_mul_of_nonneg_left hy (scale_pos n).le]
  rw [LScalar.phi_plateau (parameter_bounds i).1.le (parameter_bounds i).2.le n hh]
  ring

theorem old_residual_copy_positive (n : ℕ) (i : Fin 3) {y : Vec 2} (hy : y∈localDomain) :
    0<residualBranch i.castSucc (copyPoint n y) := by
  rw [scalar_copy n i (hy.2 i).le]
  have hh := (abs_lt.mp (hy.2 i)).1
  exact mul_pos (sq_pos_of_pos (scale_pos n)) (by linarith)

theorem last_residual_copy_negative (n : ℕ) {y : Vec 2} (hy : y∈localDomain) :
    residualBranch 3 (copyPoint n y)<0 := by
  have hv : y 1<1 := (le_abs_self _).trans_lt ((norm_le_pi_norm y 1).trans_lt hy.1)
  change scale n*(-32)+scale n*y 1<0
  have hh := mul_neg_of_pos_of_neg (scale_pos n) (show -32+y 1<0 by linarith)
  nlinarith

theorem quadratic_copy (n : ℕ) (i : Fin 3) (y : Vec 2) :
    LQuadraticSeed.quadratic mu (copyPoint n y)+(scale n)^2*(1+dot (slope i) y)=
      (scale n)^2*(offset+LQuadraticSeed.branch mu i y) := by
  unfold LQuadraticSeed.branch LQuadraticSeed.quadratic offset copyPoint copyCenter slope sqNorm dot
  simp only [Fin.sum_univ_two,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem branch_copy (n : ℕ) (i : Fin 3) {y : Vec 2} (hy : y∈localDomain) :
    branch i.castSucc (copyPoint n y)=(scale n)^2*(offset+LQuadraticSeed.branch mu i y) := by
  rw [branch,scalar_copy n i (hy.2 i).le]
  exact quadratic_copy n i y

theorem seed_branch_le (i : Fin 3) (y : Vec 2) :
    LQuadraticSeed.branch mu i y≤LQuadraticSeed.objective mu y :=
  add_le_add_left (LQuadraticSeed.seed_branch_le i y) _

theorem local_model (n : ℕ) {y : Vec 2} (hy : y∈localDomain) :
    objective (copyPoint n y)=(scale n)^2*(offset+LQuadraticSeed.objective mu y) := by
  apply le_antisymm
  · apply objective_le
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have h3 : branch 3 (copyPoint n y)<branch 0 (copyPoint n y) := by
        have hn := last_residual_copy_negative n hy
        have hp : 0<residualBranch 0 (copyPoint n y) := old_residual_copy_positive n 0 hy
        change LQuadraticSeed.quadratic mu (copyPoint n y)+residualBranch 3 (copyPoint n y)<
          LQuadraticSeed.quadratic mu (copyPoint n y)+residualBranch 0 (copyPoint n y)
        linarith
      apply h3.le.trans
      change branch (Fin.castSucc (0 : Fin 3)) (copyPoint n y)≤_
      rw [branch_copy n 0 hy]
      exact mul_le_mul_of_nonneg_left (add_le_add_left (seed_branch_le 0 y) _) (sq_nonneg _)
    · rw [branch_copy n j hy]
      exact mul_le_mul_of_nonneg_left (add_le_add_left (seed_branch_le j y) _) (sq_nonneg _)
  · have hs : SeedOrbit.objective seedC seedD y≤
        objective (copyPoint n y)/(scale n)^2-offset-LQuadraticSeed.quadratic mu y := by
      apply LQuadraticSeed.seed_objective_le
      intro i
      have hi := branch_le i.castSucc (copyPoint n y)
      rw [branch_copy n i hy] at hi
      have hh : offset+LQuadraticSeed.branch mu i y≤objective (copyPoint n y)/(scale n)^2 :=
        (le_div_iff₀ (sq_pos_of_pos (scale_pos n))).mpr (by nlinarith [hi])
      dsimp [LQuadraticSeed.branch] at hh
      linarith
    have hh := (le_div_iff₀ (sq_pos_of_pos (scale_pos n))).mp
      (show offset+LQuadraticSeed.objective mu y≤objective (copyPoint n y)/(scale n)^2 by
        dsimp [LQuadraticSeed.objective]
        linarith)
    nlinarith

theorem offset_pos : 0<offset := by
  rw [offset,center_sqNorm]
  norm_num [mu]

theorem center_value (n : ℕ) : objective (copyCenter n)=(scale n)^2*offset := by
  have hh := local_model n (y := (0 : Vec 2)) zero_mem_localDomain
  simpa only [copyPoint,smul_zero,add_zero,LQuadraticSeed.objective_zero] using hh

theorem center_value_pos (n : ℕ) : 0<objective (copyCenter n) := by
  rw [center_value]
  exact mul_pos (sq_pos_of_pos (scale_pos n)) offset_pos

theorem copyCenter_tendsto : Tendsto copyCenter atTop (𝓝 (0 : Vec 2)) := by
  simpa only [copyCenter,zero_smul] using LScalar.scale_tendsto_zero.smul_const center

theorem copyPoint_tendsto (y : Vec 2) : Tendsto (fun n => copyPoint n y) atTop (𝓝 (0 : Vec 2)) := by
  simpa only [copyPoint,zero_smul,zero_add] using copyCenter_tendsto.add (LScalar.scale_tendsto_zero.smul_const y)

end BfgsVerification.LEmbedding
