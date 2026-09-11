import BfgsVerification.LStepEmbeddingPolyhedral
import Mathlib.Analysis.Convex.Extrema

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.LStepEmbedding
open LEmbedding LScalarGeometric SeedCycle SeedOrbit

def copyPoint (n : ℕ) (y : Vec 2) : Vec 2 := scale n • LEmbedding.center+scale n • y
def copyConstant : ℝ := 1+mu/2*sqNorm LEmbedding.center
def copyNeighborhood : Set (Vec 2) := {y | (∀ i : Fin 3, |dot (slope i) y|<1/2) ∧ y 1<1}

theorem copyNeighborhood_open : IsOpen copyNeighborhood := by
  have hset : {y : Vec 2 | ∀ i : Fin 3, |dot (slope i) y|<(1/2 : ℝ)}=
      ⋂ i : Fin 3, {y : Vec 2 | |dot (slope i) y|<(1/2 : ℝ)} := by ext y; simp
  have hopen : IsOpen (⋂ i : Fin 3, {y : Vec 2 | |dot (slope i) y|<(1/2 : ℝ)}) := by
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt ((gradientFunctional (slope i)).continuous.abs) continuous_const
  have hfirst : IsOpen {y : Vec 2 | ∀ i : Fin 3, |dot (slope i) y|<(1/2 : ℝ)} := hset.symm ▸ hopen
  exact hfirst.inter (isOpen_lt (continuous_apply (1 : Fin 2)) continuous_const)

theorem copyNeighborhood_zero : (0 : Vec 2) ∈ copyNeighborhood := by
  constructor
  · intro i
    norm_num [dot]
  · norm_num

theorem copyNeighborhood_of_norm {y : Vec 2} (hy : ‖y‖<1)
    (hp : ∀ i : Fin 3, |dot (slope i) y|<1/2) : y∈copyNeighborhood := by
  refine ⟨hp,?_⟩
  have hn : |y 1|≤‖y‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y (1 : Fin 2)
  exact (le_abs_self _).trans_lt (hn.trans_lt hy)

theorem copyPoint_pairing (n : ℕ) (y : Vec 2) (i : Fin 3) :
    dot (slope i) (copyPoint n y)=parameter i*scale n+scale n*dot (slope i) y := by
  change dotProduct (slope i) (scale n • LEmbedding.center+scale n • y)=_
  rw [dotProduct_add,dotProduct_smul,dotProduct_smul]
  change scale n*parameter i+scale n*dot (slope i) y=_
  ring

theorem scalar_copy (n : ℕ) {y : Vec 2} (hy : y ∈ copyNeighborhood) (i : Fin 3) :
    LScalarStep.phi (parameter i) (dot (slope i) (copyPoint n y))=
      (scale n)^2*(1+dot (slope i) y) := by
  have hh : |scale n*dot (slope i) y|≤scale n/2 := by
    rw [abs_mul,abs_of_pos (scale_pos n)]
    have h := mul_le_mul_of_nonneg_left (hy.1 i).le (scale_pos n).le
    nlinarith
  rw [copyPoint_pairing,LScalarStep.phi_plateau (parameter_bounds i).1.le (parameter_bounds i).2.le n hh]
  ring

theorem branch_copy (n : ℕ) {y : Vec 2} (hy : y ∈ copyNeighborhood) (i : Fin 3) :
    branch i.castSucc (copyPoint n y)=(scale n)^2*(copyConstant+LQuadraticSeed.branch mu i y) := by
  rw [branch,residualBranch_old,scalar_copy n hy i]
  unfold copyPoint copyConstant LQuadraticSeed.branch LQuadraticSeed.quadratic LEmbedding.slope
  simp only [sqNorm,dot,Fin.sum_univ_two,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem copyPoint_last_negative (n : ℕ) {y : Vec 2} (hy : y ∈ copyNeighborhood) :
    copyPoint n y 1<0 := by
  have hy1 := hy.2
  change y 1<1 at hy1
  have hs := scale_pos n
  have he : copyPoint n y 1=scale n*(-32+y 1) := by
    simp only [copyPoint,LEmbedding.center,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_one,Matrix.cons_val_zero]
    ring
  rw [he]
  exact mul_neg_of_pos_of_neg hs (by linarith)

theorem fourth_lt_first_copy (n : ℕ) {y : Vec 2} (hy : y ∈ copyNeighborhood) :
    branch 3 (copyPoint n y)<branch 0 (copyPoint n y) := by
  have hneg := copyPoint_last_negative n hy
  have hnon := LScalarStep.phi_nonnegative (parameter 0) (dot (slope 0) (copyPoint n y))
  change LQuadraticSeed.quadratic mu (copyPoint n y)+copyPoint n y 1<
    LQuadraticSeed.quadratic mu (copyPoint n y)+LScalarStep.phi (parameter 0) (dot (slope 0) (copyPoint n y))
  linarith

theorem objective_copy (n : ℕ) {y : Vec 2} (hy : y ∈ copyNeighborhood) :
    objective (copyPoint n y)=(scale n)^2*(copyConstant+LQuadraticSeed.objective mu y) := by
  have hs : 0≤(scale n)^2 := sq_nonneg _
  apply le_antisymm
  · apply objective_le
    intro i
    have hle (j : Fin 3) : branch j.castSucc (copyPoint n y)≤
        (scale n)^2*(copyConstant+LQuadraticSeed.objective mu y) := by
      rw [branch_copy n hy j]
      exact mul_le_mul_of_nonneg_left (add_le_add_left (LQuadraticSeed.branch_le_objective mu j y) _) hs
    fin_cases i
    · exact hle 0
    · exact hle 1
    · exact hle 2
    · exact (fourth_lt_first_copy n hy).le.trans (hle 0)
  · obtain ⟨i,hi⟩ := LQuadraticSeed.objective_eq_branch mu y
    rw [hi,← branch_copy n hy i]
    exact branch_le i.castSucc _

theorem objective_copy_eventually (n : ℕ) :
    (fun y => objective (copyPoint n y)) =ᶠ[𝓝 (0 : Vec 2)]
      (fun y => (scale n)^2*(copyConstant+LQuadraticSeed.objective mu y)) := by
  filter_upwards [copyNeighborhood_open.mem_nhds copyNeighborhood_zero] with y hy
  exact objective_copy n hy


theorem copyConstant_positive : 0<copyConstant := by
  unfold copyConstant
  have h := mul_nonneg (div_nonneg mu_pos.le (by norm_num : (0 : ℝ)≤2)) (sqNorm_nonneg LEmbedding.center)
  linarith

theorem objective_copy_center (n : ℕ) :
    objective (copyPoint n 0)=(scale n)^2*copyConstant := by
  rw [objective_copy n copyNeighborhood_zero,LQuadraticSeed.objective_zero,add_zero]

theorem objective_copy_center_positive (n : ℕ) : 0<objective (copyPoint n 0) := by
  rw [objective_copy_center]
  exact mul_pos (sq_pos_of_pos (scale_pos n)) copyConstant_positive

theorem copy_center_nonstationary (n : ℕ) :
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential objective (copyPoint n 0) := by
  intro hzero
  have hmin := ConvexSubdifferential.zero_mem_iff_global_minimum.mp hzero
  have hlocal : IsLocalMin (LQuadraticSeed.objective mu) (0 : Vec 2) := by
    filter_upwards [copyNeighborhood_open.mem_nhds copyNeighborhood_zero] with y hy
    have he := hmin (copyPoint n y)
    rw [objective_copy n copyNeighborhood_zero,objective_copy n hy] at he
    exact (add_le_add_iff_left copyConstant).mp ((mul_le_mul_left (sq_pos_of_pos (scale_pos n))).mp he)
  have hglobal := IsMinOn.of_isLocalMin_of_convex_univ hlocal (LQuadraticSeed.objective_convex mu_pos.le)
  exact LQuadraticSeed.origin_nonstationary mu_pos.le
    (ConvexSubdifferential.zero_mem_iff_global_minimum.mpr hglobal)

end BfgsVerification.LStepEmbedding
