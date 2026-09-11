import BfgsVerification.AlgebraicSeedOrbitData
noncomputable section
open scoped BigOperators
open Matrix
namespace BfgsVerification.SeedOrbit
open AlgebraicSeed SeedCycle PlanarUpdate

theorem source_middle_matrix :
    update M1 g1 (g2 (root 0) (root 1)) (1/4) = middleMatrix (beta (root 0) (root 1)) (root 0) (root 1) := by
  obtain ⟨hU,hV,hR,hK,_,_,hA,_,_⟩ := box_denominators_and_ratio root_spec.1
  rw [← source_parameters.1]
  exact middle_update (beta_ne_zero hU.ne' hV.ne' hA.ne' hR.ne' hK.ne') hA.ne'

theorem source_last_step :
    bfgsStep (update M1 g1 (g2 (root 0) (root 1)) (1/4)) (g2 (root 0) (root 1)) (1/16) =
      ratio (root 0) (root 1) • (g0-g2 (root 0) (root 1)) := by
  obtain ⟨hU,hV,hR,_,_,hY,hA,_,_⟩ := box_denominators_and_ratio root_spec.1
  rw [source_middle_matrix,← source_parameters.2.1,last_step_generic hU.ne' hV.ne' hA.ne' hR.ne' hY.ne',source_parameters.2.2]

theorem bfgsStep_scale_alpha {n : ℕ} (H : Mat n) (g : Vec n) (a t : ℝ) :
    bfgsStep H g (t*a)=t • bfgsStep H g a := by
  simp only [bfgsStep,smul_smul,neg_mul,mul_neg]

theorem source_direction (j : Fin 3) (a : ℝ) :
    bfgsStep (metric (root 0) (root 1) j) (gradient (root 0) (root 1) j) a =
      a • direction (root 0) (root 1) (ratio (root 0) (root 1)) j := by
  fin_cases j
  · ext i
    fin_cases i <;> norm_num [metric,gradient,direction,g0,bfgsStep,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  · change bfgsStep M1 g1 a = _
    rw [middle_step]
    ext i
    fin_cases i <;> norm_num [direction] <;> ring
  · change bfgsStep (update M1 g1 (g2 (root 0) (root 1)) (1/4)) (g2 (root 0) (root 1)) a = _
    have ha : a=(16*a)*(1/16) := by ring
    rw [ha,bfgsStep_scale_alpha,source_last_step]
    ext i
    fin_cases i <;> norm_num [g0,g2,direction] <;> ring

theorem source_metric_posDef (j : Fin 3) : (metric (root 0) (root 1) j).PosDef := by
  have hM1 : M1.PosDef := by
    rw [← first_update]
    apply inverseBFGS_posDef Matrix.PosDef.one
    rw [first_step]
    norm_num [dot,g0,g1,Fin.sum_univ_two]
  fin_cases j
  · exact Matrix.PosDef.one
  · exact hM1
  · change (update M1 g1 (g2 (root 0) (root 1)) (1/4)).PosDef
    apply inverseBFGS_posDef hM1
    rw [middle_curvature]
    have hA := (box_denominators_and_ratio root_spec.1).2.2.2.2.2.2.1
    positivity

theorem phase_zero_step (c d r : ℝ) : trial c d r 0 (length 0)=point c d r 1 := by
  change initialPoint c d r+1 • (![-1,0] : Vec 2)=initialPoint c d r+![-1,0]
  rw [one_smul]

theorem phase_one_step (c d r : ℝ) : trial c d r 1 (length 1)=point c d r 2 := by
  change initialPoint c d r+![-1,0]+(1/4:ℝ) • ![127/256,1/16]=initialPoint c d r+![-897/1024,1/64]
  ext i
  fin_cases i <;> norm_num [Matrix.vecHead,Matrix.vecTail] <;> ring

theorem phase_two_step (c d r : ℝ) (hr : 1-r ≠ 0) :
    trial c d r 2 (length 2)=r • point c d r 0 := by
  change initialPoint c d r+![-897/1024,1/64]+(1/16:ℝ) • ![16*r*(1-c),-16*r*d]=r • initialPoint c d r
  ext i
  fin_cases i <;> norm_num [initialPoint]
  all_goals field_simp [hr]
  all_goals ring

theorem source_phase_two_step :
    trial (root 0) (root 1) (ratio (root 0) (root 1)) 2 (length 2) =
      ratio (root 0) (root 1) • point (root 0) (root 1) (ratio (root 0) (root 1)) 0 := by
  apply phase_two_step
  have hh := (box_denominators_and_ratio root_spec.1).2.2.2.2.2.2.2.2
  linarith

theorem source_metric_zero_update :
    update (metric (root 0) (root 1) 0) (gradient (root 0) (root 1) 0)
      (gradient (root 0) (root 1) 1) (length 0)=metric (root 0) (root 1) 1 := first_update

theorem source_metric_one_update :
    update (metric (root 0) (root 1) 1) (gradient (root 0) (root 1) 1)
      (gradient (root 0) (root 1) 2) (length 1)=metric (root 0) (root 1) 2 := rfl

theorem source_metric_two_update :
    update (metric (root 0) (root 1) 2) (gradient (root 0) (root 1) 2)
      (gradient (root 0) (root 1) 0) (length 2)=
        ratio (root 0) (root 1) • metric (root 0) (root 1) 0 := by
  change update (update M1 g1 (g2 (root 0) (root 1)) (1/4)) (g2 (root 0) (root 1)) g0 (1/16)=ratio (root 0) (root 1) • (1 : Mat 2)
  simpa only [first_update] using source_cycle

end BfgsVerification.SeedOrbit
