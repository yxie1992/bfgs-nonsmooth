import BfgsVerification.DAuxiliaryRaw
import BfgsVerification.DEmbeddingObjective

noncomputable section
namespace BfgsVerification.DBoxDenominators
open IntervalBounds SeedCycle SeedOrbit
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem fine_box {x : Vec 2} (hx : ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius) :
    Bounds (318481427627118630646451312501/10^30) (x 0)
      (318481427627118630646451312504/10^30) ∧
    Bounds (-1025232119675748725481350870015/10^30) (x 1)
      (-1025232119675748725481350870012/10^30) := by
  have hc : |x 0-AlgebraicSeed.center 0|≤AlgebraicSeed.radius :=
    (show |x 0-AlgebraicSeed.center 0|≤‖x-AlgebraicSeed.center‖ from
      norm_le_pi_norm (x-AlgebraicSeed.center) 0).trans hx
  have hd : |x 1-AlgebraicSeed.center 1|≤AlgebraicSeed.radius :=
    (show |x 1-AlgebraicSeed.center 1|≤‖x-AlgebraicSeed.center‖ from
      norm_le_pi_norm (x-AlgebraicSeed.center) 1).trans hx
  obtain ⟨hc0,hc1⟩ := abs_le.mp hc
  obtain ⟨hd0,hd1⟩ := abs_le.mp hd
  norm_num [AlgebraicSeed.center,AlgebraicSeed.radius] at hc0 hc1 hd0 hd1
  unfold Bounds
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> linarith

theorem auxiliary_bounds {x : Vec 2} (hx : ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius) :
    DAuxiliaryRaw.initial_square (x 0) (x 1)<1 ∧
    1<DAuxiliaryRaw.trial_four_square (x 0) (x 1) ∧
    (1/100 : ℝ)<DAuxiliaryRaw.last_curvature (x 0) (x 1) := by
  obtain ⟨hc,hd⟩ := fine_box hx
  apply DAuxiliaryRaw.bounds
  · convert hc using 1 <;> norm_num
  · convert hd using 1 <;> norm_num

def lastCurvature (c d : ℝ) : ℝ :=
  dot (g0-g2 c d) (bfgsStep (update M1 g1 (g2 c d) (1/4)) (g2 c d) (1/16))

theorem lastCurvature_eq_raw {c d : ℝ} (hA : AlgebraicSeed.U c d+129≠0) :
    lastCurvature c d=DAuxiliaryRaw.last_curvature c d := by
  unfold lastCurvature
  rw [middle_update (by norm_num) hA]
  simp only [bfgsStep,middleMatrix,Matrix.add_mulVec,Matrix.smul_mulVec_assoc,
    outer_mulVec,dot_smul_right]
  norm_num only [dot,Fin.sum_univ_two,g0,g2,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.add_apply]
  simp only [DAuxiliaryRaw.last_curvature,AlgebraicSeed.U,div_eq_mul_inv,mul_inv_rev,inv_pow]
  have hA' : 127*c+16*d+129≠0 := by simpa only [AlgebraicSeed.U] using hA
  field_simp [hA']
  ring

theorem original_box_last_curvature {x : Vec 2}
    (hx : ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius) :
    (1/100 : ℝ)<lastCurvature (x 0) (x 1) := by
  have hA := (AlgebraicSeed.box_denominators_and_ratio hx).2.2.2.2.2.2.1
  rw [lastCurvature_eq_raw hA.ne']
  exact (auxiliary_bounds hx).2.2

theorem original_box_metrics_posDef {x : Vec 2}
    (hx : ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius) (j : Fin 3) :
    (metric (x 0) (x 1) j).PosDef := by
  have hM1 : M1.PosDef := by simpa only [metric,Matrix.cons_val_one] using source_metric_posDef 1
  have hA := (AlgebraicSeed.box_denominators_and_ratio hx).2.2.2.2.2.2.1
  fin_cases j
  · exact Matrix.PosDef.one
  · exact hM1
  · change (update M1 g1 (g2 (x 0) (x 1)) (1/4)).PosDef
    apply inverseBFGS_posDef hM1
    rw [middle_curvature]
    positivity

theorem original_box_final_posDef {x : Vec 2}
    (hx : ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius) :
    (update (metric (x 0) (x 1) 2) (g2 (x 0) (x 1)) g0 (1/16)).PosDef := by
  apply inverseBFGS_posDef (original_box_metrics_posDef hx 2)
  exact lt_trans (by norm_num) (original_box_last_curvature hx)

theorem original_box_gradient_nonzero {x : Vec 2}
    (hx : ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius) (j : Fin 3) :
    SeedOrbit.gradient (x 0) (x 1) j≠0 := by
  have hc := (AlgebraicSeed.box_coarse hx).1
  intro hg
  have he := congrArg (fun v : Vec 2 => v 0) hg
  fin_cases j <;> norm_num [SeedOrbit.gradient,g0,g1,g2] at he
  linarith

/-- The source prescribed-length updates, including the last one, have no
curvature or positive-energy denominator zero anywhere in the original box. -/
def SourceBoxDenominatorsTarget : Prop :=
  ∀x : Vec 2, ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius →
    (∀j : Fin 3, (metric (x 0) (x 1) j).PosDef ∧
      0 < metricEnergy (metric (x 0) (x 1) j) (SeedOrbit.gradient (x 0) (x 1) j)) ∧
    0<dot (g1-g0) (bfgsStep (1 : Mat 2) g0 1) ∧
    0<dot (g2 (x 0) (x 1)-g1) (bfgsStep M1 g1 (1/4)) ∧
    (1/100 : ℝ)<lastCurvature (x 0) (x 1) ∧
    (update (metric (x 0) (x 1) 2) (g2 (x 0) (x 1)) g0 (1/16)).PosDef ∧
    0<AlgebraicSeed.ratio (x 0) (x 1) ∧ 0<1-AlgebraicSeed.ratio (x 0) (x 1)

theorem sourceBoxDenominators : SourceBoxDenominatorsTarget := by
  intro x hx
  obtain ⟨_,_,_,_,_,_,hA,hrL,hrU⟩ := AlgebraicSeed.box_denominators_and_ratio hx
  refine ⟨fun j => ⟨original_box_metrics_posDef hx j,
    metricEnergy_pos (original_box_metrics_posDef hx j) (original_box_gradient_nonzero hx j)⟩,
    ?_,?_,original_box_last_curvature hx,original_box_final_posDef hx,by linarith,by linarith⟩
  · rw [first_step]
    norm_num [dot,Fin.sum_univ_two,g0,g1]
  · rw [middle_curvature]
    positivity

end BfgsVerification.DBoxDenominators
