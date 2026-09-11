import BfgsVerification.LActualCopies

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.LActualCopies
open SeedOrbit SeedCycle LScalarGeometric

variable {F : Vec 2 → ℝ}

def uniformBound (m : ℕ) : ℝ := scale m*(‖LEmbedding.center‖+1)

theorem uniformBound_tendsto : Tendsto uniformBound atTop (𝓝 0) := by
  simpa only [uniformBound,zero_mul] using LScalar.scale_tendsto_zero.mul_const (‖LEmbedding.center‖+1)

theorem point_norm_bound (D : CopyData F) (m k : ℕ) : ‖(family D m).x k‖≤uniformBound m := by
  rw [point_formula]
  have hh := norm_add_le (scale m • LEmbedding.center) (scale m • LSeedCopies.run.x k)
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (scale_pos m)] at hh
  have hb := mul_le_mul_of_nonneg_left (LSeedCopies.point_in k).1.le (scale_pos m).le
  change ‖scale m • LEmbedding.center+scale m • LSeedCopies.run.x k‖≤scale m*(‖LEmbedding.center‖+1)
  nlinarith

theorem trial_norm_bound (D : CopyData F) (m k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    ‖(family D m).x k+trialLength q • bfgsStep ((family D m).H k) ((family D m).g k) 1‖≤uniformBound m :=
  D.query_norm_bound LSeedCopies.run LSeedCopies.point_in m k (trialLength q) 1
    (LSeedCopies.run_query_conditions k q hq).1.1.le

theorem uniform_locality (D : CopyData F) (U : Set (Vec 2)) (hU : U∈𝓝 (0 : Vec 2)) :
    ∃N : ℕ,∀m≥N,∀k,(family D m).x k∈U ∧ ∀q : Fin 9,trialPhase q=phase k →
      (family D m).x k+trialLength q • bfgsStep ((family D m).H k) ((family D m).g k) 1∈U := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  have he : ∀ᶠ m in atTop,uniformBound m<ε := uniformBound_tendsto.eventually (gt_mem_nhds hε)
  obtain ⟨N,hN⟩ := eventually_atTop.1 he
  refine ⟨N,?_⟩
  intro m hm k
  constructor
  · apply hball
    simpa only [Metric.mem_ball,dist_zero_right] using (point_norm_bound D m k).trans_lt (hN m hm)
  · intro q hq
    apply hball
    simpa only [Metric.mem_ball,dist_zero_right] using (trial_norm_bound D m k q hq).trans_lt (hN m hm)

end BfgsVerification.LActualCopies
