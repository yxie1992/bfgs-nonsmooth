import BfgsVerification.AlgebraicSeedInfiniteOrbit
import BfgsVerification.ConvexSubdifferential
noncomputable section
open scoped BigOperators Topology
open Matrix Filter
namespace BfgsVerification.SeedOrbit
open AlgebraicSeed SeedCycle

theorem period_tendsto : Tendsto period atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (3*b)] with k hk
  change b ≤ k/3
  omega

theorem orbitScale_tendsto : Tendsto orbitScale atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one source_ratio_pos_lt_one.1.le source_ratio_pos_lt_one.2).comp period_tendsto

theorem orbitPoint_tendsto : Tendsto orbitPoint atTop (𝓝 0) := by
  let C : ℝ := ∑ j : Fin 3, ‖point seedC seedD seedRatio j‖
  have hb (j : Fin 3) : ‖point seedC seedD seedRatio j‖ ≤ C := by
    exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have hbound (k : ℕ) : ‖orbitPoint k‖ ≤ orbitScale k*C := by
    rw [orbitPoint,norm_smul,Real.norm_eq_abs,abs_of_pos (orbitScale_pos k)]
    exact mul_le_mul_of_nonneg_left (hb _) (orbitScale_pos k).le
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) hbound
  simpa only [zero_mul] using orbitScale_tendsto.mul_const C

theorem objective_zero (c d : ℝ) : objective c d 0=0 := by
  unfold objective MaxAffine.Family.objective
  simp [MaxAffine.Family.branch,family,dot]

theorem orbit_value_tendsto : Tendsto (fun k => objective seedC seedD (orbitPoint k)) atTop (𝓝 0) := by
  have h := (convex_continuous (family seedC seedD).objective_convex).continuousAt.tendsto.comp orbitPoint_tendsto
  change Tendsto (fun k => objective seedC seedD (orbitPoint k)) atTop (𝓝 (objective seedC seedD 0)) at h
  simpa only [objective_zero] using h

theorem orbit_value_pos (k : ℕ) : 0 < objective seedC seedD (orbitPoint k) := by
  rw [orbitPoint,objective_scale_at_active (source_base_certificate (phase k)).active (orbitScale_pos k),
    objective_of_active (source_base_certificate (phase k)).active]
  exact mul_pos (orbitScale_pos k) (source_base_certificate (phase k)).value_pos

def downhill : Vec 2 := ![-1,16]

theorem source_downhill_pairings :
    dot (gradient seedC seedD 0) downhill = -1 ∧
      dot (gradient seedC seedD 1) downhill = -1 ∧
      dot (gradient seedC seedD 2) downhill < -1 := by
  have hc := root_tight_box.1.1
  have hd := root_tight_box.2.2
  norm_num [gradient,g0,g1,g2,downhill,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  linarith

theorem objective_downhill_ray {t : ℝ} (ht : 0 ≤ t) : objective seedC seedD (t • downhill) = -t := by
  have hpair (j : Fin 3) : dot (gradient seedC seedD j) downhill ≤ -1 := by
    fin_cases j
    · exact source_downhill_pairings.1.le
    · exact source_downhill_pairings.2.1.le
    · exact source_downhill_pairings.2.2.le
  apply le_antisymm
  · unfold objective MaxAffine.Family.objective
    apply Finset.sup'_le
    intro j _
    change dot (gradient seedC seedD j) (t • downhill)+0 ≤ -t
    rw [add_zero,dot_smul_right]
    simpa only [mul_neg_one] using mul_le_mul_of_nonneg_left (hpair j) ht
  · have hh := (family seedC seedD).branch_le 0 (t • downhill)
    change dot (gradient seedC seedD 0) (t • downhill)+0 ≤ objective seedC seedD (t • downhill) at hh
    simpa only [add_zero,dot_smul_right,source_downhill_pairings.1,mul_neg_one] using hh

theorem limit_not_stationary :
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential (objective seedC seedD) 0 := by
  intro h
  have hh := h downhill
  rw [objective_zero] at hh
  have he : objective seedC seedD downhill = -1 := by
    simpa only [one_smul] using objective_downhill_ray (t := 1) (by norm_num)
  rw [he] at hh
  norm_num [dot] at hh

theorem actual_run_failure {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    let R := run c₁ c₂ hc₁ hc₁' hc hc₂
    R.H 0=1 ∧ Tendsto R.x atTop (𝓝 0) ∧
      Tendsto (fun k => objective seedC seedD (R.x k)) atTop (𝓝 0) ∧
      (∀ k, 0 < objective seedC seedD (R.x k)) ∧
      (∀ k, objective seedC seedD (R.x (k+1)) < objective seedC seedD (R.x k)) ∧
      (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential (objective seedC seedD) 0 := by
  refine ⟨?_,orbitPoint_tendsto,orbit_value_tendsto,orbit_value_pos,?_,limit_not_stationary⟩
  · change (1:ℝ) • (1:Mat 2)=1
    rw [one_smul]
  · exact (run c₁ c₂ hc₁ hc₁' hc hc₂).objective_strict_decrease

end BfgsVerification.SeedOrbit
