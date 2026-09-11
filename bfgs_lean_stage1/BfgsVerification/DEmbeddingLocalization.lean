import BfgsVerification.DEmbeddingOracle

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.DEmbedding
open SeedCycle SeedOrbit DScalarGeometric

theorem scale_tendsto : Tendsto scale atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one theta_pos.le theta_lt_one

theorem center_tendsto : Tendsto center atTop (𝓝 0) := by
  simpa only [zero_smul] using (scale_tendsto.smul_const (![2,-32] : Vec 2))

theorem initial_points_tendsto :
    Tendsto (fun n => SeedEmbedding.point (center n) ((scale n)^2) 0) atTop (𝓝 0) := by
  simpa only [zero_pow (by decide : 2≠0), zero_smul, add_zero] using
    (center_tendsto.add ((scale_tendsto.pow 2).smul_const (orbitPoint 0)))

theorem certificate_norm_bound {z : Vec 2} {i : Fin 3} (hz : PointCertificate seedC seedD z i) :
    ‖z‖ ≤ 48 := by
  have h0 := abs_lt.mp (hz.branch_bounds 0)
  have h1 := abs_lt.mp (hz.branch_bounds 1)
  norm_num [SeedOrbit.gradient, g0, g1, dot, Fin.sum_univ_two] at h0 h1
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 48)).mpr
  intro j
  fin_cases j
  · change |z 0| ≤ 48
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · change |z 1| ≤ 48
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem center_norm_bound (n : ℕ) : ‖center n‖ ≤ 32*scale n := by
  have hb : ‖(![2,-32] : Vec 2)‖ ≤ 32 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 32)).mpr
    intro j
    fin_cases j <;> norm_num
  rw [center, norm_smul, Real.norm_eq_abs, abs_of_pos (scale_pos n)]
  nlinarith [mul_le_mul_of_nonneg_left hb (scale_pos n).le]

theorem embedded_certificate_norm_bound (n : ℕ) {z : Vec 2} {i : Fin 3}
    (hz : PointCertificate seedC seedD z i) : ‖center n+(scale n)^2 • z‖ ≤ 80*scale n := by
  have he := norm_add_le (center n) ((scale n)^2 • z)
  have hz' := certificate_norm_bound hz
  have hs := scale_pos n
  have hu := scale_le_one n
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at he
  have hmul := mul_le_mul_of_nonneg_left hz' (sq_nonneg (scale n))
  have hsq := mul_le_mul_of_nonneg_left hu hs.le
  nlinarith [center_norm_bound n]

theorem accepted_norm_bound (n k : ℕ) :
    ‖SeedEmbedding.point (center n) ((scale n)^2) k‖ ≤ 80*scale n :=
  embedded_certificate_norm_bound n (orbit_certificate k)

theorem trial_norm_bound (n k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    ‖center n+(scale n)^2 • SeedEmbedding.trialPoint k q‖ ≤ 80*scale n :=
  embedded_certificate_norm_bound n (orbit_trial_point_certificate k q hq)

theorem trajectories_uniformly_small {V : Set (Vec 2)} (hV : V ∈ 𝓝 (0 : Vec 2)) :
    ∀ᶠ n in atTop, (∀ k, SeedEmbedding.point (center n) ((scale n)^2) k ∈ V) ∧
      ∀ k q, trialPhase q=phase k → center n+(scale n)^2 • SeedEmbedding.trialPoint k q ∈ V := by
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hlim : Tendsto (fun n => 80*scale n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using scale_tendsto.const_mul 80
  have hev : ∀ᶠ n in atTop, 80*scale n<eps := hlim.eventually (gt_mem_nhds heps)
  filter_upwards [hev] with n hn
  constructor
  · intro k
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    exact (accepted_norm_bound n k).trans_lt hn
  · intro k q hq
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    exact (trial_norm_bound n k q hq).trans_lt hn

end BfgsVerification.DEmbedding
