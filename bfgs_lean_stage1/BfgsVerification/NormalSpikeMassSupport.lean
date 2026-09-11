import BfgsVerification.NormalSpikeOracle

noncomputable section
open scoped Topology
open Set Filter MeasureTheory
namespace BfgsVerification.NormalSpike

theorem scaledDensity_support_subset (a : ℝ) (ha : 0 < a) :
    Function.support (scaledDensity a) ⊆ Icc (a-a^5) (a+a^5) := by
  intro v hv
  constructor
  · by_contra h
    exact hv (scaledDensity_below ha (le_of_not_ge h))
  · by_contra h
    exact hv (scaledDensity_above ha (lt_of_not_ge h))

theorem scaledDensity_support_positive (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    Function.support (scaledDensity a) ⊆ Ioc 0 (3*a) := by
  intro v hv
  constructor
  · by_contra h
    have ht := normalized_nonpos ha ha1 (le_of_not_gt h)
    exact hv (by simp only [scaledDensity, bump, if_pos ht, mul_zero])
  · have hb := (scaledDensity_support_subset a ha hv).2
    have hp : a^5 ≤ a := by
      calc
        a^5 = a^4*a := by ring
        _ ≤ 1*a := mul_le_mul_of_nonneg_right (pow_le_one₀ ha.le ha1) ha.le
        _ = a := one_mul _
    linarith

theorem scaledDensity_integrable (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    Integrable (scaledDensity a) := by
  apply (integrableOn_iff_integrable_of_support_subset (scaledDensity_support_positive a ha ha1)).mp
  exact ((scaledDensity_continuous a).intervalIntegrable 0 (3*a)).1

theorem scaledDensity_total_mass (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ v : ℝ, scaledDensity a v) = (16/15)*a^2 := by
  rw [← intervalIntegral.integral_eq_integral_of_support_subset (scaledDensity_support_positive a ha ha1),
    scaledMass_integral ha ha1]
  apply scaledMass_above ha
  have hp : a^5 ≤ a := by
    calc
      a^5 = a^4*a := by ring
      _ ≤ 1*a := mul_le_mul_of_nonneg_right (pow_le_one₀ ha.le ha1) ha.le
      _ = a := one_mul _
  linarith

theorem density_total_mass : (∫ v : ℝ, density v) = 4/45 := by
  have hn (j : ℕ) : (∫ v : ℝ, ‖scaledDensity (scale j) v‖) = (16/15)*(scale j)^2 := by
    calc
      _ = ∫ v : ℝ, scaledDensity (scale j) v := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun v => Real.norm_of_nonneg (scaledDensity_nonneg (scale_pos j).le v))
      _ = _ := scaledDensity_total_mass _ (scale_pos j) (scale_le_one j)
  have hs : Summable (fun j : ℕ => ∫ v : ℝ, ‖scaledDensity (scale j) v‖) := by
    simp_rw [hn]
    exact summable_mass_bound
  have he := integral_tsum_of_summable_integral_norm
    (fun j => scaledDensity_integrable _ (scale_pos j) (scale_le_one j)) hs
  change (∫ v : ℝ, ∑' j : ℕ, scaledDensity (scale j) v) = 4/45
  rw [← he]
  simp_rw [scaledDensity_total_mass _ (scale_pos _) (scale_le_one _)]
  rw [tsum_mul_left, scale_power_tsum (by omega : 0 < 2)]
  norm_num

theorem density_integrable : Integrable density :=
  Integrable.of_integral_ne_zero (by rw [density_total_mass]; norm_num)

theorem bump_supports_pairwise_disjoint :
    Pairwise (fun j N : ℕ => Disjoint (Function.support (scaledDensity (scale j)))
      (Function.support (scaledDensity (scale N)))) := by
  intro j N hjN
  apply Set.disjoint_left.mpr
  intro v hj hN
  obtain ⟨hjlo, hjhi⟩ := scaledDensity_support_subset _ (scale_pos j) hj
  obtain ⟨hNlo, hNhi⟩ := scaledDensity_support_subset _ (scale_pos N) hN
  rcases lt_or_gt_of_ne hjN with hlt | hgt
  · have ht := later_bump_above_query hlt hjlo
    exact (not_lt_of_ge hNhi) ht
  · have ht := later_bump_above_query hgt hNlo
    exact (not_lt_of_ge hjhi) ht

theorem at_most_one_partial_bump (v : ℝ) :
    Set.Subsingleton {j : ℕ | v ∈ Function.support (scaledDensity (scale j))} := by
  intro j hj N hN
  by_contra hne
  exact Set.disjoint_left.mp (bump_supports_pairwise_disjoint hne) hj hN

end BfgsVerification.NormalSpike
