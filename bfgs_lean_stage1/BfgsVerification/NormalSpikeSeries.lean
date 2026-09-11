import BfgsVerification.NormalSpikeScaled

/-! The actual infinite series in U.18, indexed by `j + 2`. -/
noncomputable section
open scoped Topology
open Set Filter MeasureTheory
namespace BfgsVerification.NormalSpike

def scale (j : ℕ) : ℝ := (1/2 : ℝ)^(j+2)
def density (v : ℝ) : ℝ := ∑' j : ℕ, scaledDensity (scale j) v
def seriesPrimitive (v : ℝ) : ℝ := ∑' j : ℕ, scaledPrimitive (scale j) v
def seriesMass (v : ℝ) : ℝ := ∑' j : ℕ, scaledMass (scale j) v
def sourcePrimitive (v : ℝ) : ℝ :=
  if 0 < v then ∫ t in (0 : ℝ)..v, (v-t) * density t else 0

theorem scale_pos (j : ℕ) : 0 < scale j := by unfold scale; positivity

theorem scale_le_quarter (j : ℕ) : scale j ≤ 1/4 := by
  calc
    scale j = (1/2 : ℝ)^j * (1/4) := by unfold scale; rw [pow_add]; norm_num
    _ ≤ 1 * (1/4) := mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)
    _ = _ := by ring

theorem scale_le_one (j : ℕ) : scale j ≤ 1 := (scale_le_quarter j).trans (by norm_num)

theorem scale_power_geometric (j p : ℕ) :
    (scale j)^p = ((1/2 : ℝ)^p)^j * (1/4 : ℝ)^p := by
  unfold scale
  rw [pow_add, mul_pow, ← pow_mul, Nat.mul_comm j p, pow_mul]
  norm_num

theorem summable_scale_power {p : ℕ} (hp : 0 < p) : Summable (fun j => (scale j)^p) := by
  simp_rw [scale_power_geometric]
  apply Summable.mul_right
  apply summable_geometric_of_abs_lt_one
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1/2 : ℝ)^p)]
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

theorem scale_power_tsum {p : ℕ} (hp : 0 < p) :
    (∑' j : ℕ, (scale j)^p) = (1/4 : ℝ)^p / (1-(1/2 : ℝ)^p) := by
  simp_rw [scale_power_geometric]
  rw [tsum_mul_right, tsum_geometric_of_abs_lt_one]
  · ring
  · rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1/2 : ℝ)^p)]
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

theorem summable_mass_bound : Summable (fun j => (16/15 : ℝ)*(scale j)^2) :=
  (summable_scale_power (by omega : 0 < 2)).mul_left _

theorem summable_scaledMass (v : ℝ) : Summable (fun j => scaledMass (scale j) v) := by
  apply Summable.of_norm_bounded _ summable_mass_bound
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (scaledMass_bounds _ _).1]
  exact (scaledMass_bounds _ _).2

theorem summable_scaledPrimitive (v : ℝ) : Summable (fun j => scaledPrimitive (scale j) v) :=
  Summable.of_norm_bounded _ (summable_mass_bound.mul_right ‖v‖)
    (fun j => scaledPrimitive_bound (scale_pos j) (scale_le_one j) v)

theorem seriesPrimitive_hasDerivAt (v : ℝ) :
    HasDerivAt seriesPrimitive (seriesMass v) v := by
  apply hasDerivAt_tsum summable_mass_bound
    (fun j y => scaledPrimitive_hasDerivAt (scale_pos j).ne' y)
    (fun j y => ?_) (summable_scaledPrimitive 0) v
  rw [Real.norm_eq_abs, abs_of_nonneg (scaledMass_bounds _ _).1]
  exact (scaledMass_bounds _ _).2

theorem seriesMass_continuous : Continuous seriesMass := by
  apply continuous_tsum (fun j => continuous_iff_continuousAt.mpr
    (fun v => (scaledMass_hasDerivAt (scale_pos j).ne' v).continuousAt)) summable_mass_bound
  intro j v
  rw [Real.norm_eq_abs, abs_of_nonneg (scaledMass_bounds _ _).1]
  exact (scaledMass_bounds _ _).2

theorem seriesPrimitive_contDiff : ContDiff ℝ 1 seriesPrimitive := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun v => (seriesPrimitive_hasDerivAt v).differentiableAt, ?_⟩
  have he : deriv seriesPrimitive = seriesMass := funext fun v => (seriesPrimitive_hasDerivAt v).deriv
  rw [he]
  exact seriesMass_continuous

theorem seriesMass_monotone : Monotone seriesMass := by
  intro u v huv
  exact tsum_le_tsum (fun j => scaledMass_monotone (scale_pos j) huv)
    (summable_scaledMass u) (summable_scaledMass v)

theorem seriesPrimitive_convex : ConvexOn ℝ univ seriesPrimitive := by
  apply Monotone.convexOn_univ_of_deriv (fun v => (seriesPrimitive_hasDerivAt v).differentiableAt)
  convert seriesMass_monotone using 1
  exact funext fun v => (seriesPrimitive_hasDerivAt v).deriv

theorem seriesPrimitive_nonneg (v : ℝ) : 0 ≤ seriesPrimitive v :=
  tsum_nonneg (fun j => scaledPrimitive_nonneg (scale_pos j).le v)

theorem seriesMass_nonneg (v : ℝ) : 0 ≤ seriesMass v :=
  tsum_nonneg (fun j => (scaledMass_bounds (scale j) v).1)

theorem seriesPrimitive_nonpos {v : ℝ} (hv : v ≤ 0) : seriesPrimitive v = 0 := by
  unfold seriesPrimitive
  simp only [scaledPrimitive_nonpos (scale_pos _) (scale_le_one _) hv, tsum_zero]

theorem seriesMass_nonpos {v : ℝ} (hv : v ≤ 0) : seriesMass v = 0 := by
  unfold seriesMass
  simp only [scaledMass_nonpos (scale_pos _) (scale_le_one _) hv, tsum_zero]

theorem seriesPrimitive_eq_source (v : ℝ) : seriesPrimitive v = sourcePrimitive v := by
  by_cases hv : 0 < v
  · simp only [sourcePrimitive, if_pos hv]
    have hint (j : ℕ) : IntegrableOn (fun t => (v-t)*scaledDensity (scale j) t) (Ioc 0 v) :=
      (((continuous_const.sub continuous_id).mul (scaledDensity_continuous (scale j))).intervalIntegrable 0 v).1
    have hnorm (j : ℕ) :
        (∫ t in Ioc 0 v, ‖(v-t)*scaledDensity (scale j) t‖) = scaledPrimitive (scale j) v := by
      rw [← scaledPrimitive_kernel_integral (scale_pos j) (scale_le_one j) v,
        intervalIntegral.integral_of_le hv.le]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (sub_nonneg.mpr ht.2) (scaledDensity_nonneg (scale_pos j).le t))]
    have hsum : Summable (fun j : ℕ => ∫ t in Ioc 0 v, ‖(v-t)*scaledDensity (scale j) t‖) := by
      simp_rw [hnorm]
      exact summable_scaledPrimitive v
    have he := integral_tsum_of_summable_integral_norm hint hsum
    rw [intervalIntegral.integral_of_le hv.le]
    calc
      seriesPrimitive v = ∑' j : ℕ, ∫ t in Ioc 0 v, (v-t)*scaledDensity (scale j) t := by
        apply tsum_congr
        intro j
        rw [← intervalIntegral.integral_of_le hv.le,
          scaledPrimitive_kernel_integral (scale_pos j) (scale_le_one j) v]
      _ = ∫ t in Ioc 0 v, ∑' j : ℕ, (v-t)*scaledDensity (scale j) t := he
      _ = ∫ t in Ioc 0 v, (v-t)*density t := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t _
        exact tsum_mul_left
  · simp only [sourcePrimitive, if_neg hv, seriesPrimitive_nonpos (le_of_not_gt hv)]

end BfgsVerification.NormalSpike
