import BfgsVerification.NormalSpikeGeometry

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike

def tailMass (N : ℕ) : ℝ := ∑' j : ℕ, (16/15 : ℝ)*(scale (j+N))^2
def tailMoment (N : ℕ) : ℝ := ∑' j : ℕ, (16/15 : ℝ)*(scale (j+N))^3

theorem tailMass_eq (N : ℕ) : tailMass N = (64/45 : ℝ)*(scale N)^2 := by
  unfold tailMass
  rw [tsum_mul_left, scale_tail_power_tsum (by omega : 0 < 2)]
  norm_num
  ring

theorem tailMoment_eq (N : ℕ) : tailMoment N = (128/105 : ℝ)*(scale N)^3 := by
  unfold tailMoment
  rw [tsum_mul_left, scale_tail_power_tsum (by omega : 0 < 3)]
  norm_num
  ring

theorem cumulativeMass_contDiff : ContDiff ℝ 2 cumulativeMass := by
  rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num]
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun t => (cumulativeMass_hasDerivAt t).differentiableAt, ?_, ?_⟩
  · norm_num
  · have he : deriv cumulativeMass = bump := funext fun t => (cumulativeMass_hasDerivAt t).deriv
    rw [he]
    exact bump_contDiff

theorem primitive_contDiff : ContDiff ℝ 3 primitive := by
  rw [show (3 : WithTop ℕ∞) = 2+1 by norm_num]
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun t => (primitive_hasDerivAt t).differentiableAt, ?_, ?_⟩
  · norm_num
  · have he : deriv primitive = cumulativeMass := funext fun t => (primitive_hasDerivAt t).deriv
    rw [he]
    exact cumulativeMass_contDiff

theorem scaledPrimitive_contDiff (a : ℝ) : ContDiff ℝ 3 (scaledPrimitive a) :=
  contDiff_const.mul (primitive_contDiff.comp ((contDiff_id.sub contDiff_const).div_const _))

theorem scaledMass_contDiff (a : ℝ) : ContDiff ℝ 2 (scaledMass a) :=
  contDiff_const.mul (cumulativeMass_contDiff.comp ((contDiff_id.sub contDiff_const).div_const _))

theorem scaledDensity_contDiff (a : ℝ) : ContDiff ℝ 1 (scaledDensity a) :=
  contDiff_const.mul (bump_contDiff.comp ((contDiff_id.sub contDiff_const).div_const _))

theorem seriesPrimitive_tail_formula (N : ℕ) (v : ℝ)
    (hN : ∀ j, N ≤ j → scale j + (scale j)^5 < v) :
    seriesPrimitive v = (∑ j ∈ Finset.range N, scaledPrimitive (scale j) v) +
      tailMass N * v - tailMoment N := by
  have hm := (summable_tail_scale_power (by omega : 0 < 2) N).mul_left (16/15 : ℝ)
  have ht := (summable_tail_scale_power (by omega : 0 < 3) N).mul_left (16/15 : ℝ)
  calc
    seriesPrimitive v = (∑ j ∈ Finset.range N, scaledPrimitive (scale j) v) +
        ∑' j : ℕ, scaledPrimitive (scale (j+N)) v :=
      ((summable_scaledPrimitive v).sum_add_tsum_nat_add N).symm
    _ = (∑ j ∈ Finset.range N, scaledPrimitive (scale j) v) +
        ∑' j : ℕ, (((16/15 : ℝ)*(scale (j+N))^2)*v - (16/15)*(scale (j+N))^3) := by
      congr 1
      apply tsum_congr
      intro j
      exact scaledPrimitive_above (scale_pos _) (hN _ (by omega))
    _ = _ := by
      rw [tsum_sub (hm.mul_right v) ht, tsum_mul_right]
      unfold tailMass tailMoment
      ring

theorem seriesMass_tail_formula (N : ℕ) (v : ℝ)
    (hN : ∀ j, N ≤ j → scale j + (scale j)^5 < v) :
    seriesMass v = (∑ j ∈ Finset.range N, scaledMass (scale j) v) + tailMass N := by
  rw [seriesMass, ← (summable_scaledMass v).sum_add_tsum_nat_add N]
  congr 1
  apply tsum_congr
  intro j
  exact scaledMass_above (scale_pos _) (hN _ (by omega))

theorem density_tail_formula (N : ℕ) (v : ℝ)
    (hN : ∀ j, N ≤ j → scale j + (scale j)^5 < v) :
    density v = ∑ j ∈ Finset.range N, scaledDensity (scale j) v := by
  apply tsum_eq_sum
  intro j hj
  exact scaledDensity_above (scale_pos _) (hN j (by simpa only [Finset.mem_range, not_lt] using hj))

theorem seriesPrimitive_contDiffAt_pos {v : ℝ} (hv : 0 < v) :
    ContDiffAt ℝ 3 seriesPrimitive v := by
  obtain ⟨N, hN⟩ := exists_tail_below_neighborhood hv
  have hd : ContDiff ℝ 3 (fun u => (∑ j ∈ Finset.range N, scaledPrimitive (scale j) u) +
      tailMass N * u - tailMoment N) :=
    ((ContDiff.sum (fun j _ => scaledPrimitive_contDiff (scale j))).add
      (contDiff_const.mul contDiff_id)).sub contDiff_const
  apply hd.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hN] with u hu
  exact seriesPrimitive_tail_formula N u hu

theorem seriesPrimitive_contDiffAt_neg {v : ℝ} (hv : v < 0) :
    ContDiffAt ℝ 3 seriesPrimitive v := by
  apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hv] with u hu
  exact seriesPrimitive_nonpos hu.le

theorem seriesPrimitive_contDiffOn_off_zero : ContDiffOn ℝ 3 seriesPrimitive ({0}ᶜ : Set ℝ) := by
  intro v hv
  have hne : v ≠ 0 := hv
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact (seriesPrimitive_contDiffAt_neg hneg).contDiffWithinAt
  · exact (seriesPrimitive_contDiffAt_pos hpos).contDiffWithinAt

theorem seriesMass_hasDerivAt_pos {v : ℝ} (hv : 0 < v) :
    HasDerivAt seriesMass (density v) v := by
  obtain ⟨N, hN⟩ := exists_tail_below_neighborhood hv
  have hd := (HasDerivAt.sum (u := Finset.range N)
    (fun j _ => scaledMass_hasDerivAt (scale_pos j).ne' v)).add_const (tailMass N)
  rw [← density_tail_formula N v hN.self_of_nhds] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hN] with u hu
  exact seriesMass_tail_formula N u hu

theorem density_contDiffAt_pos {v : ℝ} (hv : 0 < v) : ContDiffAt ℝ 1 density v := by
  obtain ⟨N, hN⟩ := exists_tail_below_neighborhood hv
  have hd := ContDiff.sum (s := Finset.range N) (fun j _ => scaledDensity_contDiff (scale j))
  apply hd.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hN] with u hu
  exact density_tail_formula N u hu

theorem sourcePrimitive_contDiff : ContDiff ℝ 1 sourcePrimitive := by
  have he : sourcePrimitive = seriesPrimitive := funext fun t => (seriesPrimitive_eq_source t).symm
  rw [he]
  exact seriesPrimitive_contDiff

theorem sourcePrimitive_convex : ConvexOn ℝ univ sourcePrimitive := by
  have he : sourcePrimitive = seriesPrimitive := funext fun t => (seriesPrimitive_eq_source t).symm
  rw [he]
  exact seriesPrimitive_convex

theorem sourcePrimitive_contDiffOn_off_zero : ContDiffOn ℝ 3 sourcePrimitive ({0}ᶜ : Set ℝ) := by
  have he : sourcePrimitive = seriesPrimitive := funext fun t => (seriesPrimitive_eq_source t).symm
  rw [he]
  exact seriesPrimitive_contDiffOn_off_zero

end BfgsVerification.NormalSpike
