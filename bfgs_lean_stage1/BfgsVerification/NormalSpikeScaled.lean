import BfgsVerification.NormalSpikeBump

/-! Actual rescaled bumps and exact integrated contributions to Module U.18. -/
noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike

def scaledPrimitive (a v : ℝ) : ℝ := a^7 * primitive ((v-a)/a^5)
def scaledMass (a v : ℝ) : ℝ := a^2 * cumulativeMass ((v-a)/a^5)
def scaledDensity (a v : ℝ) : ℝ := (a^3)⁻¹ * bump ((v-a)/a^5)
def scaledMoment (a v : ℝ) : ℝ := v * scaledMass a v - scaledPrimitive a v

theorem scaledPrimitive_hasDerivAt {a : ℝ} (ha : a ≠ 0) (v : ℝ) :
    HasDerivAt (scaledPrimitive a) (scaledMass a v) v := by
  have h := ((primitive_hasDerivAt ((v-a)/a^5)).comp v
    (((hasDerivAt_id v).sub_const a).div_const (a^5))).const_mul (a^7)
  convert h using 1
  dsimp [scaledMass]
  field_simp
  ring

theorem scaledMass_hasDerivAt {a : ℝ} (ha : a ≠ 0) (v : ℝ) :
    HasDerivAt (scaledMass a) (scaledDensity a v) v := by
  have h := ((cumulativeMass_hasDerivAt ((v-a)/a^5)).comp v
    (((hasDerivAt_id v).sub_const a).div_const (a^5))).const_mul (a^2)
  convert h using 1
  dsimp [scaledDensity]
  field_simp
  ring

theorem scaledMoment_hasDerivAt {a : ℝ} (ha : a ≠ 0) (v : ℝ) :
    HasDerivAt (scaledMoment a) (v * scaledDensity a v) v := by
  convert ((hasDerivAt_id v).mul (scaledMass_hasDerivAt ha v)).sub
    (scaledPrimitive_hasDerivAt ha v) using 1 <;> try rfl
  simp only [id_eq]
  ring

theorem scaledPrimitive_nonneg {a : ℝ} (ha : 0 ≤ a) (v : ℝ) :
    0 ≤ scaledPrimitive a v := mul_nonneg (pow_nonneg ha _) (primitive_nonneg _)

theorem scaledMass_bounds (a v : ℝ) :
    0 ≤ scaledMass a v ∧ scaledMass a v ≤ (16/15)*a^2 := by
  obtain ⟨hl, hu⟩ := cumulativeMass_bounds ((v-a)/a^5)
  constructor
  · exact mul_nonneg (sq_nonneg a) hl
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hu (sq_nonneg a)

theorem scaledDensity_nonneg {a : ℝ} (ha : 0 ≤ a) (v : ℝ) :
    0 ≤ scaledDensity a v := mul_nonneg (inv_nonneg.mpr (pow_nonneg ha _)) (bump_nonneg _)

theorem normalized_nonpos {a v : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hv : v ≤ 0) :
    (v-a)/a^5 ≤ -1 := by
  have hp : a^5 ≤ a := by
    calc
      a^5 = a^4*a := by ring
      _ ≤ 1*a := mul_le_mul_of_nonneg_right (pow_le_one₀ ha.le ha1) ha.le
      _ = a := one_mul a
  apply (div_le_iff₀ (pow_pos ha 5)).mpr
  linarith

theorem scaledPrimitive_nonpos {a v : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hv : v ≤ 0) :
    scaledPrimitive a v = 0 := by
  simp only [scaledPrimitive, primitive, if_pos (normalized_nonpos ha ha1 hv), mul_zero]

theorem scaledMass_nonpos {a v : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hv : v ≤ 0) :
    scaledMass a v = 0 := by
  simp only [scaledMass, cumulativeMass, if_pos (normalized_nonpos ha ha1 hv), mul_zero]

theorem scaledPrimitive_lipschitz {a : ℝ} (ha : a ≠ 0) :
    LipschitzWith (⟨(16/15)*a^2, by positivity⟩ : NNReal) (scaledPrimitive a) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun v => (scaledPrimitive_hasDerivAt ha v).differentiableAt)
  intro v
  rw [(scaledPrimitive_hasDerivAt ha v).deriv]
  exact_mod_cast (show |scaledMass a v| ≤ (16/15)*a^2 by
    rw [abs_of_nonneg (scaledMass_bounds a v).1]
    exact (scaledMass_bounds a v).2)

theorem scaledPrimitive_bound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (v : ℝ) :
    ‖scaledPrimitive a v‖ ≤ ((16/15)*a^2)*‖v‖ := by
  have hb := (scaledPrimitive_lipschitz ha.ne').dist_le_mul v 0
  simpa only [Real.dist_eq, scaledPrimitive_nonpos ha ha1 le_rfl, sub_zero,
    Real.norm_eq_abs] using hb

theorem scaledMass_monotone {a : ℝ} (ha : 0 < a) : Monotone (scaledMass a) :=
  monotone_of_hasDerivAt_nonneg (scaledMass_hasDerivAt ha.ne') (scaledDensity_nonneg ha.le)

theorem scaledPrimitive_convex {a : ℝ} (ha : 0 < a) : ConvexOn ℝ univ (scaledPrimitive a) := by
  apply Monotone.convexOn_univ_of_deriv (fun v => (scaledPrimitive_hasDerivAt ha.ne' v).differentiableAt)
  convert scaledMass_monotone ha using 1
  exact funext fun v => (scaledPrimitive_hasDerivAt ha.ne' v).deriv

theorem scaledDensity_continuous (a : ℝ) : Continuous (scaledDensity a) :=
  continuous_const.mul (bump_contDiff.continuous.comp ((continuous_id.sub continuous_const).div_const _))

theorem scaledMass_integral {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (v : ℝ) :
    (∫ t in (0 : ℝ)..v, scaledDensity a t) = scaledMass a v := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => scaledMass_hasDerivAt ha.ne' t) ((scaledDensity_continuous a).intervalIntegrable 0 v)
  simpa only [scaledMass_nonpos ha ha1 le_rfl, sub_zero] using he

theorem scaledMoment_integral {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (v : ℝ) :
    (∫ t in (0 : ℝ)..v, t * scaledDensity a t) = scaledMoment a v := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => scaledMoment_hasDerivAt ha.ne' t)
    ((continuous_id.mul (scaledDensity_continuous a)).intervalIntegrable 0 v)
  simpa only [scaledMoment, zero_mul, scaledPrimitive_nonpos ha ha1 le_rfl, sub_zero,
    sub_self] using he

theorem scaledPrimitive_kernel_integral {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (v : ℝ) :
    (∫ t in (0 : ℝ)..v, (v-t) * scaledDensity a t) = scaledPrimitive a v := by
  have hd (t : ℝ) : HasDerivAt (fun t => v * scaledMass a t - scaledMoment a t)
      ((v-t)*scaledDensity a t) t := by
    convert ((scaledMass_hasDerivAt ha.ne' t).const_mul v).sub
      (scaledMoment_hasDerivAt ha.ne' t) using 1 <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (((continuous_const.sub continuous_id).mul (scaledDensity_continuous a)).intervalIntegrable 0 v)
  simpa only [scaledMoment, scaledMass_nonpos ha ha1 le_rfl,
    scaledPrimitive_nonpos ha ha1 le_rfl, mul_zero, zero_mul, sub_zero, sub_self, sub_sub_cancel] using he

end BfgsVerification.NormalSpike
