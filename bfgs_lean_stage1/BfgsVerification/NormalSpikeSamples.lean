import BfgsVerification.NormalSpikeGradient

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike

def normal (n : ℕ) : Vec (n+2) := Pi.single 0 1
def sample (n : ℕ) (u v : ℝ) : Vec (n+2) := Pi.single 0 v + Pi.single 1 u

theorem normal_unit (n : ℕ) : sqNorm (normal n) = 1 := by
  simp [normal, sqNorm, Pi.single_apply]

theorem sample_normal (n : ℕ) (u v : ℝ) : dot (normal n) (sample n u v) = v := by
  have hne : (0 : Fin (n+2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [Fin.val_one, Nat.mod_eq_of_lt (show 1 < n+2 by omega)] at hv
  simp [dot, normal, sample, Pi.single_apply, hne]

theorem sample_sqNorm (n : ℕ) (u v : ℝ) : sqNorm (sample n u v) = u^2+v^2 := by
  have hne : (0 : Fin (n+2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [Fin.val_one, Nat.mod_eq_of_lt (show 1 < n+2 by omega)] at hv
  simp [sqNorm, sample, Pi.add_apply, add_sq, Finset.sum_add_distrib, Pi.single_apply,
    Finset.mul_sum, hne, add_comm]

theorem sample_objective (n : ℕ) (u v : ℝ) :
    objective (normal n) (sample n u v) = (1/2 : ℝ)*(u^2+v^2)+|v|+sourcePrimitive v := by
  rw [objective, quadratic, sample_normal, sample_sqNorm, normalPenalty]
  ring

theorem sample_objective_lower (n : ℕ) (u v : ℝ) :
    (1/2 : ℝ)*u^2 ≤ objective (normal n) (sample n u v) := by
  have hb := objective_lower_bound (normal n) (sample n u v)
  rw [sample_sqNorm] at hb
  nlinarith [sq_nonneg v]

theorem sample_objective_limit (n : ℕ) (u : ℝ) :
    Tendsto (fun N => objective (normal n) (sample n u (scale N))) atTop (𝓝 ((1/2 : ℝ)*u^2)) := by
  have hr := (sourcePrimitive_contDiff.continuous.tendsto (0 : ℝ)).comp scale_tendsto_zero
  have hz : sourcePrimitive 0 = 0 := by simp [sourcePrimitive]
  rw [hz] at hr
  simp_rw [sample_objective]
  convert ((((tendsto_const_nhds.add (scale_tendsto_zero.pow 2)).const_mul (1/2 : ℝ)).add
    scale_tendsto_zero.abs).add hr) using 1 <;> norm_num

theorem sample_radial_curvature_peak (n : ℕ) (u : ℝ) (N : ℕ) :
    sqNorm (sample n u (scale N)) + (dot (normal n) (sample n u (scale N)))^2 *
      density (dot (normal n) (sample n u (scale N))) = u^2+(scale N)^2+(scale N)⁻¹ := by
  rw [sample_sqNorm, sample_normal, density_peak]
  have hn := (scale_pos N).ne'
  field_simp
  ring

theorem sample_radial_curvature_unbounded (n : ℕ) (u : ℝ) :
    Tendsto (fun N => sqNorm (sample n u (scale N)) +
      (dot (normal n) (sample n u (scale N)))^2 * density (dot (normal n) (sample n u (scale N))))
      atTop atTop := by
  simp_rw [sample_radial_curvature_peak]
  have hi : Tendsto (fun N => (scale N)⁻¹) atTop atTop := by
    apply tendsto_inv_nhdsGT_zero.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨scale_tendsto_zero, Eventually.of_forall scale_pos⟩
  apply tendsto_atTop_mono (fun N => ?_) hi
  nlinarith [sq_nonneg u, sq_nonneg (scale N)]

theorem sample_positive_gradient (n : ℕ) (u : ℝ) (N : ℕ) :
    HasFDerivAt (objective (normal n))
      (gradientFunctional (positiveGradient (normal n) (sample n u (scale N)))) (sample n u (scale N)) := by
  apply objective_hasFDerivAt_pos
  rw [sample_normal]
  exact scale_pos N

end BfgsVerification.NormalSpike
