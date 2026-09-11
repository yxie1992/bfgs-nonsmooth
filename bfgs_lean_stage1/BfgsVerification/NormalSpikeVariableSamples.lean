import BfgsVerification.NormalSpikeVariableGradient
import BfgsVerification.NormalSpikeInterface

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.NormalSpike

theorem variable_sample_dot (n : ℕ) {c : Vec (n+2)} (hc : dot (normal n) c = 0) (u v : ℝ) :
    dot c (sample n u v) = c 1*u := by
  have hc0 : c 0 = 0 := by simpa only [normal_coordinate] using hc
  change c ⬝ᵥ (Pi.single 0 v+Pi.single 1 u) = _
  rw [dotProduct_add, dotProduct_single, dotProduct_single, hc0, zero_mul, zero_add]

theorem variable_sample_objective (n : ℕ) {c : Vec (n+2)} (hc : dot (normal n) c = 0) (u v : ℝ) :
    variableObjective (normal n) c (sample n u v) =
      (1/2 : ℝ)*(u^2+v^2)+|(1+c 1*u)*v|+sourcePrimitive v := by
  rw [variableObjective, quadratic, sample_sqNorm, sample_normal, variable_sample_dot n hc]

theorem variable_sample_objective_limit (n : ℕ) {c : Vec (n+2)} (hc : dot (normal n) c = 0) (u : ℝ) :
    Tendsto (fun N => variableObjective (normal n) c (sample n u (scale N))) atTop (𝓝 ((1/2 : ℝ)*u^2)) := by
  have hr := (sourcePrimitive_contDiff.continuous.tendsto (0 : ℝ)).comp scale_tendsto_zero
  have hz : sourcePrimitive 0 = 0 := by simp [sourcePrimitive]
  rw [hz] at hr
  simp_rw [variable_sample_objective n hc]
  convert ((((tendsto_const_nhds.add (scale_tendsto_zero.pow 2)).const_mul (1/2 : ℝ)).add
    (scale_tendsto_zero.const_mul (1+c 1*u)).abs).add hr) using 1 <;> norm_num

theorem variable_sample_radial_curvature_peak (n : ℕ) {c : Vec (n+2)}
    (hc : dot (normal n) c = 0) (u : ℝ) (N : ℕ) :
    sqNorm (sample n u (scale N))+2*dot c (sample n u (scale N))*dot (normal n) (sample n u (scale N)) +
      (dot (normal n) (sample n u (scale N)))^2*density (dot (normal n) (sample n u (scale N))) =
        u^2+(scale N)^2+2*(c 1*u)*scale N+(scale N)⁻¹ := by
  rw [sample_sqNorm, sample_normal, variable_sample_dot n hc, density_peak]
  have hn := (scale_pos N).ne'
  field_simp
  ring

theorem variable_sample_radial_curvature_unbounded (n : ℕ) {c : Vec (n+2)}
    (hc : dot (normal n) c = 0) (u : ℝ) (hu : 0 ≤ c 1*u) :
    Tendsto (fun N => sqNorm (sample n u (scale N))+2*dot c (sample n u (scale N))*dot (normal n) (sample n u (scale N)) +
      (dot (normal n) (sample n u (scale N)))^2*density (dot (normal n) (sample n u (scale N))))
      atTop atTop := by
  simp_rw [variable_sample_radial_curvature_peak n hc]
  have hi : Tendsto (fun N => (scale N)⁻¹) atTop atTop := by
    apply tendsto_inv_nhdsGT_zero.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨scale_tendsto_zero, Eventually.of_forall scale_pos⟩
  apply tendsto_atTop_mono (fun N => ?_) hi
  nlinarith [sq_nonneg u, sq_nonneg (scale N), mul_nonneg hu (scale_pos N).le]

end BfgsVerification.NormalSpike
