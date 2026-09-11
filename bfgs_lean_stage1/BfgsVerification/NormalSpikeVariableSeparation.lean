import BfgsVerification.NormalSpikeVariableRadialBound
import BfgsVerification.NormalSpikeVariableSamples

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike
open RadialCertificate FixedNormal

theorem variable_not_radial_secant_sublevel_of_signed_height (n : ℕ) {c : Vec (n+2)}
    (hc : dot (normal n) c = 0) (hcnorm : Real.sqrt (sqNorm c) < 1)
    (u : ℝ) (hu : u ≠ 0) (huSign : 0 ≤ c 1*u)
    {b : ℝ} (hb : (1/2 : ℝ)*u^2 < b) :
    ¬ HasRadialSecantBounds (variableObjective (normal n) c) {x | variableObjective (normal n) c x ≤ b} 0 := by
  have hF := variableObjective_convex (normal_unit n) hc (Real.sqrt_nonneg (sqNorm c))
    (Real.sq_sqrt (sqNorm_nonneg c)) hcnorm.le
  intro hRS
  let η := u^2/8
  have hη : 0 < η := by dsimp [η]; exact div_pos (sq_pos_of_ne_zero hu) (by norm_num)
  obtain ⟨C, hC⟩ := hRS η hη
  have hxK : ∀ᶠ N in atTop, variableObjective (normal n) c (sample n u (scale N)) ≤ b :=
    ((variable_sample_objective_limit n hc u).eventually (gt_mem_nhds hb)).mono (fun _ h => h.le)
  have hbound : ∀ᶠ N in atTop, sqNorm (sample n u (scale N))+2*dot c (sample n u (scale N))*dot (normal n) (sample n u (scale N)) +
      (dot (normal n) (sample n u (scale N)))^2 * density (dot (normal n) (sample n u (scale N))) ≤ 4*C := by
    filter_upwards [hxK] with N hN
    let x := sample n u (scale N)
    have hv : 0 < dot (normal n) x := by dsimp [x]; rw [sample_normal]; exact scale_pos N
    apply variable_radial_curvature_le_of_pair_bound (normal_unit n) hc hcnorm x hv (by norm_num : (0 : ℝ) < 1/2) le_rfl
    intro t ht hthalf
    let z := (1-t) • x
    have htone : t ≤ 1 := by linarith
    have hin : inwardPoint 0 x t = z := by dsimp [inwardPoint, z]; module
    have horder : variableObjective (normal n) c z ≤ variableObjective (normal n) c x := by
      have hp := hF.2 (mem_univ x) (mem_univ 0)
        (show 0 ≤ 1-t by linarith) ht.le (by ring : (1-t)+t=1)
      simp only [smul_zero, add_zero, variableObjective_zero, smul_eq_mul, mul_zero, add_zero] at hp
      have hn := variableObjective_minimum (normal n) c x
      rw [variableObjective_zero] at hn
      exact hp.trans (by nlinarith)
    have hzK : variableObjective (normal n) c z ≤ b := horder.trans hN
    have hzband : variableObjective (normal n) c 0 + η ≤ variableObjective (normal n) c z := by
      rw [variableObjective_zero, zero_add]
      have hlower := variableObjective_lower_bound (normal n) c z
      have hsq : sqNorm z = (1-t)^2*(u^2+(scale N)^2) := by
        change sqNorm ((1-t) • sample n u (scale N)) = _
        rw [CertificateGeometry.sqNorm_smul, sample_sqNorm]
      rw [hsq] at hlower
      have hfac : (1/4 : ℝ) ≤ (1-t)^2 := by nlinarith
      have hnon := mul_nonneg (sq_nonneg (1-t)) (sq_nonneg (scale N))
      have hmul := mul_le_mul_of_nonneg_right hfac (sq_nonneg u)
      dsimp only [η]
      nlinarith [hlower]
    have hzpos : 0 < dot (normal n) z := by
      change 0 < dot (normal n) ((1-t) • x)
      rw [dot_smul_right]
      exact mul_pos (by linarith) hv
    have hwx : 0 < 1+dot c x := by
      dsimp [x]
      rw [variable_sample_dot n hc]
      linarith
    have hwz : 0 < 1+dot c z := by
      change 0 < 1+dot c ((1-t) • sample n u (scale N))
      rw [dot_smul_right, variable_sample_dot n hc]
      have hp := mul_nonneg (show 0 ≤ 1-t by linarith) huSign
      linarith
    have hg := variableObjective_hasFDerivAt_pos (normal n) c x hwx hv
    have hh := variableObjective_hasFDerivAt_pos (normal n) c z hwz hzpos
    apply hC x z (variablePositiveGradient (normal n) c x) (variablePositiveGradient (normal n) c z)
      hN hzK hzband horder hg hh
    rw [(variable_radial_contraction_identities (normal n) c x t).1]
    exact mul_pos ht (variable_radial_difference_positive (normal_unit n) hc hcnorm x hv ht)
  have hunbounded := (variable_sample_radial_curvature_unbounded n hc u huSign).eventually (eventually_gt_atTop (4*C))
  obtain ⟨N, hN, hN'⟩ := (hbound.and hunbounded).exists
  exact (not_lt_of_ge hN) hN'

theorem variable_not_radial_secant_sublevel (n : ℕ) {c : Vec (n+2)}
    (hc : dot (normal n) c = 0) (hcnorm : Real.sqrt (sqNorm c) < 1) {b : ℝ} (hb : 0 < b) :
    ¬ HasRadialSecantBounds (variableObjective (normal n) c) {x | variableObjective (normal n) c x ≤ b} 0 := by
  by_cases hs : 0 ≤ c 1
  · apply variable_not_radial_secant_sublevel_of_signed_height n hc hcnorm (Real.sqrt b)
      (Real.sqrt_pos.mpr hb).ne' (mul_nonneg hs (Real.sqrt_nonneg b))
    rw [Real.sq_sqrt hb.le]
    nlinarith
  · apply variable_not_radial_secant_sublevel_of_signed_height n hc hcnorm (-Real.sqrt b)
      (neg_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne')
      (mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hs) (neg_nonpos.mpr (Real.sqrt_nonneg b)))
    rw [neg_sq, Real.sq_sqrt hb.le]
    nlinarith

theorem variable_not_radial_secant_neighborhood (n : ℕ) {c : Vec (n+2)}
    (hc : dot (normal n) c = 0) (hcnorm : Real.sqrt (sqNorm c) < 1) {K : Set (Vec (n+2))}
    (hK : K ∈ 𝓝 0) : ¬ HasRadialSecantBounds (variableObjective (normal n) c) K 0 := by
  have hF := variableObjective_convex (normal_unit n) hc (Real.sqrt_nonneg (sqNorm c))
    (Real.sq_sqrt (sqNorm_nonneg c)) hcnorm.le
  intro hRS
  obtain ⟨ε, hε, hsub⟩ := Localization.neighborhood_basin hF 0
    (variableObjective_minimum (normal n) c) (variableObjective_unique_minimum (normal n) c) hK
  have hsub' : {x | variableObjective (normal n) c x ≤ ε} ⊆ K := by
    simpa only [variableObjective_zero, zero_add] using hsub
  apply variable_not_radial_secant_sublevel n hc hcnorm hε
  intro η hη
  obtain ⟨C, hC⟩ := hRS η hη
  refine ⟨C, ?_⟩
  intro x z g h hx hz hzband horder hg hh ht
  exact hC x z g h (hsub' hx) (hsub' hz) hzband horder hg hh ht


end BfgsVerification.NormalSpike
