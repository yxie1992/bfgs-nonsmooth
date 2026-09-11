import BfgsVerification.NormalSpikeRadialBound
import BfgsVerification.NormalSpikeSamples

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike
open RadialCertificate FixedNormal

theorem not_radial_secant_sublevel_of_tangent_height (n : ℕ) (u : ℝ) (hu : 0 < u)
    {b : ℝ} (hb : (1/2 : ℝ)*u^2 < b) :
    ¬ HasRadialSecantBounds (objective (normal n)) {x | objective (normal n) x ≤ b} 0 := by
  intro hRS
  let η := u^2/8
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨C, hC⟩ := hRS η hη
  have hxK : ∀ᶠ N in atTop, objective (normal n) (sample n u (scale N)) ≤ b :=
    ((sample_objective_limit n u).eventually (gt_mem_nhds hb)).mono (fun _ h => h.le)
  have hbound : ∀ᶠ N in atTop, sqNorm (sample n u (scale N)) +
      (dot (normal n) (sample n u (scale N)))^2 * density (dot (normal n) (sample n u (scale N))) ≤ 4*C := by
    filter_upwards [hxK] with N hN
    let x := sample n u (scale N)
    have hv : 0 < dot (normal n) x := by dsimp [x]; rw [sample_normal]; exact scale_pos N
    apply radial_curvature_le_of_pair_bound (normal n) x hv (by norm_num : (0 : ℝ) < 1/2) le_rfl
    intro t ht hthalf
    let z := (1-t) • x
    have htone : t ≤ 1 := by linarith
    have hin : inwardPoint 0 x t = z := by dsimp [inwardPoint, z]; module
    have horder : objective (normal n) z ≤ objective (normal n) x := by
      have hp := (objective_convex (normal n)).2 (mem_univ x) (mem_univ 0)
        (show 0 ≤ 1-t by linarith) ht.le (by ring : (1-t)+t=1)
      simp only [smul_zero, add_zero, objective_zero, smul_eq_mul, mul_zero, add_zero] at hp
      have hn := objective_minimum (normal n) x
      rw [objective_zero] at hn
      exact hp.trans (by nlinarith)
    have hzK : objective (normal n) z ≤ b := horder.trans hN
    have hzband : objective (normal n) 0 + η ≤ objective (normal n) z := by
      rw [objective_zero, zero_add]
      have hlower := objective_lower_bound (normal n) z
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
    have hg := objective_hasFDerivAt_pos (normal n) x hv
    have hh := objective_hasFDerivAt_pos (normal n) z hzpos
    apply hC x z (positiveGradient (normal n) x) (positiveGradient (normal n) z)
      hN hzK hzband horder hg hh
    rw [(radial_contraction_identities (normal n) x t).1]
    exact mul_pos ht (radial_difference_positive (normal n) x hv ht htone)
  have hunbounded := (sample_radial_curvature_unbounded n u).eventually (eventually_gt_atTop (4*C))
  obtain ⟨N, hN, hN'⟩ := (hbound.and hunbounded).exists
  exact (not_lt_of_ge hN) hN'

theorem not_radial_secant_sublevel (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ¬ HasRadialSecantBounds (objective (normal n)) {x | objective (normal n) x ≤ b} 0 := by
  apply not_radial_secant_sublevel_of_tangent_height n (Real.sqrt b) (Real.sqrt_pos.mpr hb)
  rw [Real.sq_sqrt hb.le]
  nlinarith

theorem not_radial_secant_neighborhood (n : ℕ) {K : Set (Vec (n+2))}
    (hK : K ∈ 𝓝 0) : ¬ HasRadialSecantBounds (objective (normal n)) K 0 := by
  intro hRS
  obtain ⟨ε, hε, hsub⟩ := Localization.neighborhood_basin (objective_convex (normal n)) 0
    (objective_minimum (normal n)) (objective_unique_minimum (normal n)) hK
  have hsub' : {x | objective (normal n) x ≤ ε} ⊆ K := by
    simpa only [objective_zero, zero_add] using hsub
  apply not_radial_secant_sublevel n hε
  intro η hη
  obtain ⟨C, hC⟩ := hRS η hη
  refine ⟨C, ?_⟩
  intro x z g h hx hz hzband horder hg hh ht
  exact hC x z g h (hsub' hx) (hsub' hz) hzband horder hg hh ht

theorem converges_without_radial_secant (n : ℕ) {K : Set (Vec (n+2))} (hK : K ∈ 𝓝 0) :
    (∀ R : AdmissibleBFGSRun (n+2) (objective (normal n)),
      Tendsto (fun k => objective (normal n) (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) ∧
    ¬ HasRadialSecantBounds (objective (normal n)) K 0 :=
  ⟨fun R => objective_fullBFGS_convergence (normal n) (normal_unit n) R,
    not_radial_secant_neighborhood n hK⟩

end BfgsVerification.NormalSpike
