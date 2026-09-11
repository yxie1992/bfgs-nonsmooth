import BfgsVerification.ParabolicUniformTransport
import BfgsVerification.TransportedCertificateVariants

/-! The actual Q certificate and full-BFGS convergence theorem. -/
noncomputable section
open scoped BigOperators Topology
open Set Matrix Filter
namespace BfgsVerification
namespace Parabolic
namespace Family
open TransportedCertificate
variable {m : ℕ} (P : Family m)

/-- Q.8 is an actual PSD matrix field satisfying all three certificate clauses.
Constants are uniform before the eligible pairs, even on empty positive bands. -/
theorem exists_bandCertificate {K : Set (Vec 2)} (hK : IsCompact K)
    {η c₁ c₂ : ℝ} (hη : 0 < η) (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) :
    ∃ B : BandCertificate P.objective K 0 c₁ c₂ η,
      ∀ x, B.W x = outer (P.calibratedVector x) (P.calibratedVector x) := by
  obtain ⟨θlo, θhi, hlo, hhi, hscale⟩ := P.calibratedScale_uniform_bounds
  obtain ⟨C, hC, hsec⟩ := P.exists_uniform_secant_bound hK hc₁ hc₂
  obtain ⟨L, δ, hL, hδ, hδ1, htransport⟩ := P.exists_uniform_vector_transport hK hη hc₁ hc₂
  have hV : ∀ x ∈ positiveBand P.objective K 0 η, ∀ g,
      HasFDerivAt P.objective (gradientFunctional g) x →
      θlo^2*(4*η^2) ≤ (dot g (P.calibratedVector x))^2 := by
    intro x hx g hg
    have hFx : η ≤ P.objective x := by simpa only [zero_add] using hx.2
    have hlow := (hscale x (hη.trans_le hFx)).1
    have hscsq : θlo^2 ≤ (P.calibratedScale x)^2 := by nlinarith
    rw [calibratedVector, dot_smul_right, mul_pow]
    exact mul_le_mul hscsq (P.positive_visibility hη.le hFx hg)
      (by positivity) (sq_nonneg _)
  have hS : ∀ x z g h, x ∈ positiveBand P.objective K 0 η →
      z ∈ positiveBand P.objective K 0 η → EligiblePair P.objective c₁ c₂ x z g h →
      pairDecrease x z g ≤ δ →
      (dot (h-g) (P.calibratedVector z))^2 ≤ (θhi^2*C)*pairCurvature x z g h := by
    intro x z g h hx hz hp hd
    have hFz : η ≤ P.objective z := by simpa only [zero_add] using hz.2
    have hupp := (hscale z (hη.trans_le hFz)).2
    have hscsq : (P.calibratedScale z)^2 ≤ θhi^2 := by
      nlinarith [P.calibratedScale_pos z]
    rw [calibratedVector, dot_smul_right, mul_pow]
    have hb := mul_le_mul hscsq (hsec x hx.1 z hz.1 g h hp (hd.trans hδ1))
      (sq_nonneg _) (sq_nonneg θhi)
    exact hb.trans_eq (by ring)
  have hT : ∀ x z g h, x ∈ positiveBand P.objective K 0 η →
      z ∈ positiveBand P.objective K 0 η → EligiblePair P.objective c₁ c₂ x z g h →
      pairDecrease x z g ≤ δ → ∃ ell β : ℝ,
        P.calibratedVector z = ell • P.calibratedVector x + β • pairStep x z ∧
        ell^2 ≤ 1+L*pairDecrease x z g := by
    intro x z g h hx hz hp hd
    exact htransport x hx.1 z hz.1 g h hp
      (by simpa only [zero_add] using hx.2) (by simpa only [zero_add] using hz.2) hd
  exact ⟨rankOneCertificate P.calibratedVector (θlo^2*(4*η^2)) (θhi^2*C) L δ
    (by positivity) hL hδ hV hS hT, fun _ => rfl⟩

/-- Module T's exact objective-only condition is derived for every original
finite parabolic maximum. There is no assumed scalar or matrix hierarchy. -/
theorem hasBandCertificates {K : Set (Vec 2)} (hK : IsCompact K)
    {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) :
    HasBandCertificates P.objective K 0 c₁ c₂ := by
  intro η hη _hne
  obtain ⟨B, _hW⟩ := P.exists_bandCertificate hK hη hc₁ hc₂
  exact ⟨B⟩

/-- The selector-free matrix field is continuous on F>0, including every
switching interface; no continuity at the minimizer is asserted. -/
theorem calibratedVector_continuousOn :
    ContinuousOn P.calibratedVector {x | 0 < P.objective x} := by
  have hr : Continuous (radialDirection : Vec 2 → Vec 2) := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun x : Vec 2 => x 0)
      exact continuous_apply 0
    · change Continuous (fun x : Vec 2 => 2*x 1)
      fun_prop
  exact P.calibratedScale_continuousOn.smul hr.continuousOn

theorem certificateField_continuousOn :
    ContinuousOn (fun x => outer (P.calibratedVector x) (P.calibratedVector x))
      {x | 0 < P.objective x} := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact (continuous_apply i |>.comp_continuousOn P.calibratedVector_continuousOn).mul
    (continuous_apply j |>.comp_continuousOn P.calibratedVector_continuousOn)

end Family
end Parabolic

namespace AdmissibleBFGSRun

/-- Q's principal theorem for every admissible unmodified full-BFGS run, with
only initial positive definiteness, differentiable accepted endpoints and the
ordinary Armijo--weak-Wolfe hypotheses in the run specification. -/
theorem parabolic_convergence {m : ℕ} (P : Parabolic.Family m)
    (R : AdmissibleBFGSRun 2 P.objective) :
    Tendsto (fun k => P.objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have hcert := P.hasBandCertificates (P.sublevel_compact (P.objective (R.x 0)))
    R.c₁_pos.le R.c₂_lt_one
  have hcert' : TransportedCertificate.HasBandCertificates P.objective
      {x | P.objective x ≤ P.objective (R.x 0)} (P.objective 0) R.c₁ R.c₂ := by
    simpa only [P.objective_zero] using hcert
  have hb := R.transported_certificate_convergence_on_sublevel (P.objective (R.x 0))
    (P.sublevel_compact _) 0 P.unique_minimum.1 le_rfl hcert'
  exact ⟨by simpa only [P.objective_zero] using hb.1, hb.2.2 P.unique_minimum.2⟩

end AdmissibleBFGSRun
end BfgsVerification
