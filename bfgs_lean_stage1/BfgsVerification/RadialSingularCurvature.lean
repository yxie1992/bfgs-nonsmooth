import BfgsVerification.ShiftedAbsAccessibility
import BfgsVerification.FiniteMaxCentralAsymptotic

noncomputable section
open scoped Topology
open Set Filter MeasureTheory
namespace BfgsVerification.RadialSingularCurvature
open ScalarCounterexamples

theorem shifted_second_derivative_one {x : ℝ} (hx : x ≠ 0) :
    deriv (deriv shiftedAbs) x=1 := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · have heq : deriv shiftedAbs =ᶠ[𝓝 x] (fun t => t+1) := by
      filter_upwards [eventually_lt_nhds hn] with t ht
      exact (shiftedAbs_hasDerivAt_neg ht).deriv
    exact ((hasDerivAt_id x).add_const 1).congr_of_eventuallyEq heq |>.deriv
  · have heq : deriv shiftedAbs =ᶠ[𝓝 x] (fun t => t+3) := by
      filter_upwards [eventually_gt_nhds hp] with t ht
      exact (shiftedAbs_hasDerivAt_pos ht).deriv
    exact ((hasDerivAt_id x).add_const 3).congr_of_eventuallyEq heq |>.deriv

theorem shifted_second_derivative_ae :
    ∀ᵐ x : ℝ ∂volume, deriv (deriv shiftedAbs) x=1 := by
  have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hn] with x hx
  exact shifted_second_derivative_one hx

theorem shifted_central_difference (t : ℝ) :
    RadialCertificate.centralDifference shiftedObjective (OneDimensional.embed (-1)) 0 t=
      t^2+2*|t| := by
  simp only [RadialCertificate.centralDifference,RadialCertificate.outwardPoint,
    RadialCertificate.inwardPoint,shiftedObjective,shiftedAbs,OneDimensional.embed,
    Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,zero_sub,sub_neg_eq_add,neg_neg,
    abs_neg,abs_zero]
  norm_num
  ring

theorem shifted_central_not_quadratic :
    ¬ RadialCertificate.centralDifference shiftedObjective (OneDimensional.embed (-1)) 0
      =O[𝓝 0] (fun t : ℝ => t^2) := by
  apply FiniteMaxRadial.not_isBigO_of_linear_abs_remainder (J := 2) (by norm_num)
  have he : (fun t => RadialCertificate.centralDifference shiftedObjective
      (OneDimensional.embed (-1)) 0 t-2*abs t)=(fun t : ℝ => t^2) := by
    ext t
    rw [shifted_central_difference]
    ring
  rw [he]
  exact Asymptotics.isBigO_refl _ _

theorem shifted_radial_hessian_ae_bounded :
    ∀ᵐ x : ℝ ∂volume, |x| ≤ 1/4 →
      0 ≤ (x+1)^2*deriv (deriv shiftedAbs) x ∧
      (x+1)^2*deriv (deriv shiftedAbs) x ≤ 25/16 := by
  filter_upwards [shifted_second_derivative_ae] with x hx hsmall
  rw [hx,mul_one]
  have hh := abs_le.mp hsmall
  exact ⟨sq_nonneg _,by nlinarith [sq_nonneg (x+1-5/4)]⟩

theorem crossing_radial_numerator (ε : ℝ) :
    RadialCertificate.radialNumerator (OneDimensional.embed (-1)) (crossingZ ε)
      (crossingG ε) (crossingH ε) = (1-ε/2-(3+ε))*(1-ε/2) := by
  simp only [RadialCertificate.radialNumerator,crossingZ,crossingG,crossingH,dot,
    Fin.sum_univ_one,Pi.sub_apply,OneDimensional.embed_apply]
  ring

theorem crossing_radial_curvature (ε : ℝ) :
    RadialCertificate.secantCurvature (crossingX ε) (crossingZ ε)
      (crossingG ε) (crossingH ε)=3*ε+9/4*ε^2 := crossing_curvature ε

/-- A compact-sublevel positive-band RS failure for the actual strongly convex
objective, although its classical scalar Hessian equals one almost everywhere. -/
theorem shifted_no_radial_secant_bounds :
    ¬ RadialCertificate.HasRadialSecantBounds shiftedObjective {x | shiftedObjective x ≤ 3}
      (OneDimensional.embed (-1)) := by
  intro hRS
  obtain ⟨C,hC⟩ := hRS (1/4) (by norm_num)
  have hbound (k : ℕ) : (1 : ℝ) ≤ C*(3*crossingScale k+9/4*(crossingScale k)^2) := by
    have hε := crossingScale_pos k
    have hs := crossingScale_le k
    have hb := crossing_band hε hs
    have hd := crossing_gradients hε
    have hord : shiftedObjective (crossingZ (crossingScale k)) ≤
        shiftedObjective (crossingX (crossingScale k)) := by
      rw [(crossing_values hε).1,(crossing_values hε).2]
      nlinarith [sq_nonneg (crossingScale k)]
    have ht : 0 < RadialCertificate.secantCurvature (crossingX (crossingScale k))
        (crossingZ (crossingScale k)) (crossingG (crossingScale k)) (crossingH (crossingScale k)) := by
      rw [crossing_radial_curvature]
      positivity
    have hc := hC _ _ _ _ hb.1.1 hb.2.1 hb.2.2 hord hd.1 hd.2 ht
    rw [crossing_radial_numerator,crossing_radial_curvature] at hc
    have he2 : (crossingScale k)^2 ≤ crossingScale k/8 := by
      nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hs)]
    have hn : (1-crossingScale k/2-(3+crossingScale k))*(1-crossingScale k/2) ≤ -1 := by
      nlinarith
    have hsq : (1 : ℝ) ≤ ((1-crossingScale k/2-(3+crossingScale k))*(1-crossingScale k/2))^2 := by
      nlinarith [sq_nonneg ((1-crossingScale k/2-(3+crossingScale k))*(1-crossingScale k/2)+1)]
    exact hsq.trans hc
  have hlim : Tendsto (fun k => C*(3*crossingScale k+9/4*(crossingScale k)^2)) atTop (𝓝 0) := by
    simpa using ((crossingScale_tendsto.const_mul 3).add
      ((crossingScale_tendsto.pow 2).const_mul (9/4 : ℝ))).const_mul C
  have hf : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hbound)
  norm_num at hf

theorem shifted_radial_hessian_on_sublevel_ae :
    ∀ᵐ x : ℝ ∂volume, shiftedAbs x ≤ 3 →
      0 ≤ (x+1)^2*deriv (deriv shiftedAbs) x ∧
      (x+1)^2*deriv (deriv shiftedAbs) x ≤ 3 := by
  filter_upwards [shifted_second_derivative_ae] with x hx hK
  rw [hx,mul_one]
  exact ⟨sq_nonneg _,by linarith [shiftedAbs_gap_lower x]⟩

/-- One actual finite strongly convex function has compact sublevels and an
attained unique minimum, a uniformly bounded classical radial Hessian almost
everywhere on the entire selected compact sublevel, yet fails RS there. -/
theorem singular_curvature_counterexample :
    StrongConvexOn univ 1 shiftedAbs ∧
    (∀ x, shiftedAbs (-1) ≤ shiftedAbs x) ∧
    (∀ x, shiftedAbs x=shiftedAbs (-1) → x=(-1)) ∧
    IsCompact {x : Vec 1 | shiftedObjective x ≤ 3} ∧
    (∀ᵐ x : ℝ ∂volume, shiftedAbs x ≤ 3 →
      0 ≤ (x+1)^2*deriv (deriv shiftedAbs) x ∧
      (x+1)^2*deriv (deriv shiftedAbs) x ≤ 3) ∧
    ¬ RadialCertificate.HasRadialSecantBounds shiftedObjective {x | shiftedObjective x ≤ 3}
      (OneDimensional.embed (-1)) :=
  ⟨shiftedAbs_strongConvex,shiftedAbs_minimum,shiftedAbs_unique,
    shiftedObjective_sublevel_compact 3,shifted_radial_hessian_on_sublevel_ae,
    shifted_no_radial_secant_bounds⟩

end BfgsVerification.RadialSingularCurvature
