import BfgsVerification.ParabolicExampleSeparation
import BfgsVerification.ParabolicCertificate

/-! The explicit example's contrasting transported correction and actual-run
convergence. The field values below are the source's printed normalization. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification
namespace Parabolic
namespace Example
open TransportedCertificate RadialCertificate Family

/-- The printed scalar field, with the common interface value assigned by
the middle branch. Its endpoint formulas are checked below. -/
def sourceScale (x : Vec 2) : ℝ :=
  if x 1 < -(x 0)^2 then Real.exp ((x 0)^2/objective x-1/3)
  else if 2*(x 0)^2 < x 1 then Real.exp ((x 0)^2/(2*objective x)-1/6) else 1

theorem sourceScale_bounds {x : Vec 2} (hx : 0 < objective x) :
    Real.exp (-1/3 : ℝ) ≤ sourceScale x ∧ sourceScale x ≤ 1 := by
  have hq : 3*(x 0)^2 ≤ objective x := by
    simpa [family, Family.branch, objective] using family.branch_le 1 x
  have hlo : 0 ≤ (x 0)^2/objective x := div_nonneg (sq_nonneg _) hx.le
  have hhi : (x 0)^2/objective x ≤ 1/3 := (div_le_iff₀ hx).mpr (by linarith)
  have hh : (x 0)^2/(2*objective x) = ((x 0)^2/objective x)/2 := by ring
  unfold sourceScale
  split_ifs
  · constructor
    · exact Real.exp_le_exp.mpr (by linarith)
    · simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (x 0)^2/objective x-1/3 ≤ 0 by linarith)
  · constructor
    · apply Real.exp_le_exp.mpr
      rw [hh]
      linarith
    · simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (x 0)^2/(2*objective x)-1/6 ≤ 0 by rw [hh]; linarith)
  · constructor
    · simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (-1/3 : ℝ) ≤ 0 by norm_num)
    · exact le_rfl

theorem sourceScale_pair {u ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hs : ρ*ε < 3*u^2) :
    sourceScale (oldPoint u ε) = Real.exp (u^2/(2*(3*u^2+ε))-1/6) ∧
    sourceScale (newPoint u ρ ε) = 1 := by
  have hxlo : ¬ (oldPoint u ε) 1 < -((oldPoint u ε) 0)^2 := by
    change ¬ 2*u^2+ε < -u^2
    nlinarith [sq_nonneg u]
  have hxhi : 2*((oldPoint u ε) 0)^2 < (oldPoint u ε) 1 := by
    change 2*u^2 < 2*u^2+ε
    linarith
  have hzlo : ¬ (newPoint u ρ ε) 1 < -((newPoint u ρ ε) 0)^2 := by
    change ¬ 2*u^2-ρ*ε < -u^2
    linarith
  have hzhi : ¬ 2*((newPoint u ρ ε) 0)^2 < (newPoint u ρ ε) 1 := by
    change ¬ 2*u^2 < 2*u^2-ρ*ε
    nlinarith [mul_pos hρ hε]
  constructor
  · rw [sourceScale, if_neg hxlo, if_pos hxhi, (pair_values hρ hε hs).1]
    rfl
  · rw [sourceScale, if_neg hzlo, if_neg hzhi]

theorem transported_numerator (u ρ ε : ℝ) :
    dot (newGradient u-oldGradient u) (radialDirection (newPoint u ρ ε)) = 2*ρ*ε := by
  simp [newGradient, oldGradient, radialDirection, newPoint, dot, Fin.sum_univ_two]
  <;> ring

theorem transported_quotient {u ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    (dot (newGradient u-oldGradient u) (radialDirection (newPoint u ρ ε)))^2 /
      pairCurvature (oldPoint u ε) (newPoint u ρ ε) (oldGradient u) (newGradient u) =
        (4*ρ^2/(1+ρ))*ε := by
  rw [transported_numerator, pair_curvature]
  have h1 : 1+ρ ≠ 0 := by positivity
  field_simp [h1, hε.ne']
  <;> ring

theorem transported_quotient_tendsto (u : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun ε => (dot (newGradient u-oldGradient u) (radialDirection (newPoint u ρ ε)))^2 /
      pairCurvature (oldPoint u ε) (newPoint u ρ ε) (oldGradient u) (newGradient u))
      (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun ε : ℝ => (4*ρ^2/(1+ρ))*ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using (show Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).const_mul (4*ρ^2/(1+ρ))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (transported_quotient hρ hε).symm

theorem quotientMultiplier_eq_one (u ρ ε : ℝ) :
    quotientMultiplier (oldPoint u ε) (newPoint u ρ ε) = 1 := by
  simp [quotientMultiplier, horizontalStep, oldPoint, newPoint]

theorem source_compensated_log {u ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hs : ρ*ε < 3*u^2) :
    Real.log (sourceScale (newPoint u ρ ε) *
      quotientMultiplier (oldPoint u ε) (newPoint u ρ ε) / sourceScale (oldPoint u ε)) =
        ε/(6*(3*u^2+ε)) := by
  rw [(sourceScale_pair hρ hε hs).1, (sourceScale_pair hρ hε hs).2,
    quotientMultiplier_eq_one, one_mul, one_div, Real.log_inv, Real.log_exp]
  have hf : 3*u^2+ε ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg u])
  field_simp [hf]
  <;> ring

/-- Every actual full-BFGS run converges although RS fails on every
neighborhood of the minimizer. The bad pairs are not an infinite bad run. -/
theorem converges_without_radial_secant {K : Set (Vec 2)} (hK : K ∈ 𝓝 (0 : Vec 2)) :
    (∀ R : AdmissibleBFGSRun 2 objective,
      Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) ∧
      ¬ HasRadialSecantBounds objective K 0 := by
  exact ⟨fun R => R.parabolic_convergence family, not_radial_secant_on_neighborhood hK⟩

end Example
end Parabolic
end BfgsVerification
