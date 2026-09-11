import BfgsVerification.PoweredGaugeRadial
import BfgsVerification.UnexcitedMetric

noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification.InterceptExamples

theorem homogeneous_intercept_zero {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (hh : Homogeneous.PositiveDegreeOne F) {x g : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    RadialCertificate.optimizerIntercept F 0 x g=0 := by
  simp only [RadialCertificate.optimizerIntercept,sub_zero,Homogeneous.value_zero hh]
  rw [Homogeneous.supporting_euler hh (convex_supporting_inequality hF hg)]
  ring

def PositiveDegree (p : ℝ) {n : ℕ} (F : Vec n → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x)=t^p*F x

theorem degree_euler {n : ℕ} {F : Vec n → ℝ} {p : ℝ}
    (hh : PositiveDegree p F) {x g : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) : dot g x=p*F x := by
  have hc : HasDerivAt (fun t : ℝ => t • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hdF := hg.comp_hasDerivAt_of_eq 1 hc (by simp)
  have hdp : HasDerivAt (fun t : ℝ => t^p*F x) (p*F x) 1 := by
    convert ((hasDerivAt_id (1 : ℝ)).rpow_const (p := p) (Or.inl (by norm_num))).mul_const (F x) using 1 <;> simp
  have heq : (fun t : ℝ => F (t • x)) =ᶠ[𝓝 1] (fun t => t^p*F x) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    exact hh t ht.le x
  simpa only [gradientFunctional_apply] using (hdF.congr_of_eventuallyEq heq.symm).unique hdp

/-- Without a positive-degree/zero-minimum convention, the value at zero must
be retained. This identity is valid for every real degree. -/
theorem degree_intercept_with_zero_value {n : ℕ} {F : Vec n → ℝ} {p : ℝ}
    (hh : PositiveDegree p F) {x g : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    RadialCertificate.optimizerIntercept F 0 x g=(p-1)*F x+F 0 := by
  simp only [RadialCertificate.optimizerIntercept,sub_zero,degree_euler hh hg]
  ring

theorem degree_value_zero {n : ℕ} {F : Vec n → ℝ} {p : ℝ}
    (hp : 0 < p) (hh : PositiveDegree p F) : F 0=0 := by
  simpa only [zero_smul,Real.zero_rpow hp.ne',zero_mul] using hh 0 le_rfl 0

/-- Literal source degree-p intercept identity; it is derived from actual
homogeneity and the actual derivative, not a premise on the radial pairing. -/
theorem degree_intercept {n : ℕ} {F : Vec n → ℝ} {p : ℝ}
    (hp : 0 < p) (hh : PositiveDegree p F) {x g : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    RadialCertificate.optimizerIntercept F 0 x g=(p-1)*F x := by
  simp only [RadialCertificate.optimizerIntercept,sub_zero,degree_value_zero hp hh,degree_euler hh hg]
  ring

theorem quadratic_absolute_radial_pairing {x g : Vec 2}
    (hg : HasFDerivAt UnexcitedMetric.objective (gradientFunctional g) x) :
    dot g x=2*(x 0)^2+|x 1| := by
  have hc : HasDerivAt (fun t : ℝ => t • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hdF := hg.comp_hasDerivAt_of_eq 1 hc (by simp)
  have hdmodel : HasDerivAt (fun t : ℝ => t^2*(x 0)^2+t*|x 1|)
      (2*(x 0)^2+|x 1|) 1 := by
    convert (((hasDerivAt_id (1 : ℝ)).pow 2).mul_const ((x 0)^2)).add
      ((hasDerivAt_id (1 : ℝ)).mul_const |x 1|) using 1 <;> norm_num
  have heq : (fun t : ℝ => UnexcitedMetric.objective (t • x)) =ᶠ[𝓝 1]
      (fun t => t^2*(x 0)^2+t*|x 1|) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    simp only [UnexcitedMetric.objective,Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_pos ht]
    ring
  simpa only [gradientFunctional_apply] using (hdF.congr_of_eventuallyEq heq.symm).unique hdmodel

theorem quadratic_absolute_intercept {x g : Vec 2}
    (hg : HasFDerivAt UnexcitedMetric.objective (gradientFunctional g) x) :
    RadialCertificate.optimizerIntercept UnexcitedMetric.objective 0 x g=(x 0)^2 := by
  simp only [RadialCertificate.optimizerIntercept,sub_zero,quadratic_absolute_radial_pairing hg]
  simp [UnexcitedMetric.objective]
  ring

end BfgsVerification.InterceptExamples
