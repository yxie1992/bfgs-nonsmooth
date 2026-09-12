import BfgsVerification.OptimizerInterceptExamples
import BfgsVerification.InwardRadial

/-! Article-only literal specialization of the reviewed inward convergence
chain to u²+|v|. All infinite admissible runs are quantified; this is not the
special vertical run family from UnexcitedMetric. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace ArticlePositive
open BfgsVerification RadialCertificate

/-- Actual inward remainder, with the necessary parameter range retained. -/
theorem mixed_inward_error {x g : Vec 2}
    (hg : HasFDerivAt UnexcitedMetric.objective (gradientFunctional g) x)
    {τ : ℝ} (_hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    supportingError UnexcitedMetric.objective x g (inwardPoint 0 x τ) =
      τ ^ 2 * (x 0) ^ 2 := by
  rw [inward_error_eq, sub_zero, InterceptExamples.quadratic_absolute_radial_pairing hg]
  have hin : inwardPoint 0 x τ = (1 - τ) • x := by
    unfold inwardPoint
    module
  rw [hin]
  simp only [UnexcitedMetric.objective, Pi.smul_apply, smul_eq_mul,
    abs_mul, abs_of_nonneg (sub_nonneg.mpr hτ1)]
  ring

/-- The positive-band bound follows from the actual objective sublevel. -/
theorem mixed_inward_on_sublevel (b : ℝ) :
    HasInwardTaylorBounds UnexcitedMetric.objective
      {x : Vec 2 | UnexcitedMetric.objective x ≤ b} 0 := by
  intro η hη
  refine ⟨2*b, 1/2, by norm_num, le_rfl, ?_⟩
  intro x g hx _ hg τ hτ0 hτhalf
  rw [mixed_inward_error hg hτ0 (by linarith)]
  constructor
  · positivity
  · have hx0 : (x 0)^2 ≤ b :=
      (le_add_of_nonneg_right (abs_nonneg (x 1))).trans hx
    nlinarith [mul_le_mul_of_nonneg_left hx0 (sq_nonneg τ)]

/-- Whole-sequence global convergence for the literal mixed benchmark,
with arbitrary SPD initialization and fixed valid Armijo--weak-Wolfe
constants supplied by the actual admissible-run structure. -/
theorem mixed_benchmark_global
    (R : AdmissibleBFGSRun 2 UnexcitedMetric.objective) :
    Tendsto (fun k => UnexcitedMetric.objective (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0) := by
  have hmin : ∀ x, UnexcitedMetric.objective 0 ≤ UnexcitedMetric.objective x := by
    intro x
    simpa [UnexcitedMetric.objective] using UnexcitedMetric.objective_nonneg x
  have hu : ∀ x, UnexcitedMetric.objective x = UnexcitedMetric.objective 0 → x = 0 :=
    fun _ hx => UnexcitedMetric.unique_minimum hx
  have hK := R.initialSublevel_compact_of_unique_minimizer 0 hmin hu
  have hRS := radial_of_inward_on_compact R.convex hK 0
    (mixed_inward_on_sublevel (UnexcitedMetric.objective (R.x 0)))
  obtain ⟨hv, _, hi⟩ := R.radial_certificate_convergence_on_sublevel
    (UnexcitedMetric.objective (R.x 0)) hK 0 hmin le_rfl hRS
  exact ⟨by simpa [UnexcitedMetric.objective] using hv, hi hu⟩

#print axioms mixed_inward_error
#print axioms mixed_inward_on_sublevel
#print axioms mixed_benchmark_global
end ArticlePositive
