import BfgsVerification.BoundedAnalyticLift

noncomputable section
open scoped Topology BoundedContinuousFunction
open Set Filter
namespace BfgsVerification.BoundedAnalytic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A zero first derivative is preserved by actual analytic superposition on
the Banach space of bounded sequences. -/
theorem exists_analytic_lift_zero {f : E → F} (hf : AnalyticAt ℝ f 0)
    (h0 : f 0=0) (hd : HasFDerivAt f (0 : E →L[ℝ] F) 0) :
    ∃ L : (ℕ →ᵇ E) → (ℕ →ᵇ F), AnalyticAt ℝ L 0 ∧ L 0=0 ∧
      HasStrictFDerivAt L (0 : (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ F)) 0 ∧
      ∃ R : ℝ, 0<R ∧ ∀ w : ℕ →ᵇ E, ‖w‖<R → ∀ k : ℕ, L w k=f (w k) := by
  obtain ⟨L,hL,R,hR,heq⟩ := exists_analytic_lift hf
  have hL0 : L 0=0 := by
    ext k
    change L 0 k=0
    simpa [h0] using heq 0 (by simpa using hR) k
  have hLd := (hL.contDiffAt (n := 1)).differentiableAt le_rfl |>.hasFDerivAt
  have hD : fderiv ℝ L 0=0 := by
    apply ContinuousLinearMap.ext
    intro v
    apply BoundedContinuousFunction.ext
    intro k
    have hleft := (BoundedContinuousFunction.evalCLM ℝ k : (ℕ →ᵇ F) →L[ℝ] F).hasFDerivAt.comp (0 : ℕ →ᵇ E) hLd
    have hright := hd.comp (0 : ℕ →ᵇ E) (BoundedContinuousFunction.evalCLM ℝ k : (ℕ →ᵇ E) →L[ℝ] E).hasFDerivAt
    have hevent : (fun w : ℕ →ᵇ E => L w k) =ᶠ[𝓝 0] (fun w => f (w k)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℕ →ᵇ E) hR] with w hw
      exact heq w (by simpa only [Metric.mem_ball,dist_zero_right] using hw) k
    have huniq := hleft.unique (hright.congr_of_eventuallyEq hevent)
    have hval := congrArg (fun D : (ℕ →ᵇ E) →L[ℝ] F => D v) huniq
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.zero_apply,
      BoundedContinuousFunction.evalCLM_apply] using hval
  have hd0 : HasFDerivAt L (0 : (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ F)) 0 := hLd.congr_fderiv hD
  exact ⟨L,hL,hL0,(hL.contDiffAt (n := 1)).hasStrictFDerivAt' hd0 le_rfl,R,hR,heq⟩

end BfgsVerification.BoundedAnalytic
