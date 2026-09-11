import BfgsVerification.BoundedCoefficient
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open scoped Topology BigOperators BoundedContinuousFunction
open Set Filter
namespace BfgsVerification.BoundedAnalytic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem apply_mem_eball {w : ℕ →ᵇ E} {r : ENNReal}
    (hw : w∈EMetric.ball (0 : ℕ →ᵇ E) r) (k : ℕ) : w k∈EMetric.ball (0 : E) r := by
  have he : edist (w k) (0 : E)≤edist w 0 := by
    simp only [edist_dist,dist_zero_right]
    exact ENNReal.ofReal_le_ofReal (w.norm_coe_le_norm k)
  exact he.trans_lt hw

theorem seriesLift_sum_apply {f : E → F} {p : FormalMultilinearSeries ℝ E F} {r : ENNReal}
    (hp : HasFPowerSeriesOnBall f p 0 r) {w : ℕ →ᵇ E}
    (hw : w∈EMetric.ball (0 : ℕ →ᵇ E) r) (k : ℕ) : (seriesLift p).sum w k=f (w k) := by
  have hwr : w∈EMetric.ball (0 : ℕ →ᵇ E) (seriesLift p).radius :=
    lt_of_lt_of_le hw (hp.r_le.trans (seriesLift_radius p))
  have hsum := (BoundedContinuousFunction.evalCLM ℝ k).hasSum ((seriesLift p).hasSum hwr)
  have hpoint := hp.hasSum (apply_mem_eball hw k)
  have hs : HasSum (fun n => p n (fun _ => w k)) ((seriesLift p).sum w k) := by
    simpa only [seriesLift,coefficientLift_apply,BoundedContinuousFunction.evalCLM_apply] using hsum
  exact hs.unique (by simpa only [zero_add] using hpoint)

/-- Actual analytic superposition near the zero bounded sequence. The map is
constructed from the lifted convergent series and agrees pointwise with f. -/
theorem exists_analytic_lift {f : E → F} (hf : AnalyticAt ℝ f 0) :
    ∃ L : (ℕ →ᵇ E) → (ℕ →ᵇ F), AnalyticAt ℝ L 0 ∧
      ∃ R : ℝ, 0<R ∧ ∀ w : ℕ →ᵇ E, ‖w‖<R → ∀ k : ℕ, L w k=f (w k) := by
  obtain ⟨p,r,hp⟩ := hf
  have hpos : 0<(seriesLift p).radius := hp.r_pos.trans_le (hp.r_le.trans (seriesLift_radius p))
  refine ⟨(seriesLift p).sum,((seriesLift p).hasFPowerSeriesOnBall hpos).analyticAt,?_⟩
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (EMetric.ball_mem_nhds (0 : ℕ →ᵇ E) hp.r_pos)
  refine ⟨R,hR,?_⟩
  intro w hw k
  exact seriesLift_sum_apply hp (hball (by simpa only [Metric.mem_ball,dist_zero_right] using hw)) k

end BfgsVerification.BoundedAnalytic
