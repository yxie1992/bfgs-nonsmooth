import BfgsVerification.ScaledCopyRun

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.ScaledCopy.Data
open LScalarGeometric DeterministicLineSearch
variable {n : ℕ} {Q F : Vec n → ℝ} {c : Vec n} {C : ℝ} {U : Set (Vec n)}

theorem query_hasGradient (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U)
    (m k : ℕ) (a : ℝ) (hU : R.x k+a • bfgsStep (R.H k) (R.g k) 1∈U)
    (hd : DifferentiableAt ℝ Q (R.x k+a • bfgsStep (R.H k) (R.g k) 1)) :
    HasFDerivAt F (gradientFunctional (scale m • coordinateGradient Q
      (R.x k+a • bfgsStep (R.H k) (R.g k) 1)))
      ((D.run R hx m).x k+a • bfgsStep ((D.run R hx m).H k) ((D.run R hx m).g k) 1) := by
  rw [D.query_identity]
  exact TranslatedRun.local_model_hasGradient D.open_domain (scale_pos m).ne' hU (D.model_offset m)
    (hasFDerivAt_coordinateGradient hd)

theorem query_value (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U)
    (m k : ℕ) (a : ℝ) (hU : R.x k+a • bfgsStep (R.H k) (R.g k) 1∈U) :
    F ((D.run R hx m).x k+a • bfgsStep ((D.run R hx m).H k) ((D.run R hx m).g k) 1)=
      (scale m)^2*(C+Q (R.x k+a • bfgsStep (R.H k) (R.g k) 1)) := by
  rw [D.query_identity]
  exact D.model m _ hU

theorem query_norm_bound (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U)
    (m k : ℕ) (a M : ℝ) (hb : ‖R.x k+a • bfgsStep (R.H k) (R.g k) 1‖≤M) :
    ‖(D.run R hx m).x k+a • bfgsStep ((D.run R hx m).H k) ((D.run R hx m).g k) 1‖≤
      scale m*(‖c‖+M) := by
  rw [D.query_identity]
  have hh := norm_add_le (scale m • c) (scale m • (R.x k+a • bfgsStep (R.H k) (R.g k) 1))
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (scale_pos m)] at hh
  have hu := mul_le_mul_of_nonneg_left hb (scale_pos m).le
  nlinarith

theorem all_queries_uniformly_small (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U)
    (fuel : ℕ) (M : ℝ)
    (hb : ∀k,∀a∈(fromMetric Q (R.x k) (R.H k) R.c₁ R.c₂ fuel).2,
      ‖R.x k+a • bfgsStep (R.H k) (R.g k) 1‖≤M)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ m in atTop,∀k,∀a∈(fromMetric Q (R.x k) (R.H k) R.c₁ R.c₂ fuel).2,
      ‖(D.run R hx m).x k+a • bfgsStep ((D.run R hx m).H k) ((D.run R hx m).g k) 1‖<ε := by
  have ht : Tendsto (fun m => scale m*(‖c‖+M)) atTop (𝓝 0) := by
    simpa only [zero_mul] using LScalar.scale_tendsto_zero.mul_const (‖c‖+M)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with m hm
  intro k a ha
  exact (D.query_norm_bound R hx m k a M (hb k a ha)).trans_lt hm

theorem queries_tendsto (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U)
    (m : ℕ) (a : ℕ → ℝ)
    (ht : Tendsto (fun k => R.x k+a k • bfgsStep (R.H k) (R.g k) 1) atTop (𝓝 0)) :
    Tendsto (fun k => (D.run R hx m).x k+a k •
      bfgsStep ((D.run R hx m).H k) ((D.run R hx m).g k) 1) atTop (𝓝 (scale m • c)) := by
  simp_rw [D.query_identity]
  simpa only [smul_zero,add_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => scale m • c) atTop (𝓝 (scale m • c))).add
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => scale m) atTop (𝓝 (scale m))).smul ht)

end BfgsVerification.ScaledCopy.Data
