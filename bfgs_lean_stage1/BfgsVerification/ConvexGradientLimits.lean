import BfgsVerification.EuclideanEstimates
import BfgsVerification.StrictContours

/-! Convex supporting vectors at differentiable limiting points converge to the
actual derivative. No gradient continuity on a neighborhood is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification

/-- A supporting vector at a differentiable point equals its actual gradient. -/
theorem supporting_vector_eq_gradient {n : ℕ} {F : Vec n → ℝ} {x a g : Vec n}
    (ha : ∀ z, dot a (z - x) ≤ F z - F x)
    (hg : HasFDerivAt F (gradientFunctional g) x) : a = g := by
  have hlocal : IsLocalMin (fun z => F z - dot a z) x := by
    apply IsMinOn.isLocalMin (s := Set.univ) _ (by simp)
    intro z _
    have h := ha z
    change a ⬝ᵥ (z - x) ≤ _ at h
    rw [dotProduct_sub] at h
    change F x - a ⬝ᵥ x ≤ F z - a ⬝ᵥ z
    linarith
  have hlinear : HasFDerivAt (fun z => dot a z) (gradientFunctional a) x := by
    convert (gradientFunctional a).hasFDerivAt using 1
    funext z
    exact (gradientFunctional_apply a z).symm
  have hzero := hlocal.hasFDerivAt_eq_zero (hg.sub hlinear)
  funext i
  have hi := congrArg (fun f : Vec n →L[ℝ] ℝ => f (Pi.single i 1)) hzero
  simp only [ContinuousLinearMap.sub_apply, gradientFunctional_apply, ContinuousLinearMap.zero_apply] at hi
  change dotProduct g (Pi.single i 1) - dotProduct a (Pi.single i 1) = 0 at hi
  rw [dotProduct_single_one, dotProduct_single_one] at hi
  linarith

theorem continuous_dot {n : ℕ} : Continuous (fun p : Vec n × Vec n => dot p.1 p.2) := by
  unfold dot
  fun_prop

/-- A convergent point/vector pair preserves the supporting inequality. -/
theorem supporting_limit {n : ℕ} {F : Vec n → ℝ} (hF : Continuous F)
    {x g : ℕ → Vec n} {xlim glim : Vec n}
    (hx : Tendsto x atTop (𝓝 xlim)) (hg : Tendsto g atTop (𝓝 glim))
    (hsupport : ∀ k z, dot (g k) (z - x k) ≤ F z - F (x k)) :
    ∀ z, dot glim (z - xlim) ≤ F z - F xlim := by
  intro z
  have hd : Tendsto (fun k => dot (g k) (z - x k)) atTop (𝓝 (dot glim (z - xlim))) := by
    unfold dot
    apply tendsto_finset_sum
    intro i _
    exact ((tendsto_pi_nhds.mp hg) i).mul
      (tendsto_const_nhds.sub ((tendsto_pi_nhds.mp hx) i))
  have hval : Tendsto (fun k => F z - F (x k)) atTop (𝓝 (F z - F xlim)) :=
    tendsto_const_nhds.sub ((hF.tendsto xlim).comp hx)
  have hineq : ∀ᶠ k in (atTop : Filter ℕ), dot (g k) (z - x k) ≤ F z - F (x k) :=
    Eventually.of_forall (fun k => hsupport k z)
  exact le_of_tendsto_of_tendsto hd hval hineq

/-- Global supporting vectors along converging points tend to the actual
gradient whenever the limiting point is differentiable. The neighboring points
need not themselves be differentiable. -/
theorem supporting_vectors_tendsto_at_differentiable {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x a : ℕ → Vec n} {star g : Vec n}
    (hx : Tendsto x atTop (𝓝 star))
    (hsupport : ∀ k z, dot (a k) (z - x k) ≤ F z - F (x k))
    (hg : HasFDerivAt F (gradientFunctional g) star) : Tendsto a atTop (𝓝 g) := by
  have hK := hx.isCompact_insert_range
  obtain ⟨G, hG, hbound⟩ := convex_supporting_bound_on_compact hF hK
  have hanorm (k : ℕ) : ‖a k‖ ≤ G := by
    apply (pi_norm_le_iff_of_nonneg hG.le).2
    intro i
    have hs := hbound (x k) (mem_insert_of_mem _ (mem_range_self k)) (a k) (hsupport k)
    have hi : (a k i) ^ 2 ≤ sqNorm (a k) :=
      Finset.single_le_sum (fun j _ => sq_nonneg (a k j)) (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) hG.le).mp
    simpa only [sq_abs] using hi.trans hs
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  by_contra hn
  push_neg at hn
  let S := Metric.closedBall (0 : Vec n) G ∩ {p | ε ≤ dist p g}
  have hS : IsCompact S := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hfreq : ∃ᶠ k in atTop, a k ∈ S := by
    apply frequently_atTop.mpr
    intro N
    obtain ⟨k, hk, hd⟩ := hn N
    refine ⟨k, hk, ?_, hd⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hanorm k
  obtain ⟨p, hp, φ, hφ, hpconv⟩ := hS.tendsto_subseq' hfreq
  have hpSupport := supporting_limit (convex_continuous hF) (hx.comp hφ.tendsto_atTop)
    hpconv (fun k z => hsupport (φ k) z)
  have heq := supporting_vector_eq_gradient hpSupport hg
  have hd : ε ≤ dist p g := hp.2
  rw [heq, dist_self] at hd
  linarith

/-- In particular, actual convex gradients converge along differentiable
approximating points when the limiting point is differentiable. -/
theorem convex_gradients_tendsto_at_differentiable {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x a : ℕ → Vec n} {star g : Vec n}
    (hx : Tendsto x atTop (𝓝 star))
    (hgrad : ∀ k, HasFDerivAt F (gradientFunctional (a k)) (x k))
    (hg : HasFDerivAt F (gradientFunctional g) star) : Tendsto a atTop (𝓝 g) :=
  supporting_vectors_tendsto_at_differentiable hF hx
    (fun k z => convex_supporting_inequality hF (hgrad k) z) hg

end BfgsVerification
