import BfgsVerification.LocalizationCorollaries

/-!
# Module G: scalar convergence with arbitrary positive metrics

This run model has no BFGS update. It records actual scalar derivatives only at
accepted iterates, positive scalar metrics and step lengths, and ordinary
Armijo--weak-Wolfe acceptance. No iterate or metric convergence is assumed.
-/

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification

structure ScalarMetricRun (f : ℝ → ℝ) where
  convex : ConvexOn ℝ Set.univ f
  x : ℕ → ℝ
  g : ℕ → ℝ
  metric : ℕ → ℝ
  α : ℕ → ℝ
  c₁ : ℝ
  c₂ : ℝ
  c₁_pos : 0 < c₁
  c₁_lt_c₂ : c₁ < c₂
  c₂_lt_one : c₂ < 1
  metric_pos : ∀ k, 0 < metric k
  alpha_pos : ∀ k, 0 < α k
  gradient_ne : ∀ k, g k ≠ 0
  hasDeriv : ∀ k, HasDerivAt f (g k) (x k)
  step : ∀ k, x (k + 1) = x k - α k * metric k * g k
  armijo : ∀ k, f (x (k + 1)) ≤ f (x k) + c₁ * g k * (x (k + 1) - x k)
  weak_wolfe : ∀ k, c₂ * g k * (x (k + 1) - x k) ≤
    g (k + 1) * (x (k + 1) - x k)

namespace ScalarMetricRun

variable {f : ℝ → ℝ} (R : ScalarMetricRun f)

def d (k : ℕ) : ℝ := R.α k * R.metric k * (R.g k) ^ 2

def initialSublevel : Set ℝ := {x | f x ≤ f (R.x 0)}

include R in
theorem continuous_objective : Continuous f :=
  continuous_iff_continuousOn_univ.mpr (R.convex.continuousOn isOpen_univ)

theorem d_pos (k : ℕ) : 0 < R.d k :=
  mul_pos (mul_pos (R.alpha_pos k) (R.metric_pos k)) (sq_pos_of_ne_zero (R.gradient_ne k))

theorem gradient_step (k : ℕ) : R.g k * (R.x (k + 1) - R.x k) = -R.d k := by
  rw [R.step]
  unfold d
  ring

theorem d_eq_abs_gradient_mul_abs_step (k : ℕ) :
    R.d k = |R.g k| * |R.x (k + 1) - R.x k| := by
  have h := congrArg abs (R.gradient_step k)
  simpa only [abs_mul, abs_neg, abs_of_pos (R.d_pos k)] using h.symm

theorem armijo_decrease (k : ℕ) :
    R.c₁ * R.d k ≤ f (R.x k) - f (R.x (k + 1)) := by
  have h := R.armijo k
  rw [mul_assoc, R.gradient_step] at h
  linarith

theorem objective_antitone : Antitone (fun k => f (R.x k)) :=
  DescentBudget.armijo_antitone R.c₁_pos (fun k => (R.d_pos k).le) R.armijo_decrease

theorem iterate_mem_initialSublevel (k : ℕ) : R.x k ∈ R.initialSublevel :=
  R.objective_antitone (Nat.zero_le k)

theorem summable_d_of_minimizer (xStar : ℝ) (hmin : ∀ x, f xStar ≤ f x) :
    Summable R.d :=
  DescentBudget.armijo_summable R.c₁_pos (fun k => (R.d_pos k).le)
    R.armijo_decrease (fun k => hmin (R.x k))

/-- The actual scalar derivative supplies the global supporting inequality. -/
theorem supporting (k : ℕ) (y : ℝ) :
    R.g k * (y - R.x k) ≤ f y - f (R.x k) := by
  rcases lt_trichotomy (R.x k) y with hxy | heq | hyx
  · have h := R.convex.le_slope_of_hasDerivAt (by trivial) (by trivial) hxy (R.hasDeriv k)
    rw [slope_def_field] at h
    exact (le_div_iff₀ (sub_pos.mpr hxy)).mp h
  · simp [← heq]
  · have h := R.convex.slope_le_of_hasDerivAt (by trivial) (by trivial) hyx (R.hasDeriv k)
    rw [slope_def_field] at h
    have hm := (div_le_iff₀ (sub_pos.mpr hyx)).mp h
    nlinarith

theorem gap_le_gradient_pairing (xStar : ℝ) (k : ℕ) :
    f (R.x k) - f xStar ≤ R.g k * (R.x k - xStar) := by
  have h := R.supporting k xStar
  nlinarith

/-- A positive objective gap on a compact sublevel gives a uniform positive
lower bound for the absolute value of every actual derivative. -/
theorem abs_gradient_lower_of_gap (hK : IsCompact R.initialSublevel)
    (xStar L : ℝ) (hL : 0 < L) (hgap : ∀ k, L ≤ f (R.x k) - f xStar) :
    ∃ m : ℝ, 0 < m ∧ ∀ k, m ≤ |R.g k| := by
  obtain ⟨B, hB, hsub⟩ := hK.isBounded.subset_closedBall_lt 0 xStar
  refine ⟨L / B, div_pos hL hB, ?_⟩
  intro k
  have hdist : |R.x k - xStar| ≤ B := by
    simpa only [Metric.mem_closedBall, Real.dist_eq] using hsub (R.iterate_mem_initialSublevel k)
  have hp := (hgap k).trans (R.gap_le_gradient_pairing xStar k)
  have hbound : R.g k * (R.x k - xStar) ≤ |R.g k| * B := by
    calc
      _ ≤ |R.g k * (R.x k - xStar)| := le_abs_self _
      _ = |R.g k| * |R.x k - xStar| := abs_mul _ _
      _ ≤ |R.g k| * B := mul_le_mul_of_nonneg_left hdist (abs_nonneg _)
  exact (div_le_iff₀ hB).mpr (hp.trans hbound)

/-- In one dimension the positive-metric identity turns a lower derivative
bound into summable accepted step lengths. -/
theorem summable_step_dist_of_gradient_lower (hs : Summable R.d)
    (m : ℝ) (hm : 0 < m) (hg : ∀ k, m ≤ |R.g k|) :
    Summable (fun k => dist (R.x k) (R.x (k + 1))) := by
  apply Summable.of_nonneg_of_le (fun _ => dist_nonneg) _ (hs.div_const m)
  intro k
  rw [Real.dist_eq, abs_sub_comm]
  apply (le_div_iff₀ hm).mpr
  rw [R.d_eq_abs_gradient_mul_abs_step]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hg k) (abs_nonneg (R.x (k + 1) - R.x k))

/-- Weak Wolfe for a positive scalar metric has this exact product form. -/
theorem wolfe_gradient_product (k : ℕ) :
    R.g (k + 1) * R.g k ≤ R.c₂ * (R.g k) ^ 2 := by
  have h := R.weak_wolfe k
  rw [R.step] at h
  have heq : R.x k - R.α k * R.metric k * R.g k - R.x k =
      -(R.α k * R.metric k) * R.g k := by ring
  rw [heq] at h
  apply (mul_le_mul_left (mul_pos (R.alpha_pos k) (R.metric_pos k))).mp
  nlinarith [h]

/-- On either fixed gradient-sign branch, weak Wolfe contracts the derivative. -/
theorem abs_gradient_contracts_of_same_sign (k : ℕ)
    (hsign : (0 < R.g k ∧ 0 < R.g (k + 1)) ∨
      (R.g k < 0 ∧ R.g (k + 1) < 0)) :
    |R.g (k + 1)| ≤ R.c₂ * |R.g k| := by
  have hp := R.wolfe_gradient_product k
  rcases hsign with ⟨hg, hn⟩ | ⟨hg, hn⟩
  · rw [abs_of_pos hg, abs_of_pos hn]
    apply (mul_le_mul_right hg).mp
    nlinarith
  · rw [abs_of_neg hg, abs_of_neg hn]
    apply (mul_le_mul_right (neg_pos.mpr hg)).mp
    nlinarith

/-- Strictly positive objective gap fixes the derivative sign on each side
of the reference minimizer. -/
theorem gradient_sign_of_gap (xStar : ℝ) (k : ℕ)
    (hgap : 0 < f (R.x k) - f xStar) :
    (R.x k < xStar → R.g k < 0) ∧ (xStar < R.x k → 0 < R.g k) := by
  have hp := R.gap_le_gradient_pairing xStar k
  constructor
  · intro hx
    by_contra hn
    have hg := le_of_not_gt hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos hg (sub_nonpos.mpr hx.le)
    linarith
  · intro hx
    by_contra hn
    have hg := le_of_not_gt hn
    have hprod := mul_nonpos_of_nonpos_of_nonneg hg (sub_nonneg.mpr hx.le)
    linarith

/-- A hypothetical positive objective gap cannot persist for a scalar run.
The summable-distance and same-side arguments use no BFGS update. -/
theorem no_uniform_positive_gap (hK : IsCompact R.initialSublevel)
    (xStar : ℝ) (hmin : ∀ x, f xStar ≤ f x) (L : ℝ) (hL : 0 < L)
    (hgap : ∀ k, L ≤ f (R.x k) - f xStar) : False := by
  obtain ⟨m, hm, hg⟩ := R.abs_gradient_lower_of_gap hK xStar L hL hgap
  have hsum := R.summable_step_dist_of_gradient_lower (R.summable_d_of_minimizer xStar hmin)
    m hm hg
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)
  have hlimitgap : L ≤ f a - f xStar :=
    ge_of_tendsto (x := (atTop : Filter ℕ)) (((R.continuous_objective.tendsto a).comp ha).sub_const (f xStar))
      (Eventually.of_forall hgap)
  have hane : a ≠ xStar := by
    intro heq
    rw [heq, sub_self] at hlimitgap
    linarith
  have hcontract : ∃ J : ℕ, ∀ k ≥ J, |R.g (k + 1)| ≤ R.c₂ * |R.g k| := by
    rcases lt_or_gt_of_ne hane with halt | hagt
    · obtain ⟨J, hJ⟩ := eventually_atTop.mp (ha.eventually_lt_const halt)
      refine ⟨J, ?_⟩
      intro k hk
      apply R.abs_gradient_contracts_of_same_sign k
      right
      exact ⟨(R.gradient_sign_of_gap xStar k (hL.trans_le (hgap k))).1 (hJ k hk),
        (R.gradient_sign_of_gap xStar (k + 1) (hL.trans_le (hgap (k + 1)))).1
          (hJ (k + 1) (by omega))⟩
    · obtain ⟨J, hJ⟩ := eventually_atTop.mp (ha.eventually (eventually_gt_nhds hagt))
      refine ⟨J, ?_⟩
      intro k hk
      apply R.abs_gradient_contracts_of_same_sign k
      left
      exact ⟨(R.gradient_sign_of_gap xStar k (hL.trans_le (hgap k))).2 (hJ k hk),
        (R.gradient_sign_of_gap xStar (k + 1) (hL.trans_le (hgap (k + 1)))).2
          (hJ (k + 1) (by omega))⟩
  obtain ⟨J, hJ⟩ := hcontract
  have hc₂ : 0 ≤ R.c₂ := R.c₁_pos.le.trans R.c₁_lt_c₂.le
  have hgeom : ∀ k : ℕ, |R.g (J + k)| ≤ R.c₂ ^ k * |R.g J| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        |R.g (J + (k + 1))| = |R.g ((J + k) + 1)| := by rw [Nat.add_assoc]
        _ ≤ R.c₂ * |R.g (J + k)| := hJ (J + k) (Nat.le_add_right J k)
        _ ≤ R.c₂ * (R.c₂ ^ k * |R.g J|) := mul_le_mul_of_nonneg_left ih hc₂
        _ = R.c₂ ^ (k + 1) * |R.g J| := by rw [pow_succ]; ring
  have hgeomlim : Tendsto (fun k : ℕ => R.c₂ ^ k * |R.g J|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc₂ R.c₂_lt_one).mul_const |R.g J|
  have hzero : Tendsto (fun k => |R.g (J + k)|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hgeom hgeomlim
  have hz : m ≤ 0 := ge_of_tendsto (x := (atTop : Filter ℕ)) hzero (Eventually.of_forall (fun k => hg (J + k)))
  linarith

/-- Scalar Armijo--weak-Wolfe convergence to the minimum value, independently
of every metric update rule. -/
theorem values_tendsto_min (hK : IsCompact R.initialSublevel)
    (xStar : ℝ) (hmin : ∀ x, f xStar ≤ f x) :
    Tendsto (fun k => f (R.x k)) atTop (𝓝 (f xStar)) := by
  have hb : BddBelow (Set.range (fun k => f (R.x k))) := by
    refine ⟨f xStar, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hmin (R.x k)
  let ℓ := ⨅ k, f (R.x k)
  have hlim : Tendsto (fun k => f (R.x k)) atTop (𝓝 ℓ) :=
    tendsto_atTop_ciInf R.objective_antitone hb
  have hminlim : f xStar ≤ ℓ := ge_of_tendsto (x := (atTop : Filter ℕ)) hlim
    (Eventually.of_forall (fun k => hmin (R.x k)))
  have heq : ℓ = f xStar := by
    apply le_antisymm _ hminlim
    by_contra hn
    have hL : 0 < ℓ - f xStar := sub_pos.mpr (lt_of_not_ge hn)
    exact R.no_uniform_positive_gap hK xStar hmin (ℓ - f xStar) hL
      (fun k => sub_le_sub_right (ciInf_le hb k) (f xStar))
  simpa only [heq] using hlim

/-- Source G's scalar convergence proposition. Uniqueness lifts the proved
value convergence to convergence of every accepted iterate. -/
theorem convergence (hK : IsCompact R.initialSublevel)
    (xStar : ℝ) (hmin : ∀ x, f xStar ≤ f x)
    (hunique : ∀ x, f x = f xStar → x = xStar) :
    Tendsto (fun k => f (R.x k)) atTop (𝓝 (f xStar)) ∧
      Tendsto R.x atTop (𝓝 xStar) := by
  have hv := R.values_tendsto_min hK xStar hmin
  exact ⟨hv, Localization.tendsto_unique_minimizer_of_values R.convex xStar hmin hunique hv⟩

end ScalarMetricRun
namespace OneDimensional

/-- The exact scalar-to-coordinate identification in dimension one. -/
def embed : ℝ →L[ℝ] Vec 1 := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ ℝ)

@[simp] theorem embed_apply (t : ℝ) (i : Fin 1) : embed t i = t := rfl

@[simp] theorem embed_eval (v : Vec 1) : embed (v 0) = v := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simp only [embed_apply, hi]

/-- The objective in scalar coordinates. -/
def objective (F : Vec 1 → ℝ) (t : ℝ) : ℝ := F (embed t)

end OneDimensional

namespace AdmissibleBFGSRun

variable {F : Vec 1 → ℝ} (R : AdmissibleBFGSRun 1 F)

/-- Forgetting the BFGS update gives exactly the scalar positive-metric run.
Positive definiteness is used only to prove positivity of its sole metric entry. -/
def toScalarMetricRun : ScalarMetricRun (OneDimensional.objective F) where
  convex := by
    simpa only [Set.preimage_univ, Function.comp_def, OneDimensional.objective] using
      R.convex.comp_linearMap OneDimensional.embed.toLinearMap
  x := fun k => R.x k 0
  g := fun k => R.g k 0
  metric := fun k => R.H k 0 0
  α := R.α
  c₁ := R.c₁
  c₂ := R.c₂
  c₁_pos := R.c₁_pos
  c₁_lt_c₂ := R.c₁_lt_c₂
  c₂_lt_one := R.c₂_lt_one
  metric_pos := by
    intro k
    have hne : (fun _ : Fin 1 => (1 : ℝ)) ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      norm_num at h0
    have h := metricEnergy_pos (R.positive_definite k) hne
    simpa [metricEnergy, dot, Matrix.mulVec, dotProduct] using h
  alpha_pos := R.alpha_pos
  gradient_ne := by
    intro k hk
    apply R.gradient_nonzero k
    rw [← OneDimensional.embed_eval (R.g k), hk]
    rfl
  hasDeriv := by
    intro k
    have hemb : HasDerivAt OneDimensional.embed (OneDimensional.embed 1) (R.x k 0) :=
      OneDimensional.embed.hasFDerivAt.hasDerivAt
    have h := (R.hasGradient k).comp_hasDerivAt_of_eq (R.x k 0) hemb
      (OneDimensional.embed_eval (R.x k)).symm
    simpa [OneDimensional.objective, gradientFunctional_apply, dot] using h
  step := by
    intro k
    have h := congrArg (fun v : Vec 1 => v 0) (R.step k)
    simpa [bfgsStep, Matrix.mulVec, dotProduct, sub_eq_add_neg, mul_assoc] using h
  armijo := by
    intro k
    have h := R.armijo k
    have hs : R.x (k + 1) 0 - R.x k 0 = (bfgsStep (R.H k) (R.g k) (R.α k)) 0 := by
      rw [R.step]
      simp
    rw [hs]
    simpa [OneDimensional.objective, dot, mul_assoc] using h
  weak_wolfe := by
    intro k
    have h := R.weak_wolfe k
    have hs : R.x (k + 1) 0 - R.x k 0 = (bfgsStep (R.H k) (R.g k) (R.α k)) 0 := by
      rw [R.step]
      simp
    rw [hs]
    simpa [dot, mul_assoc] using h

/-- Scalar coordinates carry exactly the same initial sublevel. -/
theorem scalar_initialSublevel_compact (hK : IsCompact R.initialSublevel) :
    IsCompact R.toScalarMetricRun.initialSublevel := by
  have heq : (fun v : Vec 1 => v 0) '' R.initialSublevel = R.toScalarMetricRun.initialSublevel := by
    ext t
    constructor
    · rintro ⟨v, hv, rfl⟩
      change F (OneDimensional.embed (v 0)) ≤ F (OneDimensional.embed (R.x 0 0))
      simpa only [OneDimensional.embed_eval] using hv
    · intro ht
      refine ⟨OneDimensional.embed t, ?_, rfl⟩
      change F (OneDimensional.embed t) ≤ F (R.x 0)
      change F (OneDimensional.embed t) ≤ F (OneDimensional.embed (R.x 0 0)) at ht
      simpa only [OneDimensional.embed_eval] using ht
  rw [← heq]
  exact hK.image (continuous_apply 0)

/-- Actual one-dimensional full BFGS is a specialization of the update-free
scalar convergence theorem, with its exact original objective and iterates. -/
theorem scalar_convergence (hK : IsCompact R.initialSublevel) (xStar : Vec 1)
    (hmin : ∀ x, F xStar ≤ F x)
    (hunique : ∀ x, F x = F xStar → x = xStar) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xStar)) ∧
      Tendsto R.x atTop (𝓝 xStar) := by
  have hmin' : ∀ t, OneDimensional.objective F (xStar 0) ≤ OneDimensional.objective F t := by
    intro t
    simpa only [OneDimensional.objective, OneDimensional.embed_eval] using hmin (OneDimensional.embed t)
  have huniq' : ∀ t, OneDimensional.objective F t = OneDimensional.objective F (xStar 0) → t = xStar 0 := by
    intro t ht
    have heq : OneDimensional.embed t = xStar := hunique _
      (by simpa only [OneDimensional.objective, OneDimensional.embed_eval] using ht)
    exact congrArg (fun v : Vec 1 => v 0) heq
  have h := R.toScalarMetricRun.convergence (R.scalar_initialSublevel_compact hK)
    (xStar 0) hmin' huniq'
  have hval : Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xStar)) := by
    simpa only [OneDimensional.objective, toScalarMetricRun, OneDimensional.embed_eval] using h.1
  exact ⟨hval, R.iterates_tendsto_unique_min_of_values xStar hmin hunique hval⟩

end AdmissibleBFGSRun
end BfgsVerification
