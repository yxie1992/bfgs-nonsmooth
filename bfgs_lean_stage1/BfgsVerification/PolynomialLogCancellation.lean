import BfgsVerification.PolynomialLogPoles

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem weighted_logDerivative_finite_of_weight_root {p q : Polynomial ℝ} {a : ℝ}
    (hp : p ≠ 0) (hq : q.IsRoot a) :
    Tendsto (fun x => q.eval x * p.derivative.eval x / p.eval x) (𝓝[≠] a)
      (𝓝 ((p.rootMultiplicity a : ℝ) * (q /ₘ (X-C a)).eval a)) := by
  have hfact : (X-C a) * (q /ₘ (X-C a)) = q :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hq
  have h := (polynomial_normalized_logDerivative_tendsto hp a).mul
    ((q /ₘ (X-C a)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  apply h.congr'
  filter_upwards [] with x
  have he := congrArg (Polynomial.eval x) hfact
  simp only [eval_mul, eval_sub, eval_X, eval_C] at he
  rw [← he]
  ring

/-- The signed infinite jump of an actual real function at a point. -/
def localCauchyIndex (f : ℝ → ℝ) (a : ℝ) : ℤ := by
  classical
  exact if Tendsto f (𝓝[<] a) atBot ∧ Tendsto f (𝓝[>] a) atTop then 1
  else if Tendsto f (𝓝[<] a) atTop ∧ Tendsto f (𝓝[>] a) atBot then -1
  else 0

theorem localCauchyIndex_of_positive_pole {f : ℝ → ℝ} {a : ℝ}
    (hr : Tendsto f (𝓝[>] a) atTop) (hl : Tendsto f (𝓝[<] a) atBot) :
    localCauchyIndex f a = 1 := by
  simp [localCauchyIndex, hr, hl]

theorem localCauchyIndex_of_negative_pole {f : ℝ → ℝ} {a : ℝ}
    (hr : Tendsto f (𝓝[>] a) atBot) (hl : Tendsto f (𝓝[<] a) atTop) :
    localCauchyIndex f a = -1 := by
  have hn : ¬ Tendsto f (𝓝[<] a) atBot := hl.not_tendsto disjoint_atTop_atBot
  simp [localCauchyIndex, hr, hl, hn]

theorem localCauchyIndex_of_finite_left_limit {f : ℝ → ℝ} {a b : ℝ}
    (h : Tendsto f (𝓝[<] a) (𝓝 b)) : localCauchyIndex f a = 0 := by
  have hb : ¬ Tendsto f (𝓝[<] a) atBot :=
    fun hf => not_tendsto_nhds_of_tendsto_atBot hf b h
  have ht : ¬ Tendsto f (𝓝[<] a) atTop :=
    fun hf => not_tendsto_nhds_of_tendsto_atTop hf b h
  simp [localCauchyIndex, hb, ht]

theorem localCauchyIndex_weighted_logDerivative {p q : Polynomial ℝ} {a : ℝ}
    (hp : p ≠ 0) (ha : p.IsRoot a) :
    localCauchyIndex (fun x => q.eval x * p.derivative.eval x / p.eval x) a =
      (SignType.sign (q.eval a) : ℤ) := by
  rcases lt_trichotomy (q.eval a) 0 with hn | hz | hpq
  · have h := weighted_logDerivative_negative_pole hp ha hn
    rw [localCauchyIndex_of_negative_pole h.1 h.2, sign_neg hn]
    rfl
  · have h := weighted_logDerivative_finite_of_weight_root hp hz
    have hl := h.mono_left (nhdsWithin_mono a (by intro x hx; exact ne_of_lt hx))
    rw [localCauchyIndex_of_finite_left_limit hl, hz, sign_zero]
    rfl
  · have h := weighted_logDerivative_positive_pole hp ha hpq
    rw [localCauchyIndex_of_positive_pole h.1 h.2, sign_pos hpq]
    rfl

end RealAlgebraicGeometry
end BfgsVerification
