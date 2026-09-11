import BfgsVerification.PolynomialLogDerivative

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem inverse_sub_tendsto_right (a : ℝ) :
    Tendsto (fun x : ℝ => (x-a)⁻¹) (𝓝[>] a) atTop := by
  apply tendsto_inv_nhdsGT_zero.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa using (continuousAt_id.sub continuousAt_const :
      ContinuousAt (fun x : ℝ => x-a) a).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x-a
    exact sub_pos.mpr hx

theorem inverse_sub_tendsto_left (a : ℝ) :
    Tendsto (fun x : ℝ => (x-a)⁻¹) (𝓝[<] a) atBot := by
  apply tendsto_inv_zero_atBot.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa using (continuousAt_id.sub continuousAt_const :
      ContinuousAt (fun x : ℝ => x-a) a).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change x-a < 0
    exact sub_neg.mpr hx

theorem normalized_pole_pos {f : ℝ → ℝ} {a c : ℝ} (hc : 0<c)
    (h : Tendsto (fun x => (x-a)*f x) (𝓝[≠] a) (𝓝 c)) :
    Tendsto f (𝓝[>] a) atTop ∧ Tendsto f (𝓝[<] a) atBot := by
  have hr : Tendsto (fun x => (x-a)*f x) (𝓝[>] a) (𝓝 c) :=
    h.mono_left (nhdsWithin_mono a (by intro x hx; exact ne_of_gt hx))
  have hl : Tendsto (fun x => (x-a)*f x) (𝓝[<] a) (𝓝 c) :=
    h.mono_left (nhdsWithin_mono a (by intro x hx; exact ne_of_lt hx))
  constructor
  · apply (hr.pos_mul_atTop hc (inverse_sub_tendsto_right a)).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hn : x-a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx)
    field_simp
  · apply ((inverse_sub_tendsto_left a).atBot_mul_pos hc hl).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hn : x-a ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx)
    field_simp

theorem normalized_pole_neg {f : ℝ → ℝ} {a c : ℝ} (hc : c<0)
    (h : Tendsto (fun x => (x-a)*f x) (𝓝[≠] a) (𝓝 c)) :
    Tendsto f (𝓝[>] a) atBot ∧ Tendsto f (𝓝[<] a) atTop := by
  have hr : Tendsto (fun x => (x-a)*f x) (𝓝[>] a) (𝓝 c) :=
    h.mono_left (nhdsWithin_mono a (by intro x hx; exact ne_of_gt hx))
  have hl : Tendsto (fun x => (x-a)*f x) (𝓝[<] a) (𝓝 c) :=
    h.mono_left (nhdsWithin_mono a (by intro x hx; exact ne_of_lt hx))
  constructor
  · apply (hr.neg_mul_atTop hc (inverse_sub_tendsto_right a)).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hn : x-a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx)
    field_simp
  · apply ((inverse_sub_tendsto_left a).atBot_mul_neg hc hl).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hn : x-a ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx)
    field_simp

theorem weighted_logDerivative_positive_pole {p q : Polynomial ℝ} {a : ℝ}
    (hp : p ≠ 0) (ha : p.IsRoot a) (hq : 0 < q.eval a) :
    Tendsto (fun x => q.eval x * p.derivative.eval x / p.eval x) (𝓝[>] a) atTop ∧
    Tendsto (fun x => q.eval x * p.derivative.eval x / p.eval x) (𝓝[<] a) atBot := by
  have hm : (0 : ℝ) < p.rootMultiplicity a := by
    exact_mod_cast (Polynomial.rootMultiplicity_pos hp).mpr ha
  exact normalized_pole_pos (mul_pos hm hq)
    (weighted_normalized_logDerivative_tendsto hp q a)

theorem weighted_logDerivative_negative_pole {p q : Polynomial ℝ} {a : ℝ}
    (hp : p ≠ 0) (ha : p.IsRoot a) (hq : q.eval a < 0) :
    Tendsto (fun x => q.eval x * p.derivative.eval x / p.eval x) (𝓝[>] a) atBot ∧
    Tendsto (fun x => q.eval x * p.derivative.eval x / p.eval x) (𝓝[<] a) atTop := by
  have hm : (0 : ℝ) < p.rootMultiplicity a := by
    exact_mod_cast (Polynomial.rootMultiplicity_pos hp).mpr ha
  exact normalized_pole_neg (mul_neg_of_pos_of_neg hm hq)
    (weighted_normalized_logDerivative_tendsto hp q a)

end RealAlgebraicGeometry
end BfgsVerification
