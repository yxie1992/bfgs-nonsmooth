import BfgsVerification.TarskiLocalIndex

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem rational_eval_of_order_le (p q : Polynomial ℝ) (a x : ℝ)
    (horder : q.rootMultiplicity a ≤ p.rootMultiplicity a)
    (hx : x ≠ a) (hq : (rootFactor q a).eval x ≠ 0) :
    p.eval x / q.eval x =
      (x-a) ^ (p.rootMultiplicity a - q.rootMultiplicity a) *
        ((rootFactor p a).eval x / (rootFactor q a).eval x) := by
  have hz : x-a ≠ 0 := sub_ne_zero.mpr hx
  have he : p.rootMultiplicity a =
      (p.rootMultiplicity a - q.rootMultiplicity a) + q.rootMultiplicity a :=
    (Nat.sub_add_cancel horder).symm
  rw [rootFactor_eval_factorization p a x, rootFactor_eval_factorization q a x,
    he, pow_add]
  field_simp
  ring

theorem normalized_rational_eval_of_order_le (p q : Polynomial ℝ) (a x : ℝ)
    (horder : p.rootMultiplicity a ≤ q.rootMultiplicity a)
    (hx : x ≠ a) (hq : (rootFactor q a).eval x ≠ 0) :
    (x-a) ^ (q.rootMultiplicity a - p.rootMultiplicity a) * (p.eval x / q.eval x) =
      (rootFactor p a).eval x / (rootFactor q a).eval x := by
  have hz : x-a ≠ 0 := sub_ne_zero.mpr hx
  have he : q.rootMultiplicity a =
      (q.rootMultiplicity a - p.rootMultiplicity a) + p.rootMultiplicity a :=
    (Nat.sub_add_cancel horder).symm
  rw [rootFactor_eval_factorization p a x, rootFactor_eval_factorization q a x,
    he, pow_add]
  field_simp
  ring

theorem rational_finite_limit_of_order_le (p : Polynomial ℝ) {q : Polynomial ℝ}
    (hq : q ≠ 0) (a : ℝ) (horder : q.rootMultiplicity a ≤ p.rootMultiplicity a) :
    Tendsto (fun x => p.eval x / q.eval x) (𝓝[≠] a)
      (𝓝 ((0 : ℝ) ^ (p.rootMultiplicity a - q.rootMultiplicity a) *
        ((rootFactor p a).eval a / (rootFactor q a).eval a))) := by
  have hn := rootFactor_eval_ne_zero hq a
  have hc : ContinuousAt (fun x =>
      (x-a) ^ (p.rootMultiplicity a - q.rootMultiplicity a) *
        ((rootFactor p a).eval x / (rootFactor q a).eval x)) a :=
    ((continuousAt_id.sub continuousAt_const).pow _).mul
      ((rootFactor p a).continuousAt.div (rootFactor q a).continuousAt hn)
  have hlim := hc.tendsto.mono_left (show 𝓝[≠] a ≤ 𝓝 a from nhdsWithin_le_nhds)
  simp only [sub_self] at hlim
  apply hlim.congr'
  have hev := (rootFactor q a).continuousAt.eventually_ne hn
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hqx hx
  exact (rational_eval_of_order_le p q a x horder hx hqx).symm

theorem normalized_rational_limit_of_order_le (p : Polynomial ℝ) {q : Polynomial ℝ}
    (hq : q ≠ 0) (a : ℝ) (horder : p.rootMultiplicity a ≤ q.rootMultiplicity a) :
    Tendsto (fun x => (x-a) ^ (q.rootMultiplicity a - p.rootMultiplicity a) *
      (p.eval x / q.eval x)) (𝓝[≠] a)
      (𝓝 ((rootFactor p a).eval a / (rootFactor q a).eval a)) := by
  have hn := rootFactor_eval_ne_zero hq a
  have hc := (rootFactor p a).continuousAt.div (rootFactor q a).continuousAt hn
  apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
  have hev := (rootFactor q a).continuousAt.eventually_ne hn
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hqx hx
  exact (normalized_rational_eval_of_order_le p q a x horder hx hqx).symm

theorem localCauchyIndex_zero_of_order_le (p : Polynomial ℝ) {q : Polynomial ℝ}
    (hq : q ≠ 0) (a : ℝ) (horder : q.rootMultiplicity a ≤ p.rootMultiplicity a) :
    localCauchyIndex (fun x => p.eval x / q.eval x) a = 0 := by
  apply localCauchyIndex_of_finite_left_limit
  exact (rational_finite_limit_of_order_le p hq a horder).mono_left
    (nhdsWithin_mono a (by intro x hx; exact ne_of_lt hx))

end RealAlgebraicGeometry
end BfgsVerification
