import BfgsVerification.PolynomialRootSigns
import Mathlib.Topology.Algebra.Order.Field

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem polynomial_logDerivative_identity (p : Polynomial ℝ) (a x : ℝ) :
    (x-a) * p.derivative.eval x =
      (p.rootMultiplicity a : ℝ) * p.eval x +
        (x-a) ^ (p.rootMultiplicity a + 1) * (rootFactor p a).derivative.eval x := by
  have hd := congrArg (fun r : Polynomial ℝ => r.derivative.eval x)
    (p.pow_mul_divByMonic_rootMultiplicity_eq a)
  simp only [derivative_mul, derivative_X_sub_C_pow, eval_add, eval_mul, eval_C,
    eval_pow, eval_sub, eval_X] at hd
  change (p.rootMultiplicity a : ℝ) * (x-a) ^ (p.rootMultiplicity a - 1) *
    (rootFactor p a).eval x + (x-a)^p.rootMultiplicity a *
      (rootFactor p a).derivative.eval x = p.derivative.eval x at hd
  rw [← hd, rootFactor_eval_factorization p a x]
  cases hm : p.rootMultiplicity a with
  | zero => simp [hm]
  | succ m => simp only [hm, Nat.succ_sub_one, pow_succ]; ring

theorem polynomial_normalized_logDerivative_eq (p : Polynomial ℝ) (a x : ℝ)
    (hx : x ≠ a) (hr : (rootFactor p a).eval x ≠ 0) :
    (x-a) * p.derivative.eval x / p.eval x =
      (p.rootMultiplicity a : ℝ) +
        (x-a) * (rootFactor p a).derivative.eval x / (rootFactor p a).eval x := by
  have hz : x-a ≠ 0 := sub_ne_zero.mpr hx
  have he : p.eval x ≠ 0 := by
    rw [rootFactor_eval_factorization p a x]
    exact mul_ne_zero (pow_ne_zero _ hz) hr
  apply (div_eq_iff he).mpr
  rw [polynomial_logDerivative_identity p a x, rootFactor_eval_factorization p a x]
  field_simp
  ring

theorem polynomial_normalized_logDerivative_tendsto {p : Polynomial ℝ}
    (hp : p ≠ 0) (a : ℝ) :
    Tendsto (fun x => (x-a) * p.derivative.eval x / p.eval x)
      (𝓝[≠] a) (𝓝 (p.rootMultiplicity a : ℝ)) := by
  have hr : (rootFactor p a).eval a ≠ 0 := rootFactor_eval_ne_zero hp a
  have hcont : ContinuousAt (fun x => (p.rootMultiplicity a : ℝ) +
      (x-a) * (rootFactor p a).derivative.eval x / (rootFactor p a).eval x) a := by
    exact continuousAt_const.add
      (((continuousAt_id.sub continuousAt_const).mul
        (rootFactor p a).derivative.continuousAt).div (rootFactor p a).continuousAt hr)
  have hlim : Tendsto (fun x => (p.rootMultiplicity a : ℝ) +
      (x-a) * (rootFactor p a).derivative.eval x / (rootFactor p a).eval x)
      (𝓝[≠] a) (𝓝 (p.rootMultiplicity a : ℝ)) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  have hn := (rootFactor p a).continuousAt.eventually_ne hr
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hrx hx
  exact (polynomial_normalized_logDerivative_eq p a x hx hrx).symm

theorem weighted_normalized_logDerivative_tendsto {p : Polynomial ℝ}
    (hp : p ≠ 0) (q : Polynomial ℝ) (a : ℝ) :
    Tendsto (fun x => (x-a) * (q.eval x * p.derivative.eval x / p.eval x))
      (𝓝[≠] a) (𝓝 ((p.rootMultiplicity a : ℝ) * q.eval a)) := by
  have h := (polynomial_normalized_logDerivative_tendsto hp a).mul
    (q.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  convert h using 1
  ext x
  ring

end RealAlgebraicGeometry
end BfgsVerification
