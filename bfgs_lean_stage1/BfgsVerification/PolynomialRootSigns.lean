import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Algebra.Polynomial

noncomputable section

open Filter Set Polynomial
open scoped Topology

namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- The remaining polynomial after removing the complete power of the root. -/
def rootFactor (p : Polynomial ℝ) (a : ℝ) : Polynomial ℝ :=
  p /ₘ (X - C a) ^ p.rootMultiplicity a

theorem rootFactor_eval_factorization (p : Polynomial ℝ) (a x : ℝ) :
    p.eval x = (x - a) ^ p.rootMultiplicity a * (rootFactor p a).eval x := by
  have h := congrArg (Polynomial.eval x) (p.pow_mul_divByMonic_rootMultiplicity_eq a)
  simpa [rootFactor] using h.symm

theorem rootFactor_eval_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) (a : ℝ) :
    (rootFactor p a).eval a ≠ 0 :=
  Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hp

theorem continuous_eventually_sign_eq {f : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousAt f a) (hne : f a ≠ 0) :
    ∀ᶠ x in 𝓝 a, SignType.sign (f x) = SignType.sign (f a) := by
  rcases lt_or_gt_of_ne hne with hn | hp
  · have h := hf.eventually (gt_mem_nhds hn)
    filter_upwards [h] with x hx
    rw [sign_neg hx, sign_neg hn]
  · have h := hf.eventually (lt_mem_nhds hp)
    filter_upwards [h] with x hx
    rw [sign_pos hx, sign_pos hp]

theorem polynomial_eventually_sign_eq {p : Polynomial ℝ} {a : ℝ}
    (hne : p.eval a ≠ 0) :
    ∀ᶠ x in 𝓝 a, SignType.sign (p.eval x) = SignType.sign (p.eval a) :=
  continuous_eventually_sign_eq p.continuous.continuousAt hne

theorem polynomial_sign_right_of_rootMultiplicity {p : Polynomial ℝ}
    (hp : p ≠ 0) (a : ℝ) :
    ∀ᶠ x in 𝓝[>] a,
      SignType.sign (p.eval x) = SignType.sign ((rootFactor p a).eval a) := by
  have hf := polynomial_eventually_sign_eq (rootFactor_eval_ne_zero hp a)
  filter_upwards [hf.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxa
  rw [rootFactor_eval_factorization p a x, sign_mul, sign_pow,
    sign_pos (sub_pos.mpr hxa), one_pow, one_mul, hx]

theorem polynomial_sign_left_of_rootMultiplicity {p : Polynomial ℝ}
    (hp : p ≠ 0) (a : ℝ) :
    ∀ᶠ x in 𝓝[<] a,
      SignType.sign (p.eval x) =
        (-1 : SignType) ^ p.rootMultiplicity a *
          SignType.sign ((rootFactor p a).eval a) := by
  have hf := polynomial_eventually_sign_eq (rootFactor_eval_ne_zero hp a)
  filter_upwards [hf.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxa
  rw [rootFactor_eval_factorization p a x, sign_mul, sign_pow,
    sign_neg (sub_neg.mpr hxa), hx]

end RealAlgebraicGeometry
end BfgsVerification
