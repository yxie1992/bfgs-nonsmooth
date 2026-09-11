import BfgsVerification.PowerPoleIndex

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem sign_div_eq_sign_mul (x y : ℝ) :
    SignType.sign (x/y) = SignType.sign (x*y) := by
  rw [sign_mul]
  exact map_div₀ signHom x y

theorem localCauchyIndex_rational_order {p q : Polynomial ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) (a : ℝ) :
    localCauchyIndex (fun x => p.eval x / q.eval x) a =
      if p.rootMultiplicity a < q.rootMultiplicity a ∧
          Odd (q.rootMultiplicity a-p.rootMultiplicity a) then
        (SignType.sign ((rootFactor p a).eval a * (rootFactor q a).eval a) : ℤ)
      else 0 := by
  by_cases horder : p.rootMultiplicity a < q.rootMultiplicity a
  · have hn : (rootFactor p a).eval a / (rootFactor q a).eval a ≠ 0 :=
      div_ne_zero (rootFactor_eval_ne_zero hp a) (rootFactor_eval_ne_zero hq a)
    rw [localCauchyIndex_normalized_power (Nat.sub_ne_zero_of_lt horder) hn
      (normalized_rational_limit_of_order_le p hq a horder.le), sign_div_eq_sign_mul]
    simp only [horder, true_and]
  · rw [localCauchyIndex_zero_of_order_le p hq a (Nat.le_of_not_gt horder)]
    simp only [horder, false_and, ↓reduceIte]

theorem odd_sub_iff_odd_add {m n : ℕ} (h : m ≤ n) : Odd (n-m) ↔ Odd (n+m) := by
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

theorem localCauchyIndex_rational_reciprocity {p q : Polynomial ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) (a : ℝ) :
    localCauchyIndex (fun x => p.eval x / q.eval x) a +
      localCauchyIndex (fun x => q.eval x / p.eval x) a =
        if Odd (p.rootMultiplicity a + q.rootMultiplicity a) then
          (SignType.sign ((rootFactor p a).eval a * (rootFactor q a).eval a) : ℤ)
        else 0 := by
  rw [localCauchyIndex_rational_order hp hq, localCauchyIndex_rational_order hq hp]
  have hc : (rootFactor q a).eval a * (rootFactor p a).eval a =
      (rootFactor p a).eval a * (rootFactor q a).eval a := mul_comm _ _
  rw [hc]
  rcases lt_trichotomy (p.rootMultiplicity a) (q.rootMultiplicity a) with hlt | heq | hgt
  · rw [if_neg (by omega : ¬ (q.rootMultiplicity a < p.rootMultiplicity a ∧
        Odd (p.rootMultiplicity a-q.rootMultiplicity a))), add_zero]
    simp only [hlt, true_and, odd_sub_iff_odd_add hlt.le, Nat.add_comm]
  · have hn : ¬ Odd (q.rootMultiplicity a + q.rootMultiplicity a) :=
      Nat.not_odd_iff_even.mpr ⟨q.rootMultiplicity a, rfl⟩
    simp [heq, hn]
  · rw [if_neg (by omega : ¬ (p.rootMultiplicity a < q.rootMultiplicity a ∧
        Odd (q.rootMultiplicity a-p.rootMultiplicity a))), zero_add]
    simp only [hgt, true_and, odd_sub_iff_odd_add hgt.le]

end RealAlgebraicGeometry
end BfgsVerification
