import BfgsVerification.TarskiLocalIndex

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem polynomial_sign_atTop (p : Polynomial ℝ) :
    ∀ᶠ x in atTop, SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  by_cases hn : p.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hn]
    exact Eventually.of_forall (fun _ => by simp)
  have hd : 0 < p.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hn)
  have hl : p.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_degree_gt hd)
  rcases lt_or_gt_of_ne hl with hlneg | hlpos
  · have h := p.tendsto_atBot_of_leadingCoeff_nonpos hd hlneg.le
    filter_upwards [h.eventually (eventually_lt_atBot (0 : ℝ))] with x hx
    rw [sign_neg hx, sign_neg hlneg]
  · have h := p.tendsto_atTop_of_leadingCoeff_nonneg hd hlpos.le
    filter_upwards [h.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    rw [sign_pos hx, sign_pos hlpos]

theorem polynomial_sign_atBot (p : Polynomial ℝ) :
    ∀ᶠ x in atBot, SignType.sign (p.eval x) =
      (-1 : SignType)^p.natDegree * SignType.sign p.leadingCoeff := by
  have h := tendsto_neg_atBot_atTop.eventually (polynomial_sign_atTop (p.comp (-X)))
  have hl : (p.comp (-X)).leadingCoeff = p.leadingCoeff * (-1)^p.natDegree := by
    rw [Polynomial.leadingCoeff_comp (by simp), leadingCoeff_neg, leadingCoeff_X]
  filter_upwards [h] with x hx
  simp only [eval_comp, eval_neg, eval_X, neg_neg, hl, sign_mul, sign_pow,
    sign_neg (by norm_num : (-1 : ℝ) < 0)] at hx
  simpa only [mul_comm] using hx

end RealAlgebraicGeometry
end BfgsVerification
