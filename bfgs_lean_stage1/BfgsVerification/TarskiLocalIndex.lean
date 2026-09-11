import BfgsVerification.PolynomialLogCancellation

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- Signed jumps of an actual rational function at the distinct denominator roots. -/
def rationalCauchyIndex (numerator denominator : Polynomial ℝ) : ℤ := by
  classical
  exact ∑ a ∈ denominator.roots.toFinset,
    localCauchyIndex (fun x => numerator.eval x / denominator.eval x) a

/-- The signed query on the actual distinct real roots; multiplicities are not counted. -/
def tarskiQuery (p q : Polynomial ℝ) : ℤ := by
  classical
  exact ∑ a ∈ p.roots.toFinset, (SignType.sign (q.eval a) : ℤ)

theorem tarskiQuery_eq_rationalCauchyIndex {p : Polynomial ℝ} (hp : p ≠ 0)
    (q : Polynomial ℝ) :
    tarskiQuery p q = rationalCauchyIndex (q * p.derivative) p := by
  classical
  unfold tarskiQuery rationalCauchyIndex
  apply Finset.sum_congr rfl
  intro a ha
  have hroot : p.IsRoot a := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp ha)
  simpa only [eval_mul] using (localCauchyIndex_weighted_logDerivative hp hroot (q := q)).symm

theorem sign_cast_eq_indicators (r : ℝ) :
    (SignType.sign r : ℤ) = (if 0<r then 1 else 0) - (if r<0 then 1 else 0) := by
  rcases lt_trichotomy r 0 with hn | hz | hp
  · simp [sign_neg hn, hn, not_lt_of_ge hn.le]
  · simp [hz]
  · simp [sign_pos hp, hp, not_lt_of_ge hp.le]

theorem tarskiQuery_eq_positive_card_sub_negative_card (p q : Polynomial ℝ) :
    tarskiQuery p q =
      ((p.roots.toFinset.filter (fun a => 0 < q.eval a)).card : ℤ) -
      ((p.roots.toFinset.filter (fun a => q.eval a < 0)).card : ℤ) := by
  classical
  unfold tarskiQuery
  simp_rw [sign_cast_eq_indicators]
  rw [Finset.sum_sub_distrib]
  simp

theorem tarskiQuery_one (p : Polynomial ℝ) :
    tarskiQuery p 1 = (p.roots.toFinset.card : ℤ) := by
  classical
  simp [tarskiQuery]

theorem tarskiQuery_zero (p : Polynomial ℝ) : tarskiQuery p 0 = 0 := by
  classical
  simp [tarskiQuery]

end RealAlgebraicGeometry
end BfgsVerification
