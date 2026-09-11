import BfgsVerification.UnivariateSignCells

/-! The existing genuine polynomial Boolean syntax restricted to the real line,
with an explicitly constructed finite root boundary. -/
noncomputable section
open Set Polynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- Substitute the one real coordinate into an actual univariate polynomial. -/
def toUnivariate (p : MvPolynomial Unit ℝ) : Polynomial ℝ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun _ : Unit => Polynomial.X) p

theorem toUnivariate_eval (p : MvPolynomial Unit ℝ) (t : ℝ) :
    (toUnivariate p).eval t = MvPolynomial.eval (fun _ : Unit => t) p := by
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℝ := by
    ext r
    simp
  change (Polynomial.evalRingHom t)
    (MvPolynomial.eval₂Hom Polynomial.C (fun _ : Unit => Polynomial.X) p) =
      MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun _ : Unit => t) p
  rw [MvPolynomial.map_eval₂Hom,hc]
  have hX : (fun _ : Unit => (Polynomial.evalRingHom t) Polynomial.X) = (fun _ : Unit => t) := by
    funext i
    exact Polynomial.eval_X
  rw [hX]

/-- The finite family of actual univariate polynomials appearing in the formula. -/
def PolynomialFormula.univariatePolynomials : PolynomialFormula Unit → Finset (Polynomial ℝ)
  | .equalZero p => {toUnivariate p}
  | .positive p => {toUnivariate p}
  | .and f g => f.univariatePolynomials ∪ g.univariatePolynomials
  | .not f => f.univariatePolynomials

theorem PolynomialFormula.holds_constant_on_profile (f : PolynomialFormula Unit)
    {P : Finset (Polynomial ℝ)} (hP : f.univariatePolynomials ⊆ P) {x y : ℝ}
    (hx : x ∉ rootBoundary P) (hy : y ∉ rootBoundary P)
    (hprofile : cutProfile (rootBoundary P) x = cutProfile (rootBoundary P) y) :
    f.Holds (fun _ => x) ↔ f.Holds (fun _ => y) := by
  induction f with
  | equalZero p =>
    have hp : toUnivariate p ∈ P := hP (Finset.mem_singleton_self _)
    simpa only [Holds,toUnivariate_eval] using
      (polynomial_sign_constant_on_profile hp hx hy hprofile).1
  | positive p =>
    have hp : toUnivariate p ∈ P := hP (Finset.mem_singleton_self _)
    simpa only [Holds,toUnivariate_eval] using
      (polynomial_sign_constant_on_profile hp hx hy hprofile).2
  | and f g hf hg =>
    apply and_congr
    · exact hf (fun p hp => hP (Finset.mem_union_left _ hp))
    · exact hg (fun p hp => hP (Finset.mem_union_right _ hp))
  | not f hf => exact not_congr (hf hP)

/-- An actual finite boundary for any one-dimensional Boolean polynomial set. -/
theorem PolynomialFormula.exists_finite_sign_boundary (f : PolynomialFormula Unit) :
    ∃ B : Finset ℝ, ∀ x y : ℝ, x ∉ B → y ∉ B → cutProfile B x = cutProfile B y →
      (f.Holds (fun _ => x) ↔ f.Holds (fun _ => y)) := by
  refine ⟨rootBoundary f.univariatePolynomials,fun x y hx hy hp => ?_⟩
  exact f.holds_constant_on_profile (Finset.Subset.refl _) hx hy hp

end RealAlgebraicGeometry
end BfgsVerification
