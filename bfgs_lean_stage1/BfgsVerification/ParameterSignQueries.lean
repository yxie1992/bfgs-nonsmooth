import BfgsVerification.SemialgebraicIndexQueries
import BfgsVerification.RealSignQuerySampling

/-! Actual finite families of parameter polynomials: query expressions and
the nonzero-factor choice have finite semialgebraic fibers. -/
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {σ : Type*} [Finite σ] {m : ℕ}

theorem finiteSemialgebraic_signQueryExpression
    (p : Polynomial (MvPolynomial σ ℝ))
    (q : Fin m → Polynomial (MvPolynomial σ ℝ)) (ω : Fin m → SignType) :
    FiniteSemialgebraicFunction (fun x : σ → ℝ => signQueryExpression
      (p.map (MvPolynomial.eval x)) (fun i => (q i).map (MvPolynomial.eval x)) ω) := by
  classical
  have h := FiniteSemialgebraicFunction.sum Finset.univ
    (fun (e : Fin m → Fin 3) x => signPatternCoeff ω e *
      (tarskiQuery (p.map (MvPolynomial.eval x))
        ((∏ i, (q i)^(e i).val).map (MvPolynomial.eval x)) : ℚ))
    (fun e _ => (finiteSemialgebraic_tarskiQuery p (∏ i, (q i)^(e i).val)).map
      (fun z : ℤ => signPatternCoeff ω e * (z : ℚ)))
  simpa only [signQueryExpression, signQueryPolynomial, Polynomial.map_prod,
    Polynomial.map_pow] using h

def nonzeroParameterIndices (q : Fin m → Polynomial (MvPolynomial σ ℝ))
    (x : σ → ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => (q i).map (MvPolynomial.eval x) ≠ 0)

theorem finiteSemialgebraic_nonzeroParameterIndices
    (q : Fin m → Polynomial (MvPolynomial σ ℝ)) :
    FiniteSemialgebraicFunction (nonzeroParameterIndices q) := by
  classical
  refine ⟨Set.toFinite _, fun I => ?_⟩
  have h := isSemialgebraic_finset_inter Finset.univ
    (fun i : Fin m => if i ∈ I then
      {x : σ → ℝ | (q i).map (MvPolynomial.eval x) ≠ 0} else
      {x : σ → ℝ | (q i).map (MvPolynomial.eval x) = 0})
    (fun i _ => by
      dsimp only
      split_ifs
      · exact (polynomial_map_zero_semialgebraic (q i)).compl
      · exact polynomial_map_zero_semialgebraic (q i))
  convert h using 1
  ext x
  simp only [mem_setOf_eq, nonzeroParameterIndices, Finset.ext_iff,
    Finset.mem_filter, Finset.mem_univ, true_and, mem_iInter, forall_const]
  apply forall_congr'
  intro i
  by_cases hi : i ∈ I <;> simp [hi]

theorem nonzeroFamilyProduct_specialize (q : Fin m → Polynomial (MvPolynomial σ ℝ))
    (x : σ → ℝ) :
    nonzeroFamilyProduct (fun i => (q i).map (MvPolynomial.eval x)) =
      (∏ i ∈ nonzeroParameterIndices q x, q i).map (MvPolynomial.eval x) := by
  classical
  simp only [nonzeroFamilyProduct, nonzeroParameterIndices, Polynomial.map_prod]

theorem finiteSemialgebraic_product_signQueryExpression
    (q : Fin m → Polynomial (MvPolynomial σ ℝ)) (ω : Fin m → SignType) :
    FiniteSemialgebraicFunction (fun x : σ → ℝ => signQueryExpression
      (nonzeroFamilyProduct (fun i => (q i).map (MvPolynomial.eval x)))
      (fun i => (q i).map (MvPolynomial.eval x)) ω) := by
  have h := (finiteSemialgebraic_nonzeroParameterIndices q).select
    (fun I x => signQueryExpression ((∏ i ∈ I, q i).map (MvPolynomial.eval x))
      (fun i => (q i).map (MvPolynomial.eval x)) ω)
    (fun I => finiteSemialgebraic_signQueryExpression (∏ i ∈ I, q i) q ω)
  simpa only [nonzeroFamilyProduct_specialize] using h

theorem finiteSemialgebraic_derivative_signQueryExpression
    (q : Fin m → Polynomial (MvPolynomial σ ℝ)) (ω : Fin m → SignType) :
    FiniteSemialgebraicFunction (fun x : σ → ℝ => signQueryExpression
      (nonzeroFamilyProduct (fun i => (q i).map (MvPolynomial.eval x))).derivative
      (fun i => (q i).map (MvPolynomial.eval x)) ω) := by
  have h := (finiteSemialgebraic_nonzeroParameterIndices q).select
    (fun I x => signQueryExpression ((∏ i ∈ I, q i).derivative.map (MvPolynomial.eval x))
      (fun i => (q i).map (MvPolynomial.eval x)) ω)
    (fun I => finiteSemialgebraic_signQueryExpression (∏ i ∈ I, q i).derivative q ω)
  simpa only [nonzeroFamilyProduct_specialize, Polynomial.derivative_map] using h

end RealAlgebraicGeometry
end BfgsVerification
