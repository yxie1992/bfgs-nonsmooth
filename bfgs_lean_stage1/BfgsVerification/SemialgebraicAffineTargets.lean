import BfgsVerification.SemialgebraicAffineBooleanProjection

/-! Exact contracts for proved one-coordinate affine projection. These are
real algebraic infrastructure, not general nonlinear projection or Module A's
still unproved semialgebraic finite-value conclusion. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
open RealAlgebraicGeometry

def MixedAffineEliminationTarget : Prop := ∀ {m : ℕ}
    (s : Fin m → Bool) (a b : Fin m → ℝ),
    (∃ t : ℝ, ∀ i, markedLE (s i) (a i*t) (b i)) ↔
      (∀ i, a i = 0 → markedLE (s i) 0 (b i)) ∧
      ∀ i j, a i < 0 → 0 < a j → markedLE (s i || s j) (b j*a i) (b i*a j)

theorem mixedAffineElimination : MixedAffineEliminationTarget := by
  intro m s a b
  exact exists_marked_affine_iff s a b

def PolynomialCoefficientProjectionTarget : Prop := ∀ {n m : ℕ}
    (s : Fin m → Bool) (a b : Fin m → MvPolynomial (Fin n) ℝ),
    IsSemialgebraic {x : Fin n → ℝ | ∃ t : ℝ,
      ∀ i, markedLE (s i) (MvPolynomial.eval x (a i)*t) (MvPolynomial.eval x (b i))}

theorem polynomialCoefficientProjection : PolynomialCoefficientProjectionTarget := by
  intro n m s a b
  exact marked_linear_projection_semialgebraic s a b

def AffineBooleanProjectionTarget : Prop := ∀ {n : ℕ}
    (f : AffineBooleanFormula (Fin n)),
    IsSemialgebraic (coordinateProjection
      {v : (Fin n ⊕ Unit) → ℝ | f.toPolynomialFormula.Holds v})

theorem affineBooleanProjection : AffineBooleanProjectionTarget := by
  intro n f
  exact affine_boolean_coordinate_projection f

end BfgsVerification
