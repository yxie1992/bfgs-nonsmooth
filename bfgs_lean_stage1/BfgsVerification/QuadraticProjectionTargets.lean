import BfgsVerification.QuadraticCoordinateProjection
import BfgsVerification.QuadraticDegreeProjection

/-! Exact global degree-two projection contracts. Boolean conjunctions of
multiple quadratic atoms and arbitrary-degree projection remain separate. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
open RealAlgebraicGeometry

def RealQuadraticEliminationTarget : Prop := ∀ a b c : ℝ,
    ((∃ t : ℝ, quadraticValue a b c t=0) ↔
      (a=0 ∧ (b≠0 ∨ c=0)) ∨ (a≠0 ∧ 0≤b^2-4*a*c)) ∧
    ((∃ t : ℝ, 0<quadraticValue a b c t) ↔
      0<a ∨ (a=0 ∧ (b≠0 ∨ 0<c)) ∨ (a<0 ∧ 0<b^2-4*a*c)) ∧
    ((∃ t : ℝ, 0≤quadraticValue a b c t) ↔
      0<a ∨ (a=0 ∧ (b≠0 ∨ 0≤c)) ∨ (a<0 ∧ 0≤b^2-4*a*c))

theorem realQuadraticElimination : RealQuadraticEliminationTarget := fun a b c =>
  ⟨exists_quadratic_zero_iff a b c,exists_quadratic_positive_iff a b c,
    exists_quadratic_nonnegative_iff a b c⟩

def QuadraticPolynomialProjectionTarget : Prop := ∀ {n : ℕ}
    (a b c : MvPolynomial (Fin n) ℝ),
    IsSemialgebraic (coordinateProjection {v : (Fin n ⊕ Unit) → ℝ |
      MvPolynomial.eval v (quadraticPolynomial a b c)=0}) ∧
    IsSemialgebraic (coordinateProjection {v : (Fin n ⊕ Unit) → ℝ |
      0<MvPolynomial.eval v (quadraticPolynomial a b c)}) ∧
    IsSemialgebraic (coordinateProjection {v : (Fin n ⊕ Unit) → ℝ |
      0≤MvPolynomial.eval v (quadraticPolynomial a b c)})

theorem quadraticPolynomialProjection : QuadraticPolynomialProjectionTarget :=
  quadratic_coordinate_projections_semialgebraic

def QuadraticUniversalConditionsTarget : Prop := ∀ {n : ℕ}
    (a b c : MvPolynomial (Fin n) ℝ),
    IsSemialgebraic {x : Vec n | ∀ t : ℝ,
      quadraticValue (MvPolynomial.eval x a) (MvPolynomial.eval x b) (MvPolynomial.eval x c) t≤0} ∧
    IsSemialgebraic {x : Vec n | ∀ t : ℝ,
      quadraticValue (MvPolynomial.eval x a) (MvPolynomial.eval x b) (MvPolynomial.eval x c) t<0} ∧
    IsSemialgebraic {x : Vec n | ∀ t : ℝ,
      quadraticValue (MvPolynomial.eval x a) (MvPolynomial.eval x b) (MvPolynomial.eval x c) t≠0}

theorem quadraticUniversalConditions : QuadraticUniversalConditionsTarget := fun a b c =>
  ⟨quadratic_forall_nonpositive_semialgebraic a b c,quadratic_forall_negative_semialgebraic a b c,
    quadratic_forall_nonzero_semialgebraic a b c⟩

def ActualDegreeTwoProjectionTarget : Prop := ∀ {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℝ), p.degreeOf none ≤ 2 →
    IsSemialgebraic {x : Vec n | ∃ t : ℝ, parameterEval p (x,t)=0} ∧
    IsSemialgebraic {x : Vec n | ∃ t : ℝ, 0<parameterEval p (x,t)} ∧
    IsSemialgebraic {x : Vec n | ∃ t : ℝ, 0≤parameterEval p (x,t)}

theorem actualDegreeTwoProjection : ActualDegreeTwoProjectionTarget :=
  degree_two_projections_semialgebraic

end BfgsVerification
