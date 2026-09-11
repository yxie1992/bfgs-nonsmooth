import BfgsVerification.GeneralCoordinateProjection

noncomputable section
open Set Polynomial
namespace BfgsVerification
open RealAlgebraicGeometry

def RationalIndexParameterTarget : Prop := ∀ {σ : Type} [Finite σ]
    (p q : Polynomial (MvPolynomial σ ℝ)),
    FiniteSemialgebraicFunction (fun x : σ → ℝ =>
      rationalCauchyIndex (p.map (MvPolynomial.eval x)) (q.map (MvPolynomial.eval x)))

theorem rationalIndexParameter : RationalIndexParameterTarget :=
  finiteSemialgebraic_rationalCauchyIndex

def TarskiQueryParameterTarget : Prop := ∀ {σ : Type} [Finite σ]
    (p q : Polynomial (MvPolynomial σ ℝ)),
    FiniteSemialgebraicFunction (fun x : σ → ℝ =>
      tarskiQuery (p.map (MvPolynomial.eval x)) (q.map (MvPolynomial.eval x)))

theorem tarskiQueryParameter : TarskiQueryParameterTarget := finiteSemialgebraic_tarskiQuery

def SimultaneousPolynomialProjectionTarget : Prop := ∀ {σ : Type} [Finite σ] {m : ℕ}
    (q : Fin m → MvPolynomial (Option σ) ℝ) (ω : Fin m → SignType),
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ,
      ∀ i, SignType.sign (MvPolynomial.eval (fun j => Option.elim j t x) (q i)) = ω i}

theorem simultaneousPolynomialProjection : SimultaneousPolynomialProjectionTarget :=
  polynomial_simultaneous_sign_projection

def BooleanScalarProjectionTarget : Prop := ∀ {σ : Type} [Finite σ]
    (f : PolynomialFormula (Option σ)),
    IsSemialgebraic {x : σ → ℝ | ∃ t : ℝ, f.Holds (fun j => Option.elim j t x)}

theorem booleanScalarProjection : BooleanScalarProjectionTarget := polynomial_boolean_scalar_projection

def GeneralCoordinateProjectionTarget : Prop := ∀ {σ τ : Type} [Finite σ] [Finite τ]
    {S : Set ((σ ⊕ τ) → ℝ)}, IsSemialgebraic S → IsSemialgebraic (coordinateProjection S)

theorem generalCoordinateProjection : GeneralCoordinateProjectionTarget :=
  coordinate_projection_semialgebraic

end BfgsVerification
