import BfgsVerification.EuclideanIndexComputation

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
open RealAlgebraicGeometry

def FiniteJumpTelescopingTarget : Prop := ∀ (B : Finset ℝ) (f L : ℝ → ℤ),
  (∀ a, ∀ᶠ x in 𝓝[<] a, f x=L a) →
  (∀ a, ∀ᶠ x in 𝓝[≥] a, f x=f a) →
  (∀ a, a ∉ B → L a=f a) → ∀ l r : ℤ,
  (∀ᶠ x in atBot, f x=l) → (∀ᶠ x in atTop, f x=r) →
  ∑ a ∈ B, (f a-L a)=r-l

theorem finiteJumpTelescoping : FiniteJumpTelescopingTarget := finite_jump_telescope

def PolynomialSignJumpTarget : Prop := ∀ (p : Polynomial ℝ), p ≠ 0 →
  (∀ᶠ x in atTop, SignType.sign (p.eval x)=SignType.sign p.leadingCoeff) ∧
  (∀ᶠ x in atBot, SignType.sign (p.eval x)=
    (-1 : SignType)^p.natDegree*SignType.sign p.leadingCoeff) ∧
  ∑ a ∈ p.roots.toFinset, (polynomialRightSign p a-polynomialLeftSign p a) =
    (SignType.sign p.leadingCoeff : ℤ) -
      (-1 : ℤ)^p.natDegree*(SignType.sign p.leadingCoeff : ℤ)

theorem polynomialSignJump : PolynomialSignJumpTarget := fun p hp =>
  ⟨polynomial_sign_atTop p, polynomial_sign_atBot p, polynomial_sign_jump_sum hp⟩

def RationalIndexReciprocityTarget : Prop := ∀ (p q : Polynomial ℝ), p ≠ 0 → q ≠ 0 →
  rationalCauchyIndex p q+rationalCauchyIndex q p =
    ((SignType.sign (p*q).leadingCoeff : ℤ) -
      (-1 : ℤ)^(p*q).natDegree*(SignType.sign (p*q).leadingCoeff : ℤ))/2

theorem rationalIndexReciprocity : RationalIndexReciprocityTarget :=
  fun _ _ hp hq => rationalCauchyIndex_reciprocity hp hq

def RationalIndexRemainderTarget : Prop := ∀ (p q : Polynomial ℝ), q ≠ 0 →
  rationalCauchyIndex p q = rationalCauchyIndex (p%q) q

theorem rationalIndexRemainder : RationalIndexRemainderTarget := fun p _ hq =>
  rationalCauchyIndex_mod p hq

def EuclideanIndexComputationTarget : Prop :=
  (∀ p q : Polynomial ℝ, euclideanIndex p q=rationalCauchyIndex p q) ∧
  (∀ p q : Polynomial ℝ, p ≠ 0 → tarskiQuery p q=euclideanIndex (q*p.derivative) p)

theorem euclideanIndexComputation : EuclideanIndexComputationTarget :=
  ⟨euclideanIndex_correct, fun _ q hp => tarskiQuery_eq_euclideanIndex hp q⟩

end BfgsVerification
