import BfgsVerification.RealSignQuerySampling

noncomputable section
open Polynomial
namespace BfgsVerification
open RealAlgebraicGeometry

def FinitePolynomialSignSamplingTarget : Prop := ∀ {m : ℕ}
    (q : Fin m → Polynomial ℝ) (x : ℝ),
    ∃y∈polynomialSignSamples (nonzeroFamilyProduct q),
      ∀i,SignType.sign ((q i).eval y)=SignType.sign ((q i).eval x)

theorem finitePolynomialSignSampling : FinitePolynomialSignSamplingTarget := exists_sample_with_same_family_signs

def PolynomialTailSamplesTarget : Prop := ∀ {m : ℕ}
    (q : Fin m → Polynomial ℝ) (i : Fin m),
    SignType.sign ((q i).eval (signSampleRadius (nonzeroFamilyProduct q).roots.toFinset))=
      SignType.sign (q i).leadingCoeff ∧
    SignType.sign ((q i).eval (-signSampleRadius (nonzeroFamilyProduct q).roots.toFinset))=
      (-1 : SignType)^(q i).natDegree*SignType.sign (q i).leadingCoeff

theorem polynomialTailSamples : PolynomialTailSamplesTarget := fun q i =>
  ⟨right_tail_sample_sign q i,left_tail_sample_sign q i⟩

/-- The actual all-real simultaneous sign question reduces to two finite
query expressions and literal coefficient/parity tail tests. This is a
fixed-fiber identity, not an assumed parameter projection theorem. -/
def RealPolynomialSignReductionTarget : Prop := ∀ {m : ℕ}
    (q : Fin m → Polynomial ℝ) (σ : Fin m → SignType),
    (∃x : ℝ,∀i,SignType.sign ((q i).eval x)=σ i) ↔
      0<signQueryExpression (nonzeroFamilyProduct q) q σ ∨
      0<signQueryExpression (nonzeroFamilyProduct q).derivative q σ ∨
      (∀i,(-1 : SignType)^(q i).natDegree*SignType.sign (q i).leadingCoeff=σ i) ∨
      (∀i,SignType.sign (q i).leadingCoeff=σ i)

theorem realPolynomialSignReduction : RealPolynomialSignReductionTarget :=
  exists_real_sign_pattern_iff_queries_and_tails

end BfgsVerification
