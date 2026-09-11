import BfgsVerification.TarskiLocalIndex

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
open RealAlgebraicGeometry

def PolynomialOneSidedSignsTarget : Prop := ∀ (p : Polynomial ℝ), p ≠ 0 → ∀ a : ℝ,
  (∀ᶠ x in 𝓝[>] a,
    SignType.sign (p.eval x) = SignType.sign ((rootFactor p a).eval a)) ∧
  (∀ᶠ x in 𝓝[<] a,
    SignType.sign (p.eval x) = (-1 : SignType)^p.rootMultiplicity a *
      SignType.sign ((rootFactor p a).eval a))

theorem polynomialOneSidedSigns : PolynomialOneSidedSignsTarget := fun p hp a =>
  ⟨polynomial_sign_right_of_rootMultiplicity hp a,
    polynomial_sign_left_of_rootMultiplicity hp a⟩

def PolynomialLogarithmicResidueTarget : Prop := ∀ (p q : Polynomial ℝ), p ≠ 0 → ∀ a : ℝ,
  Tendsto (fun x => (x-a) * (q.eval x * p.derivative.eval x / p.eval x))
    (𝓝[≠] a) (𝓝 ((p.rootMultiplicity a : ℝ) * q.eval a))

theorem polynomialLogarithmicResidue : PolynomialLogarithmicResidueTarget :=
  fun _ q hp a => weighted_normalized_logDerivative_tendsto hp q a

def WeightedLogarithmicPoleTarget : Prop := ∀ (p q : Polynomial ℝ), p ≠ 0 →
  ∀ a : ℝ, p.IsRoot a →
    (0 < q.eval a →
      Tendsto (fun x => q.eval x * p.derivative.eval x / p.eval x) (𝓝[>] a) atTop ∧
      Tendsto (fun x => q.eval x * p.derivative.eval x / p.eval x) (𝓝[<] a) atBot) ∧
    (q.eval a < 0 →
      Tendsto (fun x => q.eval x * p.derivative.eval x / p.eval x) (𝓝[>] a) atBot ∧
      Tendsto (fun x => q.eval x * p.derivative.eval x / p.eval x) (𝓝[<] a) atTop) ∧
    (q.eval a = 0 →
      Tendsto (fun x => q.eval x * p.derivative.eval x / p.eval x) (𝓝[≠] a)
        (𝓝 ((p.rootMultiplicity a : ℝ) * (q /ₘ (X-C a)).eval a)))

theorem weightedLogarithmicPole : WeightedLogarithmicPoleTarget := fun _ _ hp _ ha =>
  ⟨weighted_logDerivative_positive_pole hp ha,
    weighted_logDerivative_negative_pole hp ha,
    weighted_logDerivative_finite_of_weight_root hp⟩

def TarskiCauchyLocalIdentityTarget : Prop := ∀ (p q : Polynomial ℝ), p ≠ 0 →
  tarskiQuery p q = rationalCauchyIndex (q * p.derivative) p ∧
  tarskiQuery p q =
    ((p.roots.toFinset.filter (fun a => 0 < q.eval a)).card : ℤ) -
    ((p.roots.toFinset.filter (fun a => q.eval a < 0)).card : ℤ)

theorem tarskiCauchyLocalIdentity : TarskiCauchyLocalIdentityTarget := fun p q hp =>
  ⟨tarskiQuery_eq_rationalCauchyIndex hp q, tarskiQuery_eq_positive_card_sub_negative_card p q⟩

end BfgsVerification
