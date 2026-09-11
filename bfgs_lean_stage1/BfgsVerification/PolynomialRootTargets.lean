import BfgsVerification.PolynomialSimpleRoot

/-! Exact contracts for proved polynomial simple-root charts and local
existential projection. The global nonlinear projection theorem is not assumed
and is not asserted by these local infrastructure statements. -/
noncomputable section
open scoped Topology ContDiff
open Set
namespace BfgsVerification
open RealAlgebraicGeometry

def PolynomialFiberDerivativeTarget : Prop := ∀ {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℝ) (x : Vec n) (t : ℝ),
    fderiv ℝ (parameterEval p) (x,t) (0,1) = (fiberPolynomial p x).derivative.eval t

theorem polynomialFiberDerivative : PolynomialFiberDerivativeTarget :=
  parameterEval_vertical_derivative

def PolynomialSimpleRootChartTarget : Prop := ∀ {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℝ) (a : Vec n) (b : ℝ),
    (fiberPolynomial p a).eval b = 0 → (fiberPolynomial p a).derivative.eval b ≠ 0 →
    ∃ g : Vec n → ℝ, ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ g a = b ∧
      ContDiffOn ℝ ∞ g (Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, dist (g x) b < δ ∧
        ∀ t : ℝ, dist t b < δ → (parameterEval p (x,t) = 0 ↔ t = g x)) ∧
      IsSemialgebraic {v : Option (Fin n) → ℝ |
        (fun i => v (some i)) ∈ Metric.ball a r ∧ v none = g (fun i => v (some i))}

theorem polynomialSimpleRootChart : PolynomialSimpleRootChartTarget :=
  polynomial_simple_root_chart

def PolynomialSimpleRootProjectionTarget : Prop := ∀ {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℝ) (a : Vec n) (b : ℝ),
    (fiberPolynomial p a).eval b = 0 → (fiberPolynomial p a).derivative.eval b ≠ 0 →
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      {x : Vec n | x ∈ Metric.ball a r ∧ ∃ t : ℝ, dist t b < δ ∧ parameterEval p (x,t) = 0} =
        Metric.ball a r ∧
      IsSemialgebraic {x : Vec n | x ∈ Metric.ball a r ∧
        ∃ t : ℝ, dist t b < δ ∧ parameterEval p (x,t) = 0}

theorem polynomialSimpleRootProjection : PolynomialSimpleRootProjectionTarget :=
  polynomial_simple_root_local_projection

end BfgsVerification
