import BfgsVerification.MultiplicityRootCharts

/-! Exact contracts for coefficient specialization, degree/multiplicity strata,
and the derived local derivative graph at every nonzero fiber root. -/
noncomputable section
open scoped Topology ContDiff
open Set MvPolynomial
namespace BfgsVerification
open RealAlgebraicGeometry

def PolynomialDegreeStrataTarget : Prop := ∀ {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℝ),
    (∀ x : Vec n, (fiberPolynomial p x).natDegree ≤ p.degreeOf none) ∧
    IsSemialgebraic {x : Vec n | fiberPolynomial p x = 0} ∧
    (∀ k : ℕ, IsSemialgebraic {x : Vec n |
      fiberPolynomial p x ≠ 0 ∧ (fiberPolynomial p x).natDegree = k}) ∧
    ({x : Vec n | fiberPolynomial p x = 0} ∪
      (⋃ k ∈ Finset.range (p.degreeOf none + 1),
        {x : Vec n | fiberPolynomial p x ≠ 0 ∧ (fiberPolynomial p x).natDegree = k}) = univ)

theorem polynomialDegreeStrata : PolynomialDegreeStrataTarget := fun p =>
  ⟨fiberPolynomial_natDegree_le p,fiberPolynomial_zero_semialgebraic p,
    fiberPolynomial_degree_semialgebraic p,fiberPolynomial_degree_partition p⟩

def PolynomialDerivativeSpecializationTarget : Prop := ∀ {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℝ) (v : Option (Fin n) → ℝ) (k : ℕ),
    MvPolynomial.eval v (verticalDerivative p k) =
      (Polynomial.derivative^[k] (fiberPolynomial p (fun i => v (some i)))).eval (v none)

theorem polynomialDerivativeSpecialization : PolynomialDerivativeSpecializationTarget :=
  verticalDerivative_eval

def PolynomialMultiplicityStrataTarget : Prop := ∀ {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℝ),
    IsSemialgebraic (zeroFiberCylinder p) ∧
    (∀ m, IsSemialgebraic (multiplicityStratum p m)) ∧
    (∀ m, Disjoint (zeroFiberCylinder p) (multiplicityStratum p m)) ∧
    (∀ j k, j ≠ k → Disjoint (multiplicityStratum p j) (multiplicityStratum p k)) ∧
    (zeroFiberCylinder p ∪
      (⋃ m ∈ Finset.range (p.degreeOf none + 1), multiplicityStratum p m) = univ) ∧
    ({v | MvPolynomial.eval v p = 0} = zeroFiberCylinder p ∪
      (⋃ m ∈ Finset.Icc 1 (p.degreeOf none), multiplicityStratum p m))

theorem polynomialMultiplicityStrata : PolynomialMultiplicityStrataTarget := fun p =>
  ⟨zeroFiberCylinder_semialgebraic p,multiplicityStratum_semialgebraic p,
    zeroFiber_disjoint_multiplicityStratum p,fun _ _ h => multiplicityStrata_disjoint p h,
    multiplicityStrata_partition p,root_multiplicity_partition p⟩

def PolynomialMultipleRootChartTarget : Prop := ∀ {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℝ) (a : Vec n) (b : ℝ),
    fiberPolynomial p a ≠ 0 → (fiberPolynomial p a).eval b = 0 →
    ∃ m : ℕ, m = (fiberPolynomial p a).rootMultiplicity b ∧
      0 < m ∧ m ≤ p.degreeOf none ∧
      ∃ (g : Vec n → ℝ) (r δ : ℝ), 0 < r ∧ 0 < δ ∧ g a = b ∧
        ContDiffOn ℝ ∞ g (Metric.ball a r) ∧
        (∀ x ∈ Metric.ball a r, dist (g x) b < δ ∧
          ∀ t, dist t b < δ →
            (parameterEval (verticalDerivative p (m-1)) (x,t) = 0 ↔ t = g x)) ∧
        (∀ x ∈ Metric.ball a r, ∀ t, dist t b < δ →
          parameterPoint x t ∈ multiplicityStratum p m → t = g x) ∧
        IsSemialgebraic {v : Option (Fin n) → ℝ |
          (fun i => v (some i)) ∈ Metric.ball a r ∧ v none = g (fun i => v (some i))}

theorem polynomialMultipleRootChart : PolynomialMultipleRootChartTarget :=
  nonzero_fiber_root_stratum_chart

end BfgsVerification
