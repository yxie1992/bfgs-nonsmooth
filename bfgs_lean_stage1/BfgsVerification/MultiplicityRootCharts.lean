import BfgsVerification.PolynomialRootMultiplicity
import BfgsVerification.PolynomialSimpleRoot

/-! At every nonzero fiber root, its actual multiplicity selects a derivative
polynomial with a simple root. The resulting smooth graph contains nearby
points of that same multiplicity stratum; it need not contain other strata. -/
noncomputable section
open scoped Topology ContDiff
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

theorem verticalDerivative_succ (p : MvPolynomial (Option (Fin n)) ℝ) (k : ℕ) :
    MvPolynomial.pderiv none (verticalDerivative p k) = verticalDerivative p (k + 1) := by
  simp only [verticalDerivative,Function.iterate_succ_apply']

theorem multiplicityStratum_derivative_simple (p : MvPolynomial (Option (Fin n)) ℝ)
    {a : Vec n} {b : ℝ} {m : ℕ} (hv : parameterPoint a b ∈ multiplicityStratum p m)
    (hm : 0 < m) :
    (fiberPolynomial (verticalDerivative p (m - 1)) a).eval b = 0 ∧
      (fiberPolynomial (verticalDerivative p (m - 1)) a).derivative.eval b ≠ 0 := by
  obtain ⟨hz,hn⟩ := (multiplicityStratum_iff p m (parameterPoint a b)).mp hv
  constructor
  · rw [fiberPolynomial_eval]
    exact hz (m-1) (Finset.mem_range.mpr (by omega))
  · rw [← fiberPolynomial_pderiv,verticalDerivative_succ,Nat.sub_add_cancel hm,
      fiberPolynomial_eval]
    exact hn

theorem multiplicity_stratum_local_chart (p : MvPolynomial (Option (Fin n)) ℝ)
    {a : Vec n} {b : ℝ} {m : ℕ} (hv : parameterPoint a b ∈ multiplicityStratum p m)
    (hm : 0 < m) :
    ∃ (g : Vec n → ℝ) (r δ : ℝ), 0 < r ∧ 0 < δ ∧ g a = b ∧
      ContDiffOn ℝ ∞ g (Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, dist (g x) b < δ ∧
        ∀ t, dist t b < δ →
          (parameterEval (verticalDerivative p (m-1)) (x,t) = 0 ↔ t = g x)) ∧
      (∀ x ∈ Metric.ball a r, ∀ t, dist t b < δ →
        parameterPoint x t ∈ multiplicityStratum p m → t = g x) ∧
      IsSemialgebraic {v : Option (Fin n) → ℝ |
        (fun i => v (some i)) ∈ Metric.ball a r ∧ v none = g (fun i => v (some i))} := by
  obtain ⟨hz,hn⟩ := multiplicityStratum_derivative_simple p hv hm
  obtain ⟨g,r,δ,hr,hδ,hga,hg,hroot,hgraph⟩ :=
    polynomial_simple_root_chart (verticalDerivative p (m-1)) a b hz hn
  refine ⟨g,r,δ,hr,hδ,hga,hg,hroot,?_,hgraph⟩
  intro x hx t ht hmem
  apply ((hroot x hx).2 t ht).mp
  exact ((multiplicityStratum_iff p m (parameterPoint x t)).mp hmem).1
    (m-1) (Finset.mem_range.mpr (by omega))

/-- Every root of a nonzero fiber, including a multiple root, belongs to a
bounded positive multiplicity stratum with a derived smooth local graph. -/
theorem nonzero_fiber_root_stratum_chart (p : MvPolynomial (Option (Fin n)) ℝ)
    (a : Vec n) (b : ℝ) (hp : fiberPolynomial p a ≠ 0)
    (hz : (fiberPolynomial p a).eval b = 0) :
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
          (fun i => v (some i)) ∈ Metric.ball a r ∧ v none = g (fun i => v (some i))} := by
  let m := (fiberPolynomial p a).rootMultiplicity b
  have hm : 0 < m := (Polynomial.rootMultiplicity_pos hp).mpr hz
  have hmem : parameterPoint a b ∈ multiplicityStratum p m := by
    change fiberPolynomial p a ≠ 0 ∧ (fiberPolynomial p a).rootMultiplicity b = m
    exact ⟨hp,rfl⟩
  exact ⟨m,rfl,hm,multiplicityStratum_degree_bound p hmem,
    multiplicity_stratum_local_chart p hmem hm⟩

end RealAlgebraicGeometry
end BfgsVerification
